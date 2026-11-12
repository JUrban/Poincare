(* ========================================================================= *)
(* pc_moi_s35_approx: Moise GTM 47, Sec 35, Theorem 35.1, the approximation *)
(* stage of pp.249-250 (conditions (2)-(8)) in the tube form of             *)
(* pc_moi_s35_stmt.ml: main theorem APPROX, the statement MOI_S35_APPROX.   *)
(* Errors are chosen per vertex of the graph (locally finite by the vertex  *)
(* charts of the open stars and invariance of domain), the maps f_v come    *)
(* from the 34.1 theorem CELL_341 on the enlarged cells C''_v, the levels of *)
(* the A-side cuts are chosen generic for the B-annuli.                     *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt.ml";;
needs "src/pc_moi_fnd_tubea.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 0. Generic topology: approximations of an injective map keep disjoint   *)
(* compact sets apart, margins around compact sets for open maps, interiors *)
(* of images of compact sets in real^3, finite minima of positive numbers.  *)
(* ------------------------------------------------------------------------- *)

let MOI_S5A_APPROX_DISJOINT = prove
 (`!(f1:real^N->real^3) f2 (h:real^N->real^3) s t r1 r2.
     (!x. x IN s ==> dist(f1 x,h x) < r1) /\
     (!y. y IN t ==> dist(f2 y,h y) < r2) /\
     (~(s = {}) /\ ~(t = {}) ==> r1 + r2 <= setdist(IMAGE h s,IMAGE h t))
     ==> DISJOINT (IMAGE f1 s) (IMAGE f2 t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(s:real^N->bool = {}) /\ ~(t:real^N->bool = {})` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MP th)) THEN
  SUBGOAL_THEN `dist((f1:real^N->real^3) x,h x) < r1 /\
                dist((f2:real^N->real^3) y,h y) < r2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) s`; `IMAGE (h:real^N->real^3) t`;
                 `(h:real^N->real^3) x`; `(h:real^N->real^3) y`]
    SETDIST_LE_DIST) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f1:real^N->real^3) x = (f2:real^N->real^3) y` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `dist((f1:real^N->real^3) x,h x) < r1` THEN
  UNDISCH_TAC `dist((f2:real^N->real^3) y,h y) < r2` THEN
  CONV_TAC NORM_ARITH);;

let MOI_S5A_SETDIST_POS = prove
 (`!(h:real^N->real^3) u s t.
     h continuous_on u /\ (!x y. x IN u /\ y IN u /\ h x = h y ==> x = y) /\
     compact s /\ compact t /\ s SUBSET u /\ t SUBSET u /\ DISJOINT s t /\
     ~(s = {}) /\ ~(t = {})
     ==> &0 < setdist(IMAGE h s,IMAGE h t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(IMAGE (h:real^N->real^3) s) /\
                compact(IMAGE (h:real^N->real^3) t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_LE; SETDIST_POS_LE] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; COMPACT_IMP_CLOSED] THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `x:real^N = y` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ASM SET_TAC[]]);;

let MOI_S5A_MARGIN = prove
 (`!(g:real^3->real^3) u k.
     g continuous_on u /\ (!x y. x IN u /\ y IN u /\ g x = g y ==> x = y) /\
     open u /\ compact k /\ k SUBSET u
     ==> ?r. &0 < r /\ !y z. z IN k /\ dist(y,g z) < r ==> y IN IMAGE g u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open(IMAGE (g:real^3->real^3) u)` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) k`;
                 `(:real^3) DIFF IMAGE (g:real^3->real^3) u`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(g:real^3->real^3) z`; `y:real^3`]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_MESON_TAC[REAL_NOT_LT]);;

let MOI_S5A_INTERIOR_IMAGE_SUBSET = prove
 (`!(g:real^3->real^3) s.
     compact s /\ g continuous_on s /\
     (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y)
     ==> interior(IMAGE g s) SUBSET IMAGE g (interior s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `g:real^3->real^3`;
                 `IMAGE (g:real^3->real^3) s`] HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^3->real^3` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g':real^3->real^3`; `IMAGE (g:real^3->real^3) s`]
    CONTINUOUS_IMAGE_SUBSET_INTERIOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  EXISTS_TAC `(g':real^3->real^3) y` THEN
  MP_TAC(ISPEC `IMAGE (g:real^3->real^3) s` INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;

let MOI_S5A_FINITE_POS_MIN = prove
 (`!(P:A->real->bool) s.
     FINITE s /\ (!x. x IN s ==> ?e. &0 < e /\ P x e) /\
     (!x e e'. P x e /\ &0 < e' /\ e' <= e ==> P x e')
     ==> ?e. &0 < e /\ !x. x IN s ==> P x e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mono"))) THEN
  UNDISCH_TAC `!x:A. x IN s ==> ?e. &0 < e /\ (P:A->real->bool) x e` THEN
  UNDISCH_TAC `FINITE (s:A->bool)` THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_INSERT] THEN DISCH_THEN(LABEL_TAC "cov") THEN
  REMOVE_THEN "ih" MP_TAC THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "cov" (MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min e1 e2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THENL
   [USE_THEN "mono" MATCH_MP_TAC THEN EXISTS_TAC `e2:real` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    USE_THEN "mono" MATCH_MP_TAC THEN EXISTS_TAC `e1:real` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]);;
let MOI_S5A_INTERIOR_UNIONS_CLOSED = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ (!k. k IN c ==> closed k) /\ ~(interior(UNIONS c) = {})
     ==> ?k. k IN c /\ ~(interior k = {})`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; INTERIOR_EMPTY; NOT_IN_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `s:(real^N->bool)->bool`] THEN
  REWRITE_TAC[UNIONS_INSERT; IN_INSERT] THEN STRIP_TAC THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `closed(a:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTERIOR_UNION_EQ_EMPTY; DE_MORGAN_THM] THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[] THEN MESON_TAC[]);;

let MOI_S5A_PL_LIN_AT_EXISTS = prove
 (`!(f:real^3->real^3) s u.
     pl_map_on s f /\ open u /\ u SUBSET s /\ ~(u = {})
     ==> ?x m. x IN u /\ moi_s35_lin_at f x m`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:real^3` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x0:real^3` o GEN_REWRITE_RULE I [pl_map_on]) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^3->bool)->bool`
    (X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?r. &0 < r /\ cball(x0:real^3,r) SUBSET u INTER v`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `u INTER v:real^3->bool` OPEN_CONTAINS_CBALL) THEN
    ASM_SIMP_TAC[OPEN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `x0:real^3`) THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{k INTER cball(x0:real^3,r) | k IN c}`
    MOI_S5A_INTERIOR_UNIONS_CLOSED) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_CBALL] THEN
      ASM_MESON_TAC[POLYTOPE_IMP_CLOSED];
      SUBGOAL_THEN `UNIONS {k INTER cball(x0:real^3,r) | k IN c} =
                    cball(x0,r)` SUBST1_TAC THENL
       [REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[INTERIOR_CBALL; BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_GSPEC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN `y:real^3`
     STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^3` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `k INTER cball(x0:real^3,r)` INTERIOR_SUBSET) THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:real^3`; `l:real^3->real^3`] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s35_lin_at] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN k /\ (x:real^3) IN k` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_SUB] THEN VECTOR_ARITH_TAC);;

let MOI_S5A_AVOID_FINITE = prove
 (`!s:real->bool. FINITE s ==> ?c. abs c <= &1 / &512 /\ ~(c IN s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?c. abs c <= &1 / &512 /\ ~(c IN (s:real->bool))` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM;
    TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!n. &0 < &512 * (&n + &1) /\ &512 <= &512 * (&n + &1)`
  (LABEL_TAC "pos") THENL
   [GEN_TAC THEN MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (IMAGE (\n. &1 / (&512 * (&n + &1))) (:num))` MP_TAC
  THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:real->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `n:num` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "pos" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. &1 / (&512 * (&n + &1))`; `(:num)`]
    FINITE_IMAGE_INJ_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIV] THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    USE_THEN "pos" (STRIP_ASSUME_TAC o SPEC `m:num`) THEN
    USE_THEN "pos" (STRIP_ASSUME_TAC o SPEC `n:num`) THEN
    ASM_SIMP_TAC[REAL_FIELD
     `&0 < a /\ &0 < b ==> (&1 / a = &1 / b <=> a = b)`] THEN
    REWRITE_TAC[REAL_EQ_MUL_LCANCEL; REAL_EQ_ADD_RCANCEL; REAL_OF_NUM_EQ] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM INFINITE; num_INFINITE]);;

let MOI_S5A_INVERSE_UCONT = prove
 (`!(g:real^M->real^N) s e.
     compact s /\ g continuous_on s /\
     (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\ &0 < e
     ==> ?d. &0 < d /\
             !x y. x IN s /\ y IN s /\ dist(g x,g y) < d ==> dist(x,y) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `g:real^M->real^N`;
                 `IMAGE (g:real^M->real^N) s`] HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':real^N->real^M` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g':real^N->real^M`; `IMAGE (g:real^M->real^N) s`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(g:real^M->real^N) y`; `(g:real^M->real^N) x`])
  THEN ASM_SIMP_TAC[FUN_IN_IMAGE]);;
(* A polytope of real^3 with nonempty interior is a PL 3-cell bounded by    *)
(* its frontier (cone from an interior point over the frontier sphere).     *)

let MOI_S5A_POLYTOPE_CELL = prove
 (`!k:real^3->bool.
     polytope k /\ ~(interior k = {})
     ==> pl_cell_with_boundary 3 k (frontier k)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `p:real^3` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `bounded (k:real^3->bool) /\ convex k /\ closed k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[POLYTOPE_IMP_BOUNDED; POLYTOPE_IMP_CONVEX;
                  POLYTOPE_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN k ==> segment(p,y) SUBSET interior k`
  (LABEL_TAC "seg") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y:real^3. y IN frontier k ==> y IN k) /\
    (!y:real^3. y IN frontier k ==> ~(y IN interior k)) /\
    (!y:real^3. y IN k /\ ~(y IN interior k) ==> y IN frontier k)`
  (CONJUNCTS_THEN2 (LABEL_TAC "fr1") (CONJUNCTS_THEN2 (LABEL_TAC "fr2")
    (LABEL_TAC "fr3"))) THENL
   [UNDISCH_TAC `closed (k:real^3->bool)` THEN
    SIMP_TAC[frontier; CLOSURE_CLOSED; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~((p:real^3) IN frontier k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u r. ~(u = vec 0) /\ &0 < r /\ r < &1 /\ (p + u:real^3) IN k
          ==> p + r % u IN interior k`
  (LABEL_TAC "ray") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "seg" (MP_TAC o SPEC `p + u:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_ARITH `p:real^3 = p + u <=> u = vec 0`];
      EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (frontier k:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC STAR_SHAPED_PL_SPHERE THEN EXISTS_TAC `p:real^3` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `frontier k = relative_frontier (k:real^3->bool)`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_FRONTIER_FRONTIER THEN
        MATCH_MP_TAC AFFINE_HULL_NONEMPTY_INTERIOR THEN ASM SET_TAC[];
        MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:real^3->bool`; `p:real^3`; `u:real^3`]
        RAY_TO_FRONTIER) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!r1 r2. &0 < r1 /\ r1 < r2 /\
              (p:real^3) + r1 % (u:real^3) IN frontier (k:real^3->bool) /\
              p + r2 % u IN frontier k ==> F`
    (LABEL_TAC "un") THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `&0 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "ray" (MP_TAC o SPECL [`r2 % u:real^3`; `r1 / r2`]) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; REAL_LT_DIV;
                     REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`r1:real`; `r2:real`] THEN STRIP_TAC THEN
    DISJ_CASES_TAC(SPECL [`r1:real`; `r2:real`] REAL_LT_TOTAL) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [REMOVE_THEN "un" (MP_TAC o SPECL [`r1:real`; `r2:real`]);
      REMOVE_THEN "un" (MP_TAC o SPECL [`r2:real`; `r1:real`])] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `frontier k:real^3->bool`; `p:real^3`]
    MOI_FTA_CONE_CELL) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~((y:real^3) IN segment(p,x))` ASSUME_TAC THENL
     [DISCH_TAC THEN USE_THEN "seg" (MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(y:real^3 = p)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN segment[p,x]` THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    UNDISCH_TAC `convex(k:real^3->bool)` THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`p:real^3`; `x:real^3`]) THEN
    ASM_MESON_TAC[SUBSET];
    DISCH_TAC] THEN
  ASM_CASES_TAC `z:real^3 = p` THENL
   [MP_TAC(ISPECL [`k:real^3->bool`; `p:real^3`; `basis 1:real^3`]
      RAY_TO_FRONTIER) THEN
    ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `segment[p:real^3,p + d % basis 1]` THEN
    REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `p:real^3`; `z - p:real^3`]
    RAY_TO_FRONTIER) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "ray" (MP_TAC o SPECL [`z - p:real^3`; `d:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_SUB_EQ; VECTOR_ARITH `p + z - p:real^3 = z`];
      ALL_TAC] THEN
    REMOVE_THEN "fr2" (MP_TAC o SPEC `p + d % (z - p):real^3`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `segment[p:real^3,p + d % (z - p)]` THEN
  CONJ_TAC THENL
   [EXISTS_TAC `p + d % (z - p):real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `inv d:real` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_INV_LE_1] THEN
  REWRITE_TAC[VECTOR_ARITH
   `(&1 - t) % p + t % (p + d % (z - p)):real^3 = p + (t * d) % (z - p)`] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC);;
(* Moving PL 3-cells between real^3 and real^N (dimindex at least 3), and   *)
(* PL embeddings of cells into real^3 are PL 3-balls.                       *)

let MOI_S5A_PAD3 = prove
 (`3 <= dimindex(:N)
   ==> ?(A:real^3->real^N) (B:real^N->real^3).
         linear A /\ linear B /\ !x. B(A x) = x`,
  DISCH_TAC THEN
  EXISTS_TAC `(\x:real^3. (lambda i. if i <= 3 then x$i else &0):real^N)` THEN
  EXISTS_TAC `(\y:real^N. (lambda i. y$i):real^3)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[linear] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT];
    GEN_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA; DIMINDEX_3] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i <= dimindex(:N)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[LAMBDA_BETA]]]);;

let MOI_S5A_CELL_UP = prove
 (`!(s:real^3->bool) bs (p:real^3->real^N) q.
     3 <= dimindex(:N) /\ pl_cell_with_boundary 3 s bs /\
     pl_homeomorphism (s,IMAGE p s) (p,q)
     ==> pl_cell_with_boundary 3 (IMAGE p s) (IMAGE p bs)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S5A_PAD3) THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3->real^N` (X_CHOOSE_THEN `B:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x y. (A:real^3->real^N) x = A y ==> x = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!X. IMAGE (B:real^N->real^3) (IMAGE (A:real^3->real^N) X) = X`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope(k:real^3->bool) /\ polytope(IMAGE (A:real^3->real^N) k)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_LINEAR_IMAGE]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (A:real^3->real^N) k` THEN
  EXISTS_TAC `(p:real^3->real^N) o (f:real^3->real^3) o (B:real^N->real^3)` THEN
  EXISTS_TAC `((A:real^3->real^N) o (g:real^3->real^3)) o (q:real^N->real^3)`
  THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `&3 simplex (k:real^3->bool)` THEN REWRITE_TAC[simplex] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (A:real^3->real^N) c` THEN
    ASM_SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE] THEN
    MP_TAC(ISPECL [`A:real^3->real^N`; `c:real^3->bool`]
      AFFINE_DEPENDENT_LINEAR_IMAGE_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `FINITE (c:real^3->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real^3->real^N`; `c:real^3->bool`] CARD_IMAGE_INJ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
    CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`IMAGE (A:real^3->real^N) k`; `B:real^N->real^3`;
                     `vec 0:real^3`] PL_MAP_ON_AFFINE) THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; VECTOR_ADD_RID; ETA_AX]];
    MP_TAC(ISPECL [`A:real^3->real^N`; `k:real^3->bool`]
      RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[]]);;

let MOI_S5A_CELL_DOWN = prove
 (`!(s:real^N->bool) bs.
     pl_cell_with_boundary 3 s bs
     ==> ?S:real^3->bool p q.
           &3 simplex S /\ pl_homeomorphism (S,s) (p,q) /\
           IMAGE p (relative_frontier S) = bs`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_STA_SIMPLEX_RF_R3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `f1:real^3->real^N`
    (X_CHOOSE_THEN `g1:real^N->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `k:real^N->bool`; `3`;
                 `f1:real^3->real^N`; `g1:real^N->real^3`]
    PL_HOMEOMORPHISM_CONE_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^3->real^N` (X_CHOOSE_THEN
    `g2:real^N->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`S:real^3->bool`; `(f:real^N->real^N) o (f2:real^3->real^N)`;
    `(g2:real^N->real^3) o (g:real^N->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `IMAGE (f1:real^3->real^N) (relative_frontier S)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN s ==> (f:real^3->real^N) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `pl_homeomorphism (relative_frontier S,relative_frontier k)
                  ((f1:real^3->real^N),(g1:real^N->real^3))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]]);;

let MOI_S5A_PL_BALL_IMAGE = prove
 (`!(s:real^N->bool) bs u (f:real^N->real^3).
     pl_cell_with_boundary 3 s bs /\ s SUBSET u /\ pl_map_on u f /\
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)
     ==> pl_ball 3 (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S5A_CELL_DOWN) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^N`
    (X_CHOOSE_THEN `q:real^N->real^3` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `pl_homeomorphism (S,s) ((p:real^3->real^N),(q:real^N->real^3))`
  THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_map_on S ((f:real^N->real^3) o (p:real^3->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `(f:real^N->real^3) o (p:real^3->real^N)`;
                 `IMAGE (f:real^N->real^3) s`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SIMPLEX_IMP_COMPACT; PL_MAP_ON_IMP_CONTINUOUS_ON; IMAGE_o] THEN
    REWRITE_TAC[o_THM] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]; ALL_TAC]) THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^3->real^N) x IN u /\ p y IN u` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `s SUBSET (u:real^N->bool)` THEN
      UNDISCH_TAC `IMAGE (p:real^3->real^N) S = s` THEN
      UNDISCH_TAC `(x:real^3) IN S` THEN UNDISCH_TAC `(y:real^3) IN S` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3->real^N) x = p y` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y. x IN u /\ y IN u /\ (f:real^N->real^3) x = f y
                                  ==> x = y`) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^3`) THEN
  REWRITE_TAC[pl_ball] THEN
  MAP_EVERY EXISTS_TAC [`S:real^3->bool`;
    `(f:real^N->real^3) o (p:real^3->real^N)`; `g:real^3->real^3`] THEN
  ASM_SIMP_TAC[HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM]);;
(* The boundary of a PL 3-cell of real^N goes to non-interior points under  *)
(* any continuous injective map into real^3 (invariance of domain).         *)

let MOI_S5A_CELL_BD_NOT_INTERIOR = prove
 (`!(s:real^N->bool) bs (h:real^N->real^3) x.
     pl_cell_with_boundary 3 s bs /\ h continuous_on s /\
     (!x y. x IN s /\ y IN s /\ h x = h y ==> x = y) /\ x IN bs
     ==> ~(h x IN interior(IMAGE h s))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S5A_CELL_DOWN o
    check (can (term_match [] `pl_cell_with_boundary 3 (s:real^N->bool) bs`) o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^N`
    (X_CHOOSE_THEN `q:real^N->real^3` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `pl_homeomorphism (S,s) ((p:real^3->real^N),(q:real^N->real^3))`
  THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (S:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier S SUBSET (S:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) o (p:real^3->real^N)`; `S:real^3->bool`]
    MOI_S5A_INTERIOR_IMAGE_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(p:real^3->real^N) y = p z` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!x y. x IN s /\ y IN s /\
                     (h:real^N->real^3) x = h y ==> x = y`) (concl th))) THEN
        ASM SET_TAC[];
        ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?z:real^3. z IN relative_frontier S /\ x = (p:real^3->real^N) z`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN bs` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
      `IMAGE (p:real^3->real^N) (relative_frontier S) = bs`) o concl)) THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z':real^3. z' IN interior S /\
                            (h:real^N->real^3) x = h((p:real^3->real^N) z')`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `interior (IMAGE (h:real^N->real^3) s) SUBSET
                 IMAGE h (IMAGE (p:real^3->real^N) (interior S))` THEN
    UNDISCH_TAC `(h:real^N->real^3) x IN interior (IMAGE h s)` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `S:real^3->bool` MOI_STA_SIMPLEX_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z':real^3) IN S /\ (z:real^3) IN S` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3->real^N) z' = p z` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x y. x IN s /\ y IN s /\
                 (h:real^N->real^3) x = h y ==> x = y`) (concl th))) THEN
    ASM SET_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `z':real^3 = z` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[]; ASM SET_TAC[]]);;
(* The marker lemma in a chart: a box of the model is a PL 3-cell, its image *)
(* under a PL chart p is one in real^N, and an approximation f of h on it   *)
(* covers every point within r of h o p of a compact t inside an open u in  *)
(* the inner box kb (MARKER plus a margin from invariance of domain).       *)

let MOI_S5A_CHART_MARKER = prove
 (mk_imp(MOI_S35_MARKER,
  `!(p:real^3->real^N) q (a:real^3) b (kb:real^3->bool) u t
    (h:real^N->real^3) w.
     3 <= dimindex(:N) /\ (!i. 1 <= i /\ i <= 3 ==> a$i < b$i) /\
     pl_homeomorphism (interval[a,b],IMAGE p (interval[a,b])) (p,q) /\
     compact kb /\ kb SUBSET interval(a,b) /\ open u /\ u SUBSET kb /\
     compact t /\ t SUBSET u /\
     IMAGE p (interval[a,b]) SUBSET w /\ h continuous_on w /\
     (!x y. x IN w /\ y IN w /\ h x = h y ==> x = y)
     ==> ?r. &0 < r /\
             !f y z. f continuous_on IMAGE p (interval[a,b]) /\
                     (!x y. x IN IMAGE p (interval[a,b]) /\
                            y IN IMAGE p (interval[a,b]) /\ f x = f y
                            ==> x = y) /\
                     (!x. x IN IMAGE p (interval[a,b]) ==> dist(f x,h x) < r) /\
                     z IN t /\ dist(y,h(p z)) < r
                     ==> y IN interior(IMAGE f (IMAGE p (interval[a,b])))`),
  DISCH_THEN(LABEL_TAC "mark") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hinj")))))))))))) THEN
  ASM_CASES_TAC `t:real^3->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 3 (interval[a:real^3,b]) (frontier(interval[a,b]))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5A_POLYTOPE_CELL THEN
    REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_CLOSED_INTERVAL;
                INTERVAL_NE_EMPTY; DIMINDEX_3] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval[a:real^3,b]`; `frontier(interval[a:real^3,b])`;
                 `p:real^3->real^N`; `q:real^N->real^3`] MOI_S5A_CELL_UP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(p:real^3->real^N) continuous_on interval[a,b] /\
    (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ p x = p y ==> x = y)`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pinj")) THENL
   [UNDISCH_TAC `pl_homeomorphism (interval[a,b],IMAGE p (interval[a,b]))
                  ((p:real^3->real^N),(q:real^N->real^3))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `kb SUBSET interval[a:real^3,b] /\ u SUBSET interval[a:real^3,b] /\
    t SUBSET u /\ ~(kb:real^3->bool = {}) /\
    frontier(interval[a:real^3,b]) SUBSET interval[a,b] /\
    DISJOINT kb (frontier(interval[a:real^3,b]))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[FRONTIER_CLOSED_INTERVAL] THEN
    MP_TAC(ISPECL [`a:real^3`; `b:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    UNDISCH_TAC `kb SUBSET interval(a:real^3,b)` THEN
    UNDISCH_TAC `u SUBSET (kb:real^3->bool)` THEN
    UNDISCH_TAC `t SUBSET (u:real^3->bool)` THEN
    UNDISCH_TAC `~(t:real^3->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (p:real^3->real^N) kb SUBSET w /\
    IMAGE (p:real^3->real^N) u SUBSET w /\
    IMAGE (p:real^3->real^N) (frontier(interval[a,b])) SUBSET w /\
    IMAGE (p:real^3->real^N) kb SUBSET IMAGE p (interval[a,b]) /\
    IMAGE (p:real^3->real^N) (frontier(interval[a,b])) SUBSET
    IMAGE p (interval[a,b])`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (p:real^3->real^N) (interval[a,b]) SUBSET w` THEN
    UNDISCH_TAC `kb SUBSET interval[a:real^3,b]` THEN
    UNDISCH_TAC `u SUBSET interval[a:real^3,b]` THEN
    UNDISCH_TAC `frontier(interval[a:real^3,b]) SUBSET interval[a,b]` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact (IMAGE (p:real^3->real^N) kb) /\
    compact (IMAGE (p:real^3->real^N) (frontier(interval[a,b])))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[COMPACT_FRONTIER_BOUNDED; BOUNDED_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[a:real^3,b]` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (p:real^3->real^N) kb)
             (IMAGE (p:real^3->real^N) (frontier(interval[a,b])))`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `x2:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `x1:real^3 = x2` SUBST_ALL_TAC THENL
     [USE_THEN "pinj" MATCH_MP_TAC THEN
      UNDISCH_TAC `kb SUBSET interval[a:real^3,b]` THEN
      UNDISCH_TAC `frontier(interval[a:real^3,b]) SUBSET interval[a,b]` THEN
      UNDISCH_TAC `(x1:real^3) IN kb` THEN
      UNDISCH_TAC `(x2:real^3) IN frontier(interval[a,b])` THEN
      UNDISCH_TAC `y = (p:real^3->real^N) x1` THEN
      UNDISCH_TAC `y = (p:real^3->real^N) x2` THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT kb (frontier(interval[a:real^3,b]))` THEN
      UNDISCH_TAC `(x2:real^3) IN kb` THEN
      UNDISCH_TAC `(x2:real^3) IN frontier(interval[a,b])` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^3`; `w:real^N->bool`;
                 `IMAGE (p:real^3->real^N) kb`;
                 `IMAGE (p:real^3->real^N) (frontier(interval[a,b]))`]
    MOI_S5A_SETDIST_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; FRONTIER_EQ_EMPTY] THEN
    REWRITE_TAC[DE_MORGAN_THM; INTERVAL_NE_EMPTY; DIMINDEX_3] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
        `!i. 1 <= i /\ i <= 3 ==> (a:real^3)$i < (b:real^3)$i`) (concl th)))
      THEN ASM_REWRITE_TAC[];
      MESON_TAC[BOUNDED_INTERVAL; NOT_BOUNDED_UNIV]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) o (p:real^3->real^N)`; `u:real^3->bool`;
                 `t:real^3->bool`] MOI_S5A_MARGIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[a:real^3,b]` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^N->bool` THEN
        ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`x1:real^3`; `x2:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x1:real^3) IN interval[a,b] /\ (x2:real^3) IN interval[a,b]`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `u SUBSET interval[a:real^3,b]` THEN
        UNDISCH_TAC `(x1:real^3) IN u` THEN UNDISCH_TAC `(x2:real^3) IN u` THEN
        SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "pinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (p:real^3->real^N) (interval[a,b]) SUBSET w` THEN
      UNDISCH_TAC `(x1:real^3) IN interval[a,b]` THEN
      UNDISCH_TAC `(x2:real^3) IN interval[a,b]` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "marg"))) THEN
  ABBREV_TAC `e1 = setdist(IMAGE (h:real^N->real^3) (IMAGE p kb),
                           IMAGE h (IMAGE (p:real^3->real^N)
                                     (frontier(interval[a,b]))))` THEN
  EXISTS_TAC `min e1 rho` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real^3`; `y:real^3`; `z:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `y IN IMAGE (h:real^N->real^3) (IMAGE (p:real^3->real^N) kb)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `y IN IMAGE ((h:real^N->real^3) o (p:real^3->real^N)) u`
    MP_TAC THENL
     [USE_THEN "marg" MATCH_MP_TAC THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[o_THM] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IMAGE_o] THEN
      UNDISCH_TAC `u SUBSET (kb:real^3->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "mark" (MP_TAC o SPECL
   [`IMAGE (p:real^3->real^N) (interval[a,b])`;
    `IMAGE (p:real^3->real^N) (frontier(interval[a,b]))`;
    `IMAGE (p:real^3->real^N) kb`; `f:real^N->real^3`; `h:real^N->real^3`;
    `e1:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (p:real^3->real^N) kb SUBSET IMAGE p (interval[a,b])`
      THEN UNDISCH_TAC `DISJOINT (IMAGE (p:real^3->real^N) kb)
                   (IMAGE p (frontier (interval[a,b])))` THEN
      SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
      USE_THEN "hinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (p:real^3->real^N) (interval[a,b]) SUBSET w` THEN
      UNDISCH_TAC `(x1:real^N) IN IMAGE (p:real^3->real^N) (interval[a,b])` THEN
      UNDISCH_TAC `(x2:real^N) IN IMAGE (p:real^3->real^N) (interval[a,b])` THEN
      SET_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `min e1 rho` THEN
      REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `IMAGE (p:real^3->real^N) (frontier(interval[a,b])) SUBSET
                   IMAGE p (interval[a,b])` THEN
      UNDISCH_TAC
       `(x:real^N) IN IMAGE (p:real^3->real^N) (frontier (interval[a:real^3,b]))`
      THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
      EXPAND_TAC "e1" THEN MATCH_MP_TAC SETDIST_LE_DIST THEN
      CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    UNDISCH_TAC `y IN IMAGE (h:real^N->real^3) (IMAGE (p:real^3->real^N) kb)`
    THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 1. The context of the approximation stage (hypotheses of APPROX with the *)
(* compact cores kk of moi_s35_source_ok fixed), and the model cube.        *)
(* ------------------------------------------------------------------------- *)

let moi_s5a_ctx = new_definition
 `moi_s5a_ctx (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
              (h:real^N->real^3) (w:real^N->real^3->bool)
              (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
              (psi:(real^N->bool)->real^3->real^N) (kk:real^N->real^N->bool) <=>
    graph_in_complex t l /\
    h continuous_on UNIONS t /\
    (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
    (!v. {v} IN l ==> open (w v) /\ IMAGE h (derived_dual_cell t l v) SUBSET w v) /\
    moi_s35_charts t l (\v. {x | x IN UNIONS t /\ h x IN w v}) av bv psi /\
    moi_s35_source_ok t l av bv psi /\
    (!v. {v} IN l
         ==> compact (kk v) /\
             (!cc. (!e. abs(cc e) <= &1 / &512)
                   ==> kk v SUBSET (subtopology euclidean (UNIONS t)) interior_of
                                   (moi_s35_csrc t l av bv psi cc v)) /\
             (!e. moi_s35_edge l e
                  ==> DISJOINT (kk v) (IMAGE (psi e) moi_s35_stube))) /\
    UNIONS l SUBSET UNIONS {kk v | v | {v} IN l}`;;

(* Edges at a vertex. *)

let moi_s5a_edges = new_definition
 `moi_s5a_edges (l:(real^N->bool)->bool) (av:(real^N->bool)->real^N)
                (bv:(real^N->bool)->real^N) v =
    {e | moi_s35_edge l e /\ (av e = v \/ bv e = v)}`;;

let MOI_S5A_CUBE_IN = prove
 (`!x:real^3. x IN moi_s35_cube <=>
              abs(x$1) <= &1 /\ abs(x$2) <= &1 /\ abs(x$3) <= &1`,
  REWRITE_TAC[moi_s35_cube; IN_INTERVAL; DIMINDEX_3; FORALL_3;
              VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S5A_MODEL_RW = prove
 (`(!x:real^3. x IN moi_s35_lower <=> x IN moi_s35_cube /\ x$3 <= &0) /\
   (!x:real^3. x IN moi_s35_upper <=> x IN moi_s35_cube /\ &0 <= x$3) /\
   (!x:real^3. x IN moi_s35_mid <=> x IN moi_s35_cube /\ x$3 = &0) /\
   (!x:real^3. x IN moi_s35_slab <=> x IN moi_s35_cube /\ abs(x$3) <= &1 / &8) /\
   (!x:real^3. x IN moi_s35_dom <=> x IN moi_s35_cube /\ x$3 <= &1 / &8) /\
   (!x:real^3. x IN moi_s35_stube <=>
       &1 / &8 <= moi_s35_n x /\ moi_s35_n x <= &3 / &8 /\
       abs(x$3) <= &1 / &16) /\
   (!x:real^3. x IN moi_s35_ttube <=>
       &3 / &16 <= moi_s35_n x /\ moi_s35_n x <= &5 / &16 /\
       abs(x$3) <= &1 / &32) /\
   (!x:real^3. x IN moi_s35_bcell <=>
       x IN moi_s35_cube /\ (moi_s35_n x - &1 / &4) / &8 <= x$3) /\
   (!x:real^3. x IN moi_s35_bann <=>
       &5 / &32 <= moi_s35_n x /\ moi_s35_n x <= &11 / &32 /\
       x$3 = (moi_s35_n x - &1 / &4) / &8) /\
   (!x:real^3 r c. x IN moi_s35_sq r c <=> moi_s35_n x = r /\ x$3 = c) /\
   (!x:real^3 c. x IN moi_s35_level c <=> x IN moi_s35_cube /\ x$3 = c) /\
   (!x:real^3 c. x IN moi_s35_aflat c <=>
       &3 / &16 <= moi_s35_n x /\ moi_s35_n x <= &5 / &16 /\ x$3 = c)`,
  REWRITE_TAC[moi_s35_lower; moi_s35_upper; moi_s35_mid; moi_s35_slab;
              moi_s35_dom; moi_s35_stube; moi_s35_ttube; moi_s35_bcell;
              moi_s35_bann; moi_s35_sq; moi_s35_level; moi_s35_aflat;
              IN_ELIM_THM]);;

(* A rewrite list reducing model memberships to coordinates. *)

let MOI_S5A_MODEL_CONV_THMS =
  [MOI_S5A_MODEL_RW; MOI_S5A_CUBE_IN; moi_s35_n];;

let MOI_S5A_MODEL_BASIC = prove
 (`moi_s35_slab SUBSET moi_s35_cube /\ moi_s35_dom SUBSET moi_s35_cube /\
   moi_s35_lower SUBSET moi_s35_cube /\ moi_s35_upper SUBSET moi_s35_cube /\
   moi_s35_bcell SUBSET moi_s35_cube /\
   moi_s35_lower SUBSET moi_s35_dom /\
   moi_s35_slab INTER moi_s35_upper SUBSET moi_s35_dom /\
   moi_s35_dom SUBSET moi_s35_lower UNION (moi_s35_slab INTER moi_s35_upper) /\
   moi_s35_bcell INTER moi_s35_lower SUBSET moi_s35_slab /\
   moi_s35_lower INTER moi_s35_upper = moi_s35_mid /\
   moi_s35_stube SUBSET moi_s35_slab /\ moi_s35_stube SUBSET moi_s35_dom /\
   moi_s35_ttube SUBSET moi_s35_stube /\
   moi_s35_level (&1 / &8) SUBSET moi_s35_slab INTER moi_s35_upper /\
   moi_s35_bann SUBSET moi_s35_bcell INTER moi_s35_slab /\
   moi_s35_cube = moi_s35_lower UNION moi_s35_upper`,
  REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_UNION] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REPEAT CONJ_TAC THEN
  GEN_TAC THEN REAL_ARITH_TAC);;
(* ------------------------------------------------------------------------- *)
(* 2. Source geometry: the chart of an edge, dual cells against slabs.      *)
(* ------------------------------------------------------------------------- *)

let MOI_S5A_EDGE_CHART = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> {av e} IN l /\ {bv e} IN l /\ ~(av e = bv e) /\
         segment[av e,bv e] = e /\
         (psi e) continuous_on moi_s35_cube /\
         (!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\ psi e x = psi e y
                ==> x = y) /\
         pl_map_on moi_s35_cube (psi e) /\
         IMAGE (psi e) moi_s35_lower = derived_dual_cell t l (av e) /\
         IMAGE (psi e) moi_s35_upper = derived_dual_cell t l (bv e) /\
         IMAGE (psi e) moi_s35_cube =
           derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e) /\
         derived_dual_cell t l (av e) INTER derived_dual_cell t l (bv e) =
           IMAGE (psi e) moi_s35_mid /\
         (!x. x IN moi_s35_slab
              ==> psi e x IN UNIONS t /\ h(psi e x) IN w(av e) /\
                  h(psi e x) IN w(bv e)) /\
         (!x. x IN moi_s35_slab /\ psi e x IN UNIONS l
              ==> moi_s35_n x < &1 / &16)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5a_ctx; moi_s35_charts] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
    can (term_match [] `!e. moi_s35_edge (l:(real^N->bool)->bool) e ==> P e`)
    (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:real^N->real^3`) STRIP_ASSUME_TAC))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism;
    homeomorphism] o check (can (term_match []
      `pl_homeomorphism (moi_s35_cube,s:real^N->bool) (f,g)`) o concl)) THEN
  MP_TAC MOI_S5A_MODEL_BASIC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
          (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(AP_TERM `q:real^N->real^3` th)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `derived_dual_cell t l ((av:(real^N->bool)->real^N) e) INTER
    derived_dual_cell t l ((bv:(real^N->bool)->real^N) e) =
    IMAGE (psi (e:real^N->bool)) moi_s35_mid`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
      `moi_s35_lower INTER moi_s35_upper = moi_s35_mid`) o concl)) THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> can (term_match []
      `IMAGE (f:real^3->real^N) moi_s35_lower = s`) (concl th) ||
      can (term_match [] `IMAGE (f:real^3->real^N) moi_s35_upper = s`)
      (concl th)))) THEN
    UNDISCH_TAC `!x. x IN moi_s35_cube
                     ==> (q:real^N->real^3) (psi (e:real^N->bool) x) = x` THEN
    UNDISCH_TAC `moi_s35_lower SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `moi_s35_upper SUBSET moi_s35_cube` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN moi_s35_slab
        ==> psi (e:real^N->bool) x IN UNIONS (t:(real^N->bool)->bool) /\
            (h:real^N->real^3)(psi e x) IN
              (w:real^N->real^3->bool)((av:(real^N->bool)->real^N) e) /\
            h(psi e x) IN w((bv:(real^N->bool)->real^N) e)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `IMAGE (f:real^3->real^N) moi_s35_slab SUBSET s`) o concl)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  FIRST_ASSUM(fun th -> ACCEPT_TAC th ORELSE (fun g -> ACCEPT_TAC(SYM th) g)));;
let MOI_S5A_CTX_BASIC = prove
 (`!t l (h:real^N->real^3) w av bv psi kk.
     moi_s5a_ctx t l h w av bv psi kk
     ==> graph_in_complex t l /\ h continuous_on UNIONS t /\
         (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
         (!v. {v} IN l
              ==> open (w v) /\ IMAGE h (derived_dual_cell t l v) SUBSET w v) /\
         moi_s35_source_ok t l av bv psi /\
         (!v. {v} IN l
              ==> compact (kk v) /\
                  (!cc. (!e. abs(cc e) <= &1 / &512)
                        ==> kk v SUBSET (subtopology euclidean (UNIONS t))
                                        interior_of
                                        (moi_s35_csrc t l av bv psi cc v)) /\
                  (!e. moi_s35_edge l e
                       ==> DISJOINT (kk v) (IMAGE (psi e) moi_s35_stube))) /\
         UNIONS l SUBSET UNIONS {kk v | v | {v} IN l}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5a_ctx] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let MOI_S5A_SLAB_DISJ = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e e'.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\
     moi_s35_edge l e' /\ ~(e = e')
     ==> DISJOINT (IMAGE (psi e) moi_s35_slab) (IMAGE (psi e') moi_s35_slab)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s5a_ctx; moi_s35_charts] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
   `!e e'. moi_s35_edge (l:(real^N->bool)->bool) e /\ moi_s35_edge l e' /\
           ~(e = e')
           ==> DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                               moi_s35_slab)
                        (IMAGE (psi e') moi_s35_slab)`) o concl)) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5A_EDGE_ENDS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e e'.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\
     moi_s35_edge l e' /\
     (av e' = av e \/ av e' = bv e) /\ (bv e' = av e \/ bv e' = bv e)
     ==> e' = e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e':real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `segment[(av:(real^N->bool)->real^N) e',bv e'] =
                segment[av e,(bv:(real^N->bool)->real^N) e]`
  MP_TAC THENL
   [REWRITE_TAC[SEGMENT_EQ] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN2 DISJ_CASES_TAC DISJ_CASES_TAC) THEN
    ASM_REWRITE_TAC[INSERT_AC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* Two dual cells of distinct vertices are disjoint, or they meet in the    *)
(* splitting disk of the edge joining them.                                  *)

let MOI_S5A_CELL_PAIR = prove
 (`!t l (h:real^N->real^3) w av bv psi kk u v.
     moi_s5a_ctx t l h w av bv psi kk /\ {u} IN l /\ {v} IN l /\ ~(u = v)
     ==> derived_dual_cell t l u INTER derived_dual_cell t l v = {} \/
         ?e. moi_s35_edge l e /\
             ((av e = u /\ bv e = v) \/ (av e = v /\ bv e = u)) /\
             derived_dual_cell t l u INTER derived_dual_cell t l v =
             IMAGE (psi e) moi_s35_mid`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `segment[u:real^N,v] IN l` THENL
   [ALL_TAC;
    DISJ1_TAC THEN MATCH_MP_TAC MOI_FTA_CELLS_DISJOINT THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MOI_S5A_CTX_BASIC th)])]
  THEN
  DISJ2_TAC THEN EXISTS_TAC `segment[u:real^N,v]` THEN
  SUBGOAL_THEN `moi_s35_edge l (segment[u:real^N,v])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s35_edge; AFF_DIM_SEGMENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `segment[u:real^N,v]`] MOI_S5A_EDGE_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{av(segment[u:real^N,v]),bv(segment[u,v])} = {u,v}` MP_TAC
  THENL
   [FIRST_X_ASSUM(MP_TAC o check (can (term_match []
      `segment[x:real^N,y] = segment[u,v]`) o concl)) THEN
    REWRITE_TAC[SEGMENT_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `{a:real^N,b} = {u,v} <=>
                        (a = u /\ b = v) \/ (a = v /\ b = u) \/
                        (a = u /\ b = u /\ u = v) \/ (a = v /\ b = v /\ u = v)`]
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match []
    `derived_dual_cell (t:(real^N->bool)->bool) l a INTER
     derived_dual_cell t l b = IMAGE (f:real^3->real^N) s`) o concl)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[INTER_COMM]);;

let MOI_S5A_MID_SLAB = prove
 (`moi_s35_mid SUBSET moi_s35_slab`,
  REWRITE_TAC[SUBSET] THEN REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

(* SF3: a dual cell misses the slab of every edge not at its vertex. *)

let MOI_S5A_CELL_SLAB = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e u.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\ {u} IN l /\
     ~(u = av e) /\ ~(u = bv e)
     ==> DISJOINT (derived_dual_cell t l u) (IMAGE (psi e) moi_s35_slab)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v. v = (av:(real^N->bool)->real^N) e \/ v = bv e
        ==> DISJOINT (derived_dual_cell t l u INTER derived_dual_cell t l v)
                     (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                            moi_s35_slab)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `u:real^N`; `v:real^N`] MOI_S5A_CELL_PAIR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM DISJ_CASES_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `e3:real^N->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))
    THENL [REWRITE_TAC[DISJOINT_EMPTY]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!s t u:real^N->bool. s SUBSET t /\ DISJOINT t u ==> DISJOINT s u`) THEN
    EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e3) moi_s35_slab`
    THEN SIMP_TAC[IMAGE_SUBSET; MOI_S5A_MID_SLAB] THEN
    MATCH_MP_TAC MOI_S5A_SLAB_DISJ THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`;
      `w:real^N->real^3->bool`; `av:(real^N->bool)->real^N`;
      `bv:(real^N->bool)->real^N`; `kk:real^N->real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    REPEAT(FIRST_X_ASSUM DISJ_CASES_TAC) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab SUBSET
    derived_dual_cell t l ((av:(real^N->bool)->real^N) e) UNION
    derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)`
  MP_TAC THENL
   [FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (can (term_match []
      `IMAGE (f:real^3->real^N) moi_s35_cube = s`) o concl)) THEN
    SIMP_TAC[IMAGE_SUBSET; MOI_S5A_MODEL_BASIC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `(av:(real^N->bool)->real^N) e` th) THEN
                          MP_TAC(SPEC `(bv:(real^N->bool)->real^N) e` th)) THEN
  REWRITE_TAC[] THEN SET_TAC[]);;
(* The enlarged cells C''_v and the pierced cells C'_v near an edge.        *)

let MOI_S5A_IMAGE_SLAB_PIECES = prove
 (`!(psi:(real^N->bool)->real^3->real^N) e.
     IMAGE (psi e) (moi_s35_bcell INTER moi_s35_lower) SUBSET
     IMAGE (psi e) moi_s35_slab /\
     IMAGE (psi e) (moi_s35_slab INTER moi_s35_upper) SUBSET
     IMAGE (psi e) moi_s35_slab /\
     IMAGE (psi e) (moi_s35_bcell INTER moi_s35_slab) SUBSET
     IMAGE (psi e) moi_s35_slab /\
     IMAGE (psi e) {x | x IN moi_s35_slab /\ x$3 <= c} SUBSET
     IMAGE (psi e) moi_s35_slab`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
  MP_TAC MOI_S5A_MODEL_BASIC THEN SET_TAC[]);;

let MOI_S5A_CPLUS_SUB = prove
 (`!t l av bv (psi:(real^N->bool)->real^3->real^N) v.
     moi_s35_cplus t l av bv psi v SUBSET
     derived_dual_cell t l v UNION
     UNIONS {IMAGE (psi e) moi_s35_slab | e | e IN moi_s5a_edges l av bv v}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_cplus; moi_s5a_edges; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  MP_TAC(ISPEC `psi:(real^N->bool)->real^3->real^N` MOI_S5A_IMAGE_SLAB_PIECES)
  THEN REWRITE_TAC[SUBSET] THEN MESON_TAC[]);;

(* A-side: the chart image of the A-chart domain lies in C''_a, and C''_a  *)
(* lies in it plus the slabs of the other edges at a.                       *)

let MOI_S5A_CPLUS_A = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> IMAGE (psi e) moi_s35_dom SUBSET moi_s35_cplus t l av bv psi (av e) /\
         IMAGE (psi e) moi_s35_slab SUBSET moi_s35_cplus t l av bv psi (av e) /\
         moi_s35_cplus t l av bv psi (av e) SUBSET
         IMAGE (psi e) moi_s35_dom UNION
         UNIONS {IMAGE (psi e') moi_s35_slab | e' |
                 e' IN moi_s5a_edges l av bv (av e) /\ ~(e' = e)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_MODEL_BASIC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
          (moi_s35_slab INTER moi_s35_upper) SUBSET
    UNIONS {IMAGE (psi e') (moi_s35_slab INTER moi_s35_upper) | e' |
            moi_s35_edge l e' /\ (av:(real^N->bool)->real^N) e' = av e}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_dom SUBSET
    IMAGE (psi e) moi_s35_lower UNION
    IMAGE (psi e) (moi_s35_slab INTER moi_s35_upper) /\
    IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab SUBSET
    IMAGE (psi e) moi_s35_lower UNION
    IMAGE (psi e) (moi_s35_slab INTER moi_s35_upper)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN CONJ_TAC THEN
    MATCH_MP_TAC IMAGE_SUBSET THENL
     [ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `moi_s35_cube = moi_s35_lower UNION moi_s35_upper` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_cplus; moi_s5a_edges; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower
                UNION IMAGE (psi e) (moi_s35_slab INTER moi_s35_upper)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `u SUBSET k ==> (c:real^N->bool) UNION u SUBSET
                                          (c UNION f) UNION k`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_lower
                UNION IMAGE (psi e) (moi_s35_slab INTER moi_s35_upper)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `u SUBSET k ==> (c:real^N->bool) UNION u SUBSET
                                          (c UNION f) UNION k`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(DISJ_CASES_THEN2 (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) MP_TAC)
  THENL
   [DISJ1_TAC THEN
    UNDISCH_TAC `y IN derived_dual_cell t l ((av:(real^N->bool)->real^N) e)` THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (can (term_match []
      `IMAGE (f:real^3->real^N) moi_s35_lower = s`) o concl)) THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> y IN IMAGE (f:real^3->real^N) s
                                         ==> y IN IMAGE f t`) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN EXISTS_TAC `e':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                   (moi_s35_bcell INTER moi_s35_lower)` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> y IN IMAGE (f:real^3->real^N) s
                                         ==> y IN IMAGE f t`) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `e':real^N->bool = e` THENL
     [DISJ1_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     (moi_s35_slab INTER moi_s35_upper)` THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> y IN IMAGE (f:real^3->real^N) s
                                           ==> y IN IMAGE f t`) THEN
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `e':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                     (moi_s35_slab INTER moi_s35_upper)` THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> y IN IMAGE (f:real^3->real^N) s
                                           ==> y IN IMAGE f t`) THEN
      SET_TAC[]]]);;
(* B-side: the chart image of the altered B-cell and of the upper half lie *)
(* in C''_b, and C''_b lies in their union plus the other slabs at b.       *)

let MOI_S5A_CPLUS_B = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> IMAGE (psi e) moi_s35_bcell SUBSET moi_s35_cplus t l av bv psi (bv e) /\
         IMAGE (psi e) moi_s35_upper SUBSET moi_s35_cplus t l av bv psi (bv e) /\
         moi_s35_cplus t l av bv psi (bv e) SUBSET
         IMAGE (psi e) (moi_s35_bcell UNION moi_s35_upper) UNION
         UNIONS {IMAGE (psi e') moi_s35_slab | e' |
                 e' IN moi_s5a_edges l av bv (bv e) /\ ~(e' = e)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_MODEL_BASIC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
          (moi_s35_bcell INTER moi_s35_lower) SUBSET
    UNIONS {IMAGE (psi e') (moi_s35_bcell INTER moi_s35_lower) | e' |
            moi_s35_edge l e' /\ (bv:(real^N->bool)->real^N) e' = bv e}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_bcell SUBSET
    IMAGE (psi e) (moi_s35_bcell INTER moi_s35_lower) UNION
    IMAGE (psi e) moi_s35_upper`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    UNDISCH_TAC `moi_s35_bcell SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `moi_s35_cube = moi_s35_lower UNION moi_s35_upper` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_cplus; moi_s5a_edges; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                      (moi_s35_bcell INTER moi_s35_lower) UNION
                IMAGE (psi e) moi_s35_upper` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `u SUBSET f ==> u UNION (c:real^N->bool) SUBSET
                                          (c UNION f) UNION k`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(DISJ_CASES_THEN2 (DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) MP_TAC)
  THENL
   [DISJ1_TAC THEN
    UNDISCH_TAC `y IN derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)` THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (can (term_match []
      `IMAGE (f:real^3->real^N) moi_s35_upper = s`) o concl)) THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> y IN IMAGE (f:real^3->real^N) s
                                         ==> y IN IMAGE f t`) THEN
    SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `e':real^N->bool = e` THENL
     [DISJ1_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     (moi_s35_bcell INTER moi_s35_lower)` THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> y IN IMAGE (f:real^3->real^N) s
                                           ==> y IN IMAGE f t`) THEN
      SET_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `e':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                     (moi_s35_bcell INTER moi_s35_lower)` THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> y IN IMAGE (f:real^3->real^N) s
                                           ==> y IN IMAGE f t`) THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN EXISTS_TAC `e':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                   (moi_s35_slab INTER moi_s35_upper)` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> y IN IMAGE (f:real^3->real^N) s
                                         ==> y IN IMAGE f t`) THEN
    SET_TAC[]]);;
(* SF4: the pierced cells inside the slab of an edge.                        *)

let MOI_S5A_OTHER_SLAB = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e e' s y.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\
     moi_s35_edge l e' /\ ~(e' = e) /\ s SUBSET moi_s35_slab /\
     y IN IMAGE (psi e) moi_s35_slab /\ y IN IMAGE (psi e') s
     ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`; `e':real^N->bool`] MOI_S5A_SLAB_DISJ) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(psi:(real^N->bool)->real^3->real^N) e'`; `s:real^3->bool`;
                 `moi_s35_slab`] IMAGE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab`
  THEN UNDISCH_TAC `(y:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e') s`
  THEN SET_TAC[]);;

let MOI_S5A_SLABCUT_SUB = prove
 (`!c. {x:real^3 | x IN moi_s35_slab /\ x$3 <= c} SUBSET moi_s35_slab`,
  SET_TAC[]);;

let MOI_S5A_CSRC_SLAB = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e cc.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> moi_s35_csrc t l av bv psi cc (av e) INTER IMAGE (psi e) moi_s35_slab =
         IMAGE (psi e) {x | x IN moi_s35_slab /\ x$3 <= cc e} /\
         moi_s35_csrc t l av bv psi cc (bv e) INTER IMAGE (psi e) moi_s35_slab =
         IMAGE (psi e) (moi_s35_bcell INTER moi_s35_slab)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e} SUBSET
    moi_s35_slab /\
    moi_s35_bcell INTER moi_s35_slab SUBSET moi_s35_slab /\
    moi_s35_bcell INTER moi_s35_lower SUBSET moi_s35_slab`
  STRIP_ASSUME_TAC THENL
   [MP_TAC MOI_S5A_MODEL_BASIC THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e' s y. moi_s35_edge l e' /\ ~(e' = e) /\ s SUBSET moi_s35_slab /\
             y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab /\
             y IN IMAGE (psi e') s ==> F`
  (LABEL_TAC "oth") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5A_OTHER_SLAB THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`; `e':real^N->bool`; `s:real^3->bool`; `y:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_csrc; EXTENSION; IN_INTER; IN_UNION; IN_DIFF;
              UNIONS_GSPEC; IN_ELIM_THM] THEN
  CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (DISJ_CASES_THEN2 MP_TAC MP_TAC) MP_TAC) THENL
     [DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o
        REWRITE_RULE[NOT_EXISTS_THM] o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `e':real^N->bool = e` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REMOVE_THEN "oth" (MP_TAC o SPECL [`e':real^N->bool`;
        `moi_s35_bcell INTER moi_s35_slab`; `y:real^N`]) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `e':real^N->bool = e` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "oth" (MP_TAC o SPECL [`e':real^N->bool`;
        `{x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e'}`;
        `y:real^N`]) THEN
      ASM_REWRITE_TAC[MOI_S5A_SLABCUT_SUB]];
    DISCH_TAC THEN CONJ_TAC THENL
     [DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     {x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e}`
      THEN UNDISCH_TAC `{x | x IN moi_s35_slab /\
                            x$3 <= (cc:(real^N->bool)->real) e} SUBSET
                        moi_s35_slab` THEN
      SET_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(DISJ_CASES_THEN2 (DISJ_CASES_THEN2 MP_TAC MP_TAC) MP_TAC) THENL
     [DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o
        REWRITE_RULE[NOT_EXISTS_THM] o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `e':real^N->bool = e` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "oth" (MP_TAC o SPECL [`e':real^N->bool`;
        `moi_s35_bcell INTER moi_s35_slab`; `y:real^N`]) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `e':real^N->bool = e` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REMOVE_THEN "oth" (MP_TAC o SPECL [`e':real^N->bool`;
        `{x | x IN moi_s35_slab /\ x$3 <= (cc:(real^N->bool)->real) e'}`;
        `y:real^N`]) THEN
      ASM_REWRITE_TAC[MOI_S5A_SLABCUT_SUB]];
    DISCH_TAC THEN CONJ_TAC THENL
     [DISJ1_TAC THEN DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     (moi_s35_bcell INTER moi_s35_slab)` THEN
      UNDISCH_TAC `moi_s35_bcell INTER moi_s35_slab SUBSET moi_s35_slab` THEN
      SET_TAC[]]]);;
let MOI_S5A_CSRC_MONO = prove
 (`!t l av bv (psi:(real^N->bool)->real^3->real^N) cc cc' v.
     (!e. cc e <= cc' e)
     ==> moi_s35_csrc t l av bv psi cc v SUBSET moi_s35_csrc t l av bv psi cc' v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s35_csrc; SUBSET; IN_UNION; IN_DIFF; UNIONS_GSPEC;
              IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  MATCH_MP_TAC(TAUT `(c ==> c') ==> (a \/ b) \/ c ==> (a \/ b) \/ c'`) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^N->bool` THEN
  MATCH_MP_TAC(TAUT `(b ==> b') ==> a /\ b ==> a /\ b'`) THEN
  SPEC_TAC(`(psi:(real^N->bool)->real^3->real^N) e`,`f:real^3->real^N`) THEN
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET t ==> (y:real^N) IN IMAGE (f:real^3->real^N) s ==> y IN IMAGE f t`)
  THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool`) THEN MESON_TAC[REAL_LE_TRANS]);;

let MOI_S5A_CELL_COMPACT = prove
 (`!n (s:real^N->bool) bs.
     pl_cell_with_boundary n s bs ==> compact s /\ compact bs /\ bs SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `pl_homeomorphism (k,s) ((f:real^N->real^N),(g:real^N->real^N))`
  THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (k:real^N->bool) /\ relative_frontier k SUBSET k /\
                compact (relative_frontier k)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `compact (k:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED;
                 COMPACT_RELATIVE_FRONTIER_BOUNDED; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^N->real^N) k = s`)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^N->real^N) k = s`)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

let MOI_S5A_SOURCE_FACTS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l
     ==> (!cc. (!e. abs(cc e) <= &1 / &512)
               ==> moi_s35_csrc t l av bv psi cc v SUBSET
                   moi_s35_cplus t l av bv psi v /\
                   (?bs. pl_cell_with_boundary 3
                           (moi_s35_csrc t l av bv psi cc v) bs)) /\
         (?bs. pl_cell_with_boundary 3 (moi_s35_cplus t l av bv psi v) bs) /\
         (?bs. pl_cell_with_boundary 3 (moi_s35_cbig t l av bv psi v) bs) /\
         compact (moi_s35_cplus t l av bv psi v) /\
         compact (moi_s35_cbig t l av bv psi v) /\
         (!cc. (!e. abs(cc e) <= &1 / &512)
               ==> compact (moi_s35_csrc t l av bv psi cc v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
    CONJUNCT2 o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  REWRITE_TAC[moi_s35_source_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "src") (CONJUNCTS_THEN2
    (LABEL_TAC "cp") (K ALL_TAC))) THEN
  REMOVE_THEN "cp" (MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `b1:real^N->bool`)
    (X_CHOOSE_TAC `b2:real^N->bool`)) THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    REMOVE_THEN "src" (MP_TAC o SPECL [`cc:(real^N->bool)->real`; `v:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    EXISTS_TAC `b1:real^N->bool` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `b2:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MOI_S5A_CELL_COMPACT];
    ASM_MESON_TAC[MOI_S5A_CELL_COMPACT];
    GEN_TAC THEN DISCH_TAC THEN
    REMOVE_THEN "src" (MP_TAC o SPECL [`cc:(real^N->bool)->real`; `v:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[MOI_S5A_CELL_COMPACT]]);;
let MOI_S5A_NOT_BOTH_ENDS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e u v.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\
     ~(u = v) /\ ~(segment[u,v] IN l)
     ==> ~((av e = u \/ bv e = u) /\ (av e = v \/ bv e = v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[(av:(real^N->bool)->real^N) e,bv e] IN l` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_s35_edge]; ALL_TAC] THEN
  UNDISCH_TAC `~(segment[u:real^N,v] IN l)` THEN
  UNDISCH_TAC `~(u:real^N = v)` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN MESON_TAC[SEGMENT_SYM]);;

let MOI_S5A_CPLUS_DISJ = prove
 (`!t l (h:real^N->real^3) w av bv psi kk u v.
     moi_s5a_ctx t l h w av bv psi kk /\ {u} IN l /\ {v} IN l /\ ~(u = v) /\
     ~(segment[u,v] IN l)
     ==> DISJOINT (moi_s35_cplus t l av bv psi u) (moi_s35_cplus t l av bv psi v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!e y x x'. moi_s35_edge l e /\
               ((av:(real^N->bool)->real^N) e = x \/
                (bv:(real^N->bool)->real^N) e = x) /\
               ((x = u /\ x' = v) \/ (x = v /\ x' = u)) /\
               y IN derived_dual_cell t l x' /\
               y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab
               ==> F`
  (LABEL_TAC "d1") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`; `u:real^N`; `v:real^N`] MOI_S5A_NOT_BOTH_ENDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`; `x':real^N`] MOI_S5A_CELL_SLAB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(((av:(real^N->bool)->real^N) e = u \/ bv e = u) /\
                     (av e = v \/ bv e = v))` THEN
      UNDISCH_TAC `(x = u /\ x' = v) \/ (x:real^N = v /\ x' = u)` THEN
      UNDISCH_TAC `(av:(real^N->bool)->real^N) e = x \/ bv e = x` THEN
      UNDISCH_TAC `{u:real^N} IN l` THEN UNDISCH_TAC `{v:real^N} IN l` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN MESON_TAC[];
      UNDISCH_TAC `(y:real^N) IN derived_dual_cell t l x'` THEN
      UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     moi_s35_slab` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e e' y. moi_s35_edge l e /\
             ((av:(real^N->bool)->real^N) e = u \/
              (bv:(real^N->bool)->real^N) e = u) /\
             moi_s35_edge l e' /\ (av e' = v \/ bv e' = v) /\
             y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab /\
             y IN IMAGE (psi e') moi_s35_slab
             ==> F`
  (LABEL_TAC "d2") THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e':real^N->bool`; `u:real^N`; `v:real^N`] MOI_S5A_NOT_BOTH_ENDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`; `e':real^N->bool`] MOI_S5A_SLAB_DISJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(((av:(real^N->bool)->real^N) e' = u \/ bv e' = u) /\
                     (av e' = v \/ bv e' = v))` THEN
      UNDISCH_TAC `(av:(real^N->bool)->real^N) e' = u \/ bv e' = u` THEN
      UNDISCH_TAC `(av:(real^N->bool)->real^N) e' = v \/ bv e' = v` THEN
      CONV_TAC TAUT;
      UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                     moi_s35_slab` THEN
      UNDISCH_TAC `y IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     moi_s35_slab` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (derived_dual_cell (t:(real^N->bool)->bool) l u)
                         (derived_dual_cell t l v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN MATCH_MP_TAC MOI_FTA_CELLS_DISJOINT THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MOI_S5A_CTX_BASIC th)]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `u:real^N`] MOI_S5A_CPLUS_SUB) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `v:real^N`] MOI_S5A_CPLUS_SUB) THEN
  UNDISCH_TAC `DISJOINT (derived_dual_cell (t:(real^N->bool)->bool) l u)
                        (derived_dual_cell t l v)` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; SUBSET; IN_UNION;
              UNIONS_GSPEC; IN_ELIM_THM; moi_s5a_edges] THEN
  DISCH_THEN(LABEL_TAC "dj") THEN DISCH_THEN(LABEL_TAC "sv") THEN
  DISCH_THEN(LABEL_TAC "su") THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  REMOVE_THEN "su" (MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e:real^N->bool`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))) THEN
  (REMOVE_THEN "sv" (MP_TAC o SPEC `y:real^N`) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e':real^N->bool`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))) THENL
   [REMOVE_THEN "dj" (MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[];
    USE_THEN "d1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`e':real^N->bool`; `y:real^N`; `v:real^N`;
                          `u:real^N`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "d1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `y:real^N`; `u:real^N`;
                          `v:real^N`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "d2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `e':real^N->bool`; `y:real^N`] THEN
    ASM_REWRITE_TAC[]]);;
let MOI_S5A_CPLUS_SLAB_DISJ = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e v.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\ {v} IN l /\
     ~(v = av e) /\ ~(v = bv e)
     ==> DISJOINT (moi_s35_cplus t l av bv psi v) (IMAGE (psi e) moi_s35_slab)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`; `v:real^N`] MOI_S5A_CELL_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!e'. moi_s35_edge l e' /\
         ((av:(real^N->bool)->real^N) e' = v \/ (bv:(real^N->bool)->real^N) e' = v)
         ==> DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                             moi_s35_slab)
                      (IMAGE (psi e) moi_s35_slab)`
  ASSUME_TAC THENL
   [X_GEN_TAC `e':real^N->bool` THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MATCH_MP_TAC MOI_S5A_SLAB_DISJ THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `kk:real^N->real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(v:real^N = av(e:real^N->bool))` THEN
    UNDISCH_TAC `~(v:real^N = bv(e:real^N->bool))` THEN
    UNDISCH_TAC `(av:(real^N->bool)->real^N) e = v \/ bv e = v` THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `v:real^N`] MOI_S5A_CPLUS_SUB) THEN
  UNDISCH_TAC `DISJOINT (derived_dual_cell t l v)
                 (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab)` THEN
  UNDISCH_TAC
   `!e'. moi_s35_edge l e' /\
         ((av:(real^N->bool)->real^N) e' = v \/ (bv:(real^N->bool)->real^N) e' = v)
         ==> DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                             moi_s35_slab)
                      (IMAGE (psi e) moi_s35_slab)` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; SUBSET; IN_UNION;
              UNIONS_GSPEC; IN_ELIM_THM; moi_s5a_edges] THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 3. Local finiteness of the target images: the dual cells lie in open     *)
(* vertex stars, h is an open map there (vertex charts and invariance of    *)
(* domain), and only finitely many vertices of the graph are near a vertex. *)
(* ------------------------------------------------------------------------- *)

let MOI_S5A_CELL_OPEN_STAR = prove
 (`!(t:(real^N->bool)->bool) l w.
     graph_in_complex t l /\ {w} IN l
     ==> derived_dual_cell t l w SUBSET moi_sta_open_star t w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool) /\ {w:real^N} IN t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
    REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN
    UNDISCH_TAC `{w:real^N} IN l` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; moi_sta_open_star; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `w:real^N`] MOI_FTA_CELL_IN_STAR) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `x IN derived_dual_cell t l (w:real^N)`
    THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `w:real^N`; `x:real^N`] MOI_FTA_IN_DUAL_CELL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `hh:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `hh:(real^N->bool)->bool`;
                 `s:real^N->bool`; `x:real^N`] MOI_FTA_HULL_INTER_SIMPLEX) THEN
  ASM_SIMP_TAC[MOI_FTA_LF_BAR] THEN
  ASM_CASES_TAC `hh INTER {u | u face_of (s:real^N->bool)} = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `tau:real^N->bool` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_INTER; IN_ELIM_THM] o
    check (can (term_match [] `(tau:real^N->bool) IN a INTER b`) o concl)) THEN
  SUBGOAL_THEN `(w:real^N) IN tau` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain t (hh:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`{w:real^N}`; `tau:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(tau:real^N->bool = {})` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]);;

let MOI_S5A_STAR_IMAGE_OPEN = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w u.
     graph_in_complex t l /\ {w} IN l /\ h continuous_on UNIONS t /\
     (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\ open u
     ==> open (IMAGE h (u INTER moi_sta_open_star t w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool) /\
                {w:real^N} IN t /\
                pl_sphere 2 (UNIONS (simplicial_link t w))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
    REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN
    UNDISCH_TAC `{w:real^N} IN l` THEN SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `w:real^N`]
    MOI_FMB_STAR_SPHERE_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->real^3` (X_CHOOSE_THEN `p':real^3->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_sta_open_star t (w:real^N) SUBSET UNIONS t` ASSUME_TAC THENL
   [REWRITE_TAC[moi_sta_open_star] THEN SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `o0 = (u:real^N->bool) INTER moi_sta_open_star t w` THEN
  SUBGOAL_THEN `open (IMAGE (p:real^N->real^3) o0)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (p:real^N->real^3) (moi_sta_open_star t w)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`p':real^3->real^N`;
                          `moi_sta_open_star t (w:real^N)`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "o0" THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o
    check (can (term_match []
      `homeomorphism (a:real^N->bool,b:real^3->bool) (f,g)`) o concl)) THEN
  SUBGOAL_THEN `(o0:real^N->bool) SUBSET moi_sta_open_star t w`
  ASSUME_TAC THENL [EXPAND_TAC "o0" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^3) o0 =
    IMAGE (h o (p':real^3->real^N)) (IMAGE (p:real^N->real^3) o0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> IMAGE (f:real^N->real^3) s = IMAGE g s`)
    THEN UNDISCH_TAC `(o0:real^N->bool) SUBSET moi_sta_open_star t w` THEN
    UNDISCH_TAC `!x. x IN moi_sta_open_star t w
                     ==> (p':real^3->real^N) ((p:real^N->real^3) x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (p:real^N->real^3) (moi_sta_open_star t w)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool`
      THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(o0:real^N->bool) SUBSET moi_sta_open_star t w` THEN
      UNDISCH_TAC `moi_sta_open_star t (w:real^N) SUBSET UNIONS t` THEN
      UNDISCH_TAC `!x. x IN moi_sta_open_star t w
                       ==> (p':real^3->real^N) ((p:real^N->real^3) x) = x` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IMAGE_o; o_THM] THEN MESON_TAC[]];
    REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x1:real^3`; `x2:real^3`] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)
       MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^N) IN moi_sta_open_star t w /\
                  (b:real^N) IN moi_sta_open_star t w` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(o0:real^N->bool) SUBSET moi_sta_open_star t w` THEN
      UNDISCH_TAC `(a:real^N) IN o0` THEN UNDISCH_TAC `(b:real^N) IN o0` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p':real^3->real^N) (p a) = a /\ p' (p b) = b`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(h:real^N->real^3) (p' ((p:real^N->real^3) a)) = h (p' (p b))`
    THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    AP_TERM_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN UNIONS t /\ y IN UNIONS t /\ (h:real^N->real^3) x = h y
             ==> x = y`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_sta_open_star t (w:real^N) SUBSET UNIONS t` THEN
    UNDISCH_TAC `(a:real^N) IN moi_sta_open_star t w` THEN
    UNDISCH_TAC `(b:real^N) IN moi_sta_open_star t w` THEN SET_TAC[]]);;
(* Model sets: continuity of the square norm, closed and open level sets.   *)

let MOI_S5A_N_CONT = prove
 (`!x:real^3. (\x. lift(moi_s35_n x)) continuous (at x)`,
  GEN_TAC THEN REWRITE_TAC[moi_s35_n] THEN
  MP_TAC(ISPECL [`\x:real^3. abs(x$1)`; `\x:real^3. abs(x$2)`; `(:real^3)`]
    CONTINUOUS_ON_MAX_1) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS_COMPONENT THEN
    REWRITE_TAC[CONTINUOUS_ON_ID];
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]]);;

let MOI_S5A_COMP_CONT = prove
 (`!x:real^3. (\x. lift(x$3)) continuous (at x)`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_LIFT_COMPONENT THEN
  REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC);;

(* A real function of x$3 and n x that is affine in each, and the closed and *)
(* open sets cut out by comparing two of them.                                *)

let MOI_S5A_AFF_CONT = prove
 (`!a b c x:real^3. (\x. lift(a * moi_s35_n x + b * x$3 + c)) continuous (at x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_CMUL THEN REWRITE_TAC[MOI_S5A_N_CONT]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_CMUL THEN REWRITE_TAC[MOI_S5A_COMP_CONT]);;

let MOI_S5A_AFF_CLOSED_OPEN = prove
 (`!a b c. closed {x:real^3 | a * moi_s35_n x + b * x$3 + c <= &0} /\
           closed {x:real^3 | a * moi_s35_n x + b * x$3 + c = &0} /\
           open {x:real^3 | a * moi_s35_n x + b * x$3 + c < &0}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `c:real`] MOI_S5A_AFF_CONT) THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x:real^3. lift(a * moi_s35_n x + b * x$3 + c)`;
                   `{y:real^1 | y$1 <= &0}`] CONTINUOUS_CLOSED_PREIMAGE_UNIV);
    MP_TAC(ISPECL [`\x:real^3. lift(a * moi_s35_n x + b * x$3 + c)`;
                   `{vec 0:real^1}`] CONTINUOUS_CLOSED_PREIMAGE_UNIV);
    MP_TAC(ISPECL [`\x:real^3. lift(a * moi_s35_n x + b * x$3 + c)`;
                   `{y:real^1 | y$1 < &0}`] CONTINUOUS_OPEN_PREIMAGE_UNIV)] THEN
  ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE; CLOSED_SING;
                  OPEN_HALFSPACE_COMPONENT_LT; IN_ELIM_THM; IN_SING] THEN
  REWRITE_TAC[GSYM drop; LIFT_DROP; GSYM LIFT_NUM; LIFT_EQ]);;
(* A tactic proving `closed s` for a model set s given as an intersection  *)
(* of sets a * n x + b * x$3 + c <= 0 (the triples), by set equality.      *)

let MOI_S5A_AFF_CLOSED_TAC (abcs:(term*term*term) list) : tactic =
  fun (asl,w) ->
    let s = rand w in
    let piece (a,b,c) =
      vsubst [a,`a:real`; b,`b:real`; c,`c:real`]
        `{x:real^3 | a * moi_s35_n x + b * x$3 + c <= &0}` in
    let ps = map piece abcs in
    let intr = end_itlist (fun p q -> mk_comb(mk_comb(
      `(INTER):(real^3->bool)->(real^3->bool)->(real^3->bool)`,p),q)) ps in
    (SUBGOAL_THEN (mk_eq(s,intr)) SUBST1_TAC THENL
      [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
       REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC;
       REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
       REWRITE_TAC[MOI_S5A_AFF_CLOSED_OPEN]]) (asl,w);;

let MOI_S5A_MODEL_CLOSED = prove
 (`closed moi_s35_cube /\ closed moi_s35_slab /\ closed moi_s35_dom /\
   closed moi_s35_lower /\ closed moi_s35_upper /\ closed moi_s35_bcell /\
   closed moi_s35_stube /\ closed moi_s35_ttube /\ closed moi_s35_bann /\
   (!c. closed (moi_s35_level c)) /\ (!r c. closed (moi_s35_sq r c)) /\
   (!c. closed (moi_s35_aflat c))`,
  let cube = [`&1`,`&0`,`-- &1`; `&0`,`&1`,`-- &1`; `&0`,`-- &1`,`-- &1`] in
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN TRY GEN_TAC THENL
   [MOI_S5A_AFF_CLOSED_TAC cube;
    MOI_S5A_AFF_CLOSED_TAC
     (cube @ [`&0`,`&1`,`-- &1 / &8`; `&0`,`-- &1`,`-- &1 / &8`]);
    MOI_S5A_AFF_CLOSED_TAC (cube @ [`&0`,`&1`,`-- &1 / &8`]);
    MOI_S5A_AFF_CLOSED_TAC (cube @ [`&0`,`&1`,`&0`]);
    MOI_S5A_AFF_CLOSED_TAC (cube @ [`&0`,`-- &1`,`&0`]);
    MOI_S5A_AFF_CLOSED_TAC (cube @ [`&1 / &8`,`-- &1`,`-- &1 / &32`]);
    MOI_S5A_AFF_CLOSED_TAC
     [`-- &1`,`&0`,`&1 / &8`; `&1`,`&0`,`-- &3 / &8`;
      `&0`,`&1`,`-- &1 / &16`; `&0`,`-- &1`,`-- &1 / &16`];
    MOI_S5A_AFF_CLOSED_TAC
     [`-- &1`,`&0`,`&3 / &16`; `&1`,`&0`,`-- &5 / &16`;
      `&0`,`&1`,`-- &1 / &32`; `&0`,`-- &1`,`-- &1 / &32`];
    MOI_S5A_AFF_CLOSED_TAC
     [`-- &1`,`&0`,`&5 / &32`; `&1`,`&0`,`-- &11 / &32`;
      `&1 / &8`,`-- &1`,`-- &1 / &32`; `-- &1 / &8`,`&1`,`&1 / &32`];
    MOI_S5A_AFF_CLOSED_TAC (cube @ [`&0`,`&1`,`--c`; `&0`,`-- &1`,`c:real`]);
    MOI_S5A_AFF_CLOSED_TAC
     [`&1`,`&0`,`--r`; `-- &1`,`&0`,`r:real`; `&0`,`&1`,`--c`;
      `&0`,`-- &1`,`c:real`];
    MOI_S5A_AFF_CLOSED_TAC
     [`-- &1`,`&0`,`&3 / &16`; `&1`,`&0`,`-- &5 / &16`; `&0`,`&1`,`--c`;
      `&0`,`-- &1`,`c:real`]]);;

let MOI_S5A_MODEL_COMPACT = prove
 (`compact moi_s35_cube /\ compact moi_s35_slab /\ compact moi_s35_dom /\
   compact moi_s35_lower /\ compact moi_s35_upper /\ compact moi_s35_bcell /\
   compact moi_s35_stube /\ compact moi_s35_ttube /\ compact moi_s35_bann /\
   (!c. compact (moi_s35_level c)) /\ (!r c. compact (moi_s35_sq r c)) /\
   (!c. compact (moi_s35_aflat c))`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; MOI_S5A_MODEL_CLOSED] THEN
  SUBGOAL_THEN `!s:real^3->bool. s SUBSET moi_s35_cube ==> bounded s`
  (LABEL_TAC "bc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `moi_s35_cube` THEN ASM_REWRITE_TAC[moi_s35_cube; BOUNDED_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r c s. s SUBSET {x:real^3 | abs(x$1) <= r /\ abs(x$2) <= r /\ abs(x$3) <= c}
            ==> bounded s`
  (LABEL_TAC "bi") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `interval[--vector[r;r;c]:real^3,vector[r;r;c]]` THEN
    REWRITE_TAC[BOUNDED_INTERVAL] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `(s:real^3->bool) SUBSET t ==> t SUBSET u ==> s SUBSET u`)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_NEG_COMPONENT; VECTOR_3] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN TRY GEN_TAC THEN
  FIRST [USE_THEN "bc" MATCH_MP_TAC THEN REWRITE_TAC[SUBSET] THEN
         REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC;
         USE_THEN "bi" MATCH_MP_TAC THEN
         MAP_EVERY EXISTS_TAC [`abs r`; `abs c`] THEN REWRITE_TAC[SUBSET] THEN
         REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REWRITE_TAC[IN_ELIM_THM] THEN
         GEN_TAC THEN REAL_ARITH_TAC;
         USE_THEN "bi" MATCH_MP_TAC THEN
         MAP_EVERY EXISTS_TAC [`&1`; `abs c`] THEN REWRITE_TAC[SUBSET] THEN
         REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REWRITE_TAC[IN_ELIM_THM] THEN
         GEN_TAC THEN REAL_ARITH_TAC]);;
(* Neighbours of a vertex (itself and the ends of its edges) and the region *)
(* of a vertex (the enlarged cell and the slabs of its edges).              *)

let moi_s5a_nbrs = new_definition
 `moi_s5a_nbrs (l:(real^N->bool)->bool) (av:(real^N->bool)->real^N)
               (bv:(real^N->bool)->real^N) v =
    v INSERT (IMAGE av (moi_s5a_edges l av bv v) UNION
              IMAGE bv (moi_s5a_edges l av bv v))`;;

let moi_s5a_region = new_definition
 `moi_s5a_region (t:(real^N->bool)->bool) l av bv
                 (psi:(real^N->bool)->real^3->real^N) v =
    moi_s35_cplus t l av bv psi v UNION
    UNIONS {IMAGE (psi e) moi_s35_slab | e | e IN moi_s5a_edges l av bv v}`;;

let MOI_S5A_EDGES_FINITE = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l
     ==> FINITE (moi_s5a_edges l av bv v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool) /\
                l SUBSET t /\ (v:real^N) IN UNIONS t`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S5A_CTX_BASIC) THEN
    REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN
    UNDISCH_TAC `{v:real^N} IN l` THEN REWRITE_TAC[IN_UNIONS] THEN
    MESON_TAC[SUBSET; IN_SING];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{e | e IN t /\ aff_dim e = &1 /\ (v:real^N) IN e}` THEN
  ASM_SIMP_TAC[MOI_FN1_EDGES_FINITE] THEN
  REWRITE_TAC[SUBSET; moi_s5a_edges; IN_ELIM_THM] THEN
  X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  (MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  UNDISCH_TAC `moi_s35_edge l (e:real^N->bool)` THEN
  REWRITE_TAC[moi_s35_edge] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
    `segment[a:real^N,b] = e`) o concl)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `v:real^N`)) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT]);;

let MOI_S5A_VS_FINITE = prove
 (`!(t:(real^N->bool)->bool) w.
     lf_simplicial_complex t /\ w IN UNIONS t
     ==> FINITE {w' | {w'} IN t /\ ?s. s IN t /\ w IN s /\ w' IN s}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS {{x:real^N | x extreme_point_of s} | s |
                      s IN t /\ ~(s INTER u = {})}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `polytope (s:real^N->bool)` MP_TAC THENL
       [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
      REWRITE_TAC[polytope] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:real^N->bool` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[EXTREME_POINT_OF_CONVEX_HULL]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `w':real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM FACE_OF_SING] THEN
  SUBGOAL_THEN `{w':real^N} INTER s face_of s` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;
let MOI_S5A_REGION_FACTS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l
     ==> FINITE (moi_s5a_nbrs l av bv v) /\
         (!x. x IN moi_s5a_nbrs l av bv v ==> {x} IN l) /\
         moi_s5a_region t l av bv psi v SUBSET
           UNIONS {derived_dual_cell t l x | x | x IN moi_s5a_nbrs l av bv v} /\
         compact (moi_s5a_region t l av bv psi v) /\
         moi_s5a_region t l av bv psi v SUBSET UNIONS t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `v:real^N`] MOI_S5A_EDGES_FINITE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN moi_s5a_edges l av bv (v:real^N)
        ==> {(av:(real^N->bool)->real^N) e} IN l /\
            {(bv:(real^N->bool)->real^N) e} IN l /\
            IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab SUBSET
            derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e) /\
            compact (IMAGE (psi e) moi_s35_slab)`
  (LABEL_TAC "ed") THENL
   [X_GEN_TAC `e:real^N->bool` THEN REWRITE_TAC[moi_s5a_edges; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
        `IMAGE (f:real^3->real^N) moi_s35_cube = s`) o concl)) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[MOI_S5A_MODEL_BASIC];
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[MOI_S5A_MODEL_BASIC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN moi_s5a_nbrs l av bv (v:real^N) ==> {x} IN l`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5a_nbrs; IN_INSERT; IN_UNION; IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN
      (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN REMOVE_THEN "ed" (MP_TAC o SPEC `e:real^N->bool`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN moi_s5a_nbrs l av bv (v:real^N)
        ==> derived_dual_cell t l x SUBSET UNIONS t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `x:real^N`] MOI_FTA_CELL_IN_STAR) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MOI_S5A_CTX_BASIC th)]);
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_s5a_region t l av bv psi (v:real^N) SUBSET
    UNIONS {derived_dual_cell t l x | x | x IN moi_s5a_nbrs l av bv v}`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5a_region] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `v:real^N`] MOI_S5A_CPLUS_SUB) THEN
    MATCH_MP_TAC(SET_RULE
     `d SUBSET t /\ u SUBSET t ==> c SUBSET d UNION u
      ==> (c:real^N->bool) UNION u SUBSET t`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `v:real^N` THEN
      ASM_REWRITE_TAC[moi_s5a_nbrs; IN_INSERT];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "ed" (MP_TAC o SPEC `e:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `y IN derived_dual_cell t l ((av:(real^N->bool)->real^N) e) \/
                  y IN derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    (STRIP_TAC THENL
      [EXISTS_TAC `(av:(real^N->bool)->real^N) e`;
       EXISTS_TAC `(bv:(real^N->bool)->real^N) e`]) THEN
    ASM_REWRITE_TAC[moi_s5a_nbrs; IN_INSERT; IN_UNION] THEN
    DISJ2_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s5a_nbrs; FINITE_INSERT; FINITE_UNION] THEN
    ASM_SIMP_TAC[FINITE_IMAGE];
    REWRITE_TAC[moi_s5a_region] THEN MATCH_MP_TAC COMPACT_UNION THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC COMPACT_UNIONS THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      ASM_SIMP_TAC[FINITE_IMAGE; SET_RULE `{x:real^N->bool | x IN s} = s`] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_SIMP_TAC[]];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {derived_dual_cell t l x | x | x IN moi_s5a_nbrs l av bv
                        (v:real^N)}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    ASM_SIMP_TAC[]]);;
let MOI_S5A_NBRS_SYM = prove
 (`!(l:(real^N->bool)->bool) av bv v x.
     x IN moi_s5a_nbrs l av bv v ==> v IN moi_s5a_nbrs l av bv x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s5a_nbrs; moi_s5a_edges; IN_INSERT; IN_UNION; IN_IMAGE;
              IN_ELIM_THM] THEN
  MESON_TAC[]);;
let MOI_S5A_LF = prove
 (`!t l (h:real^N->real^3) w av bv psi kk u.
     moi_s5a_ctx t l h w av bv psi kk /\ {u} IN l
     ==> ?r fs. &0 < r /\ FINITE fs /\
                !v x y. {v} IN l /\ ~(v IN fs) /\
                        x IN moi_s5a_region t l av bv psi u /\
                        y IN moi_s5a_region t l av bv psi v
                        ==> r <= dist(h x,h y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  SUBGOAL_THEN `l SUBSET (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
    SIMP_TAC[graph_in_complex; simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `graph_in_complex (t:(real^N->bool)->bool) l` THEN
    SIMP_TAC[graph_in_complex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `u:real^N`] MOI_S5A_REGION_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `oo = UNIONS {moi_sta_open_star t x | x |
                           x IN moi_s5a_nbrs l av bv (u:real^N)}` THEN
  SUBGOAL_THEN `moi_s5a_region t l av bv psi (u:real^N) SUBSET oo /\
                oo SUBSET UNIONS (t:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS {derived_dual_cell t l x | x |
                          x IN moi_s5a_nbrs l av bv (u:real^N)}` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "oo" THEN
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `x:real^N`] MOI_S5A_CELL_OPEN_STAR) THEN
      ASM_SIMP_TAC[SUBSET];
      EXPAND_TAC "oo" THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[moi_sta_open_star] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (h:real^N->real^3) oo)` ASSUME_TAC THENL
   [EXPAND_TAC "oo" THEN REWRITE_TAC[IMAGE_UNIONS] THEN
    MATCH_MP_TAC OPEN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `x:real^N`; `(:real^N)`] MOI_S5A_STAR_IMAGE_OPEN) THEN
    REWRITE_TAC[INTER_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_UNIV] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) (moi_s5a_region t l av bv psi u)`;
                 `(:real^3) DIFF IMAGE (h:real^N->real^3) oo`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS (t:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_s5a_region t l av bv psi (u:real^N) SUBSET oo` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "sep"))) THEN
  EXISTS_TAC `d:real` THEN
  EXISTS_TAC `UNIONS {moi_s5a_nbrs l av bv w' | w' |
                      {w'} IN l /\
                      ?x s. x IN moi_s5a_nbrs l av bv (u:real^N) /\ s IN t /\
                            x IN s /\ w' IN s}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `UNIONS {{w' | {w'} IN t /\
                               ?s. s IN t /\ x IN s /\ w' IN s} | x |
                          x IN moi_s5a_nbrs l av bv (u:real^N)}` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
         [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
          ASM_REWRITE_TAC[SET_RULE `{x:real^N | x IN s} = s`];
          REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `x:real^N` THEN
          DISCH_TAC THEN MATCH_MP_TAC MOI_S5A_VS_FINITE THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `{x:real^N} IN t` MP_TAC THENL
           [UNDISCH_TAC `l SUBSET (t:(real^N->bool)->bool)` THEN
            REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
            ASM_SIMP_TAC[];
            REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[IN_SING]]];
        REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
        X_GEN_TAC `w':real^N` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `x:real^N`
          (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC))) THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `l SUBSET (t:(real^N->bool)->bool)` THEN
          UNDISCH_TAC `{w':real^N} IN l` THEN SET_TAC[];
          EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]]];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `w':real^N` THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `w':real^N`] MOI_S5A_REGION_FACTS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N`; `x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^3) y IN IMAGE h oo` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    REMOVE_THEN "sep" (MP_TAC o SPECL [`(h:real^N->real^3) x`;
                                     `(h:real^N->real^3) y`]) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `v:real^N`] MOI_S5A_REGION_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN oo` MP_TAC THENL
   [SUBGOAL_THEN `y:real^N = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN UNIONS t /\ y IN UNIONS t /\ (h:real^N->real^3) x = h y
             ==> x = y`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXPAND_TAC "oo" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?w'. w' IN moi_s5a_nbrs l av bv (v:real^N) /\
                     (y:real^N) IN derived_dual_cell t l w'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5a_region t l av bv psi (v:real^N) SUBSET
                 UNIONS {derived_dual_cell t l x | x |
                         x IN moi_s5a_nbrs l av bv v}` THEN
    UNDISCH_TAC `(y:real^N) IN moi_s5a_region t l av bv psi v` THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{w':real^N} IN l` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `w':real^N`] MOI_FTA_CELL_IN_STAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~((v:real^N) IN
                 UNIONS {moi_s5a_nbrs l av bv w' | w' |
                         {w'} IN l /\
                         ?x s. x IN moi_s5a_nbrs l av bv u /\ s IN t /\
                               x IN s /\ w' IN s})` THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  EXISTS_TAC `w':real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`x0:real^N`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN moi_sta_open_star t x0` THEN
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_S5A_NBRS_SYM THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 4. Error bookkeeping.  The pieces of a vertex (compact sets in its       *)
(* region whose images under the approximations must stay apart from those  *)
(* of other vertices), a positive separation radius eta per vertex, the     *)
(* approximation predicate, and per-edge goodness of an error bound.        *)
(* ------------------------------------------------------------------------- *)

let moi_s5a_pieces = new_definition
 `moi_s5a_pieces (t:(real^N->bool)->bool) l av bv
                 (psi:(real^N->bool)->real^3->real^N) (kk:real^N->real^N->bool) v =
    {moi_s35_cplus t l av bv psi v, kk v} UNION
    IMAGE (\e. IMAGE (psi e) moi_s35_slab) (moi_s5a_edges l av bv v) UNION
    IMAGE (\e. IMAGE (psi e) moi_s35_stube) (moi_s5a_edges l av bv v) UNION
    IMAGE (\e. IMAGE (psi e) (moi_s35_level (&1 / &8))) (moi_s5a_edges l av bv v)`;;

let moi_s5a_apx = new_definition
 `moi_s5a_apx (t:(real^N->bool)->bool) l av bv psi (h:real^N->real^3)
              (ff:real^N->real^N->real^3) (err:real^N->real) <=>
    !v. {v} IN l
        ==> pl_map_on (moi_s35_cplus t l av bv psi v) (ff v) /\
            (!x y. x IN moi_s35_cplus t l av bv psi v /\
                   y IN moi_s35_cplus t l av bv psi v /\ ff v x = ff v y
                   ==> x = y) /\
            (!x. x IN moi_s35_cplus t l av bv psi v ==> dist(ff v x,h x) < err v)`;;

let moi_s5a_good = new_definition
 `moi_s5a_good (t:(real^N->bool)->bool) l (h:real^N->real^3) av bv psi e d
               (P:(real^N->real^N->real^3)->((real^N->bool)->real)->bool) <=>
    !ff err cc. moi_s5a_apx t l av bv psi h ff err /\
                err (av e) + err (bv e) <= d /\ (!e. abs(cc e) <= &1 / &512)
                ==> P ff cc`;;

let MOI_S5A_GOOD_MONO = prove
 (`!t l (h:real^N->real^3) av bv psi e d d' P.
     moi_s5a_good t l h av bv psi e d P /\ d' <= d
     ==> moi_s5a_good t l h av bv psi e d' P`,
  REWRITE_TAC[moi_s5a_good] THEN MESON_TAC[REAL_LE_TRANS]);;

let MOI_S5A_GOOD_AND = prove
 (`!t l (h:real^N->real^3) av bv psi e d1 d2 P Q.
     moi_s5a_good t l h av bv psi e d1 P /\ moi_s5a_good t l h av bv psi e d2 Q
     ==> moi_s5a_good t l h av bv psi e (min d1 d2) (\ff cc. P ff cc /\ Q ff cc)`,
  REWRITE_TAC[moi_s5a_good] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `err:real^N->real` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5A_PIECES_FACTS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l
     ==> FINITE (moi_s5a_pieces t l av bv psi kk v) /\
         !X. X IN moi_s5a_pieces t l av bv psi kk v
             ==> compact X /\ X SUBSET moi_s5a_region t l av bv psi v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `v:real^N`] MOI_S5A_EDGES_FINITE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_s5a_pieces; FINITE_UNION; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_SIMP_TAC[FINITE_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN moi_s5a_edges l av bv (v:real^N)
        ==> compact (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                           moi_s35_slab) /\
            compact (IMAGE (psi e) moi_s35_stube) /\
            compact (IMAGE (psi e) (moi_s35_level (&1 / &8)))`
  (LABEL_TAC "cp") THENL
   [X_GEN_TAC `e:real^N->bool` THEN REWRITE_TAC[moi_s5a_edges; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    MP_TAC MOI_S5A_MODEL_BASIC THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(kk:real^N->real^N->bool) v SUBSET
                moi_s35_cplus t l av bv psi v /\ compact (kk v)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (MP_TAC o SPEC `\e:real^N->bool. &0`) (K ALL_TAC))) THEN
    BETA_TAC THEN REWRITE_TAC[REAL_ABS_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `\e:real^N->bool. &0` o CONJUNCT1) THEN
    BETA_TAC THEN REWRITE_TAC[REAL_ABS_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `(kk:real^N->real^N->bool) v SUBSET
                 subtopology euclidean (UNIONS t) interior_of
                 moi_s35_csrc t l av bv psi (\e. &0) v` THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS (t:(real^N->bool)->bool))`;
                   `moi_s35_csrc t l av bv psi (\e:real^N->bool. &0) v`]
      INTERIOR_OF_SUBSET) THEN
    UNDISCH_TAC `moi_s35_csrc t l av bv psi (\e:real^N->bool. &0) (v:real^N)
                 SUBSET moi_s35_cplus t l av bv psi v` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[moi_s5a_pieces; IN_UNION; IN_INSERT; NOT_IN_EMPTY; IN_IMAGE] THEN
  X_GEN_TAC `X:real^N->bool` THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THENL
   [DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[moi_s5a_region] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[moi_s5a_region] THEN
    UNDISCH_TAC `(kk:real^N->real^N->bool) v SUBSET
                 moi_s35_cplus t l av bv psi v` THEN SET_TAC[];
    ALL_TAC; ALL_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 SUBST1_TAC
    ASSUME_TAC)) THEN
  BETA_TAC THEN
  REMOVE_THEN "cp" (MP_TAC o SPEC `e:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_s5a_region] THEN
  MATCH_MP_TAC(SET_RULE `x SUBSET u ==> x SUBSET (c:real^N->bool) UNION u`) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab` THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC IMAGE_SUBSET THEN MP_TAC MOI_S5A_MODEL_BASIC THEN SET_TAC[];
     REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
     X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
     ASM_REWRITE_TAC[]]));;
let MOI_S5A_PIECES_SEP = prove
 (`!t l (h:real^N->real^3) w av bv psi kk.
     moi_s5a_ctx t l h w av bv psi kk
     ==> ?eta. !u. {u} IN l
               ==> &0 < eta u /\
                   !v X Y. {v} IN l /\ X IN moi_s5a_pieces t l av bv psi kk u /\
                           Y IN moi_s5a_pieces t l av bv psi kk v /\
                           DISJOINT X Y /\ ~(X = {}) /\ ~(Y = {})
                           ==> eta u <= setdist(IMAGE h X,IMAGE h Y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN
  X_GEN_TAC `u:real^N` THEN
  ASM_CASES_TAC `{u:real^N} IN l` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `u:real^N`] MOI_S5A_LF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `fs:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "far"))))) THEN
  SUBGOAL_THEN
   `!v X. {v} IN l /\
          X IN moi_s5a_pieces t l av bv psi (kk:real^N->real^N->bool) v
          ==> compact X /\ X SUBSET moi_s5a_region t l av bv psi v /\
              X SUBSET UNIONS t`
  (LABEL_TAC "pc") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `v:real^N`] MOI_S5A_PIECES_FACTS) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `v:real^N`] MOI_S5A_REGION_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `X:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\(v:real^N) e. !X Y. {v} IN l /\
                 X IN moi_s5a_pieces t l av bv psi (kk:real^N->real^N->bool) u /\
                 Y IN moi_s5a_pieces t l av bv psi kk v /\
                 DISJOINT X Y /\ ~(X = {}) /\ ~(Y = {})
                 ==> e <= setdist(IMAGE (h:real^N->real^3) X,IMAGE h Y)`;
    `fs:real^N->bool`] MOI_S5A_FINITE_POS_MIN) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; MESON_TAC[REAL_LE_TRANS]] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `{v:real^N} IN l` THENL
     [ALL_TAC; EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01]] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`\(X:real^N->bool) e. !Y.
                 X IN moi_s5a_pieces t l av bv psi (kk:real^N->real^N->bool) u /\
                 Y IN moi_s5a_pieces t l av bv psi kk v /\
                 DISJOINT X Y /\ ~(X = {}) /\ ~(Y = {})
                 ==> e <= setdist(IMAGE (h:real^N->real^3) X,IMAGE h Y)`;
      `moi_s5a_pieces t l av bv psi kk (u:real^N)`] MOI_S5A_FINITE_POS_MIN) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
          `h:real^N->real^3`; `w:real^N->real^3->bool`;
          `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
          `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
          `u:real^N`] MOI_S5A_PIECES_FACTS) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [ALL_TAC; MESON_TAC[REAL_LE_TRANS]] THEN
      X_GEN_TAC `X:real^N->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL
       [`\(Y:real^N->bool) e.
               X IN moi_s5a_pieces t l av bv psi (kk:real^N->real^N->bool) u /\
               Y IN moi_s5a_pieces t l av bv psi kk v /\
               DISJOINT X Y /\ ~(X = {}) /\ ~(Y = {})
               ==> e <= setdist(IMAGE (h:real^N->real^3) X,IMAGE h Y)`;
        `moi_s5a_pieces t l av bv psi kk (v:real^N)`] MOI_S5A_FINITE_POS_MIN)
      THEN BETA_TAC THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
            `h:real^N->real^3`; `w:real^N->real^3->bool`;
            `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
            `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
            `v:real^N`] MOI_S5A_PIECES_FACTS) THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        CONJ_TAC THENL [ALL_TAC; MESON_TAC[REAL_LE_TRANS]] THEN
        X_GEN_TAC `Y:real^N->bool` THEN DISCH_TAC THEN
        ASM_CASES_TAC `DISJOINT (X:real^N->bool) Y /\ ~(X = {}) /\ ~(Y = {})`
        THENL
         [EXISTS_TAC `setdist(IMAGE (h:real^N->real^3) X,IMAGE h Y)` THEN
          REWRITE_TAC[REAL_LE_REFL] THEN
          MATCH_MP_TAC MOI_S5A_SETDIST_POS THEN
          EXISTS_TAC `UNIONS (t:(real^N->bool)->bool)` THEN
          ASM_REWRITE_TAC[] THEN
          USE_THEN "pc" (MP_TAC o SPECL [`u:real^N`; `X:real^N->bool`]) THEN
          USE_THEN "pc" (MP_TAC o SPECL [`v:real^N`; `Y:real^N->bool`]) THEN
          ASM_SIMP_TAC[];
          EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01]];
        MESON_TAC[]];
      MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "near"))) THEN
  EXISTS_TAC `min r e0` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:real^N`; `X:real^N->bool`; `Y:real^N->bool`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `(v:real^N) IN fs` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e0:real` THEN
    REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
    USE_THEN "near" (MP_TAC o SPEC `v:real^N`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `r:real` THEN
  REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_SETDIST THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN X_GEN_TAC `y:real^N` THEN
  DISCH_TAC THEN
  USE_THEN "far" MATCH_MP_TAC THEN EXISTS_TAC `v:real^N` THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "pc" (MP_TAC o SPECL [`u:real^N`; `X:real^N->bool`]) THEN
  USE_THEN "pc" (MP_TAC o SPECL [`v:real^N`; `Y:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;
let moi_s5a_etaok = new_definition
 `moi_s5a_etaok (t:(real^N->bool)->bool) l (h:real^N->real^3) av bv psi kk
                (eta:real^N->real) <=>
    !u. {u} IN l
        ==> &0 < eta u /\
            !v X Y. {v} IN l /\ X IN moi_s5a_pieces t l av bv psi kk u /\
                    Y IN moi_s5a_pieces t l av bv psi kk v /\
                    DISJOINT X Y /\ ~(X = {}) /\ ~(Y = {})
                    ==> eta u <= setdist(IMAGE h X,IMAGE h Y)`;;

let MOI_S5A_ETA_EXISTS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk.
     moi_s5a_ctx t l h w av bv psi kk
     ==> ?eta. moi_s5a_etaok t l h av bv psi kk eta`,
  REWRITE_TAC[moi_s5a_etaok; MOI_S5A_PIECES_SEP]);;

let MOI_S5A_GLOBAL_SEP = prove
 (`!t l (h:real^N->real^3) av bv psi kk eta err u v X Y
    (f1:real^N->real^3) f2.
     moi_s5a_etaok t l h av bv psi kk eta /\
     (!u. {u} IN l ==> &3 * err u <= eta u) /\
     {u} IN l /\ {v} IN l /\
     X IN moi_s5a_pieces t l av bv psi kk u /\
     Y IN moi_s5a_pieces t l av bv psi kk v /\ DISJOINT X Y /\
     (!x. x IN X ==> dist(f1 x,h x) < err u) /\
     (!y. y IN Y ==> dist(f2 y,h y) < err v)
     ==> DISJOINT (IMAGE f1 X) (IMAGE f2 Y)`,
  REWRITE_TAC[moi_s5a_etaok] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "eta") (CONJUNCTS_THEN2
    (LABEL_TAC "err") STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_S5A_APPROX_DISJOINT THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `(err:real^N->real) u`;
                        `(err:real^N->real) v`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(eta:real^N->real) u <= setdist(IMAGE (h:real^N->real^3) X,IMAGE h Y) /\
    eta v <= setdist(IMAGE h X,IMAGE h Y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "eta" (fun th -> MP_TAC(CONJUNCT2(MP (SPEC `u:real^N` th)
        (ASSUME `{u:real^N} IN l`)))) THEN
      DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `X:real^N->bool`;
                                 `Y:real^N->bool`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      USE_THEN "eta" (fun th -> MP_TAC(CONJUNCT2(MP (SPEC `v:real^N` th)
        (ASSUME `{v:real^N} IN l`)))) THEN
      DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `Y:real^N->bool`;
                                 `X:real^N->bool`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[SETDIST_SYM]]];
    ALL_TAC] THEN
  USE_THEN "err" (fun th ->
    MP_TAC(MP (SPEC `u:real^N` th) (ASSUME `{u:real^N} IN l`)) THEN
    MP_TAC(MP (SPEC `v:real^N` th) (ASSUME `{v:real^N} IN l`))) THEN
  MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) X`; `IMAGE (h:real^N->real^3) Y`]
    SETDIST_POS_LE) THEN
  UNDISCH_TAC `(eta:real^N->real) u <= setdist(IMAGE (h:real^N->real^3) X,IMAGE h Y)` THEN
  UNDISCH_TAC `(eta:real^N->real) v <= setdist(IMAGE (h:real^N->real^3) X,IMAGE h Y)` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 5. The chart maps of an edge: A-chart ach e = f_a o psi e on the model   *)
(* domain, B-chart bch e = f_b o psi e on the altered B-cell and the upper  *)
(* half, both close to h o psi e.                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S5A_DOM_INTERVAL = prove
 (`moi_s35_dom = interval[vector[-- &1; -- &1; -- &1],vector[&1; &1; &1 / &8]]`,
  REWRITE_TAC[EXTENSION; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC);;

(* Model inclusions as assumptions, without the two set equations (which   *)
(* would rewrite the cube or lower INTER upper everywhere).                 *)

let MOI_S5A_MODEL_TAC : tactic =
  MP_TAC MOI_S5A_MODEL_BASIC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC
    (filter (fun t -> not(is_eq(concl t))) (CONJUNCTS th)));;

let MOI_S5A_CHART_MAPS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk ff err e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s5a_apx t l av bv psi h ff err /\
     moi_s35_edge l e
     ==> (moi_s35_ach ff av psi e) continuous_on moi_s35_dom /\
         (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\
                moi_s35_ach ff av psi e x = moi_s35_ach ff av psi e y ==> x = y) /\
         (!s. s SUBSET moi_s35_dom /\ locally_polyhedral s
              ==> pl_map_on s (moi_s35_ach ff av psi e)) /\
         (!x. x IN moi_s35_dom
              ==> dist(moi_s35_ach ff av psi e x,h(psi e x)) < err (av e)) /\
         (moi_s35_bch ff bv psi e) continuous_on
           (moi_s35_bcell UNION moi_s35_upper) /\
         (!x y. x IN moi_s35_bcell UNION moi_s35_upper /\
                y IN moi_s35_bcell UNION moi_s35_upper /\
                moi_s35_bch ff bv psi e x = moi_s35_bch ff bv psi e y ==> x = y) /\
         (!s. s SUBSET moi_s35_bcell UNION moi_s35_upper /\ locally_polyhedral s
              ==> pl_map_on s (moi_s35_bch ff bv psi e)) /\
         (!x. x IN moi_s35_bcell UNION moi_s35_upper
              ==> dist(moi_s35_bch ff bv psi e x,h(psi e x)) < err (bv e)) /\
         (h o psi e) continuous_on moi_s35_cube /\
         (!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                h(psi e x) = h(psi e y) ==> x = y) /\
         IMAGE (psi e) moi_s35_cube SUBSET UNIONS t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_CPLUS_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s5a_apx t l av bv psi (h:real^N->real^3) ff err` THEN
  REWRITE_TAC[moi_s5a_apx] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `(av:(real^N->bool)->real^N) e` th) THEN
                       MP_TAC(SPEC `(bv:(real^N->bool)->real^N) e` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "plb") (CONJUNCTS_THEN2
    (LABEL_TAC "injb") (LABEL_TAC "clb"))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pla") (CONJUNCTS_THEN2
    (LABEL_TAC "inja") (LABEL_TAC "cla"))) THEN
  MOI_S5A_MODEL_TAC THEN
  SUBGOAL_THEN `moi_s35_bcell UNION moi_s35_upper SUBSET moi_s35_cube /\
                IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                  (moi_s35_bcell UNION moi_s35_upper) SUBSET
                moi_s35_cplus t l av bv psi (bv e)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `moi_s35_bcell SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `moi_s35_upper SUBSET moi_s35_cube` THEN
      SET_TAC[];
      REWRITE_TAC[IMAGE_UNION; UNION_SUBSET] THEN CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_cube
                SUBSET UNIONS t`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e x IN
                  derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e)`
    MP_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN moi_s35_cube` THEN
      UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_cube =
                   derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `(av:(real^N->bool)->real^N) e`] MOI_FTA_CELL_IN_STAR);
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `(bv:(real^N->bool)->real^N) e`] MOI_FTA_CELL_IN_STAR)] THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^N->real^3) o (psi:(real^N->bool)->real^3->real^N) e)
                continuous_on
                moi_s35_cube` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS (t:(real^N->bool)->bool)` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
          (h:real^N->real^3)((psi:(real^N->bool)->real^3->real^N) e x) =
          h(psi e y) ==> x = y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
             (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`) o
      concl)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN UNIONS t /\ y IN UNIONS t /\ (h:real^N->real^3) x = h y
             ==> x = y`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_cube
                 SUBSET UNIONS t` THEN
    UNDISCH_TAC `(x:real^3) IN moi_s35_cube` THEN
    UNDISCH_TAC `(y:real^3) IN moi_s35_cube` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_ach; moi_s35_bch; o_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
      ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON]];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
             (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`) o
      concl)) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN moi_s35_dom` THEN
      UNDISCH_TAC `moi_s35_dom SUBSET moi_s35_cube` THEN SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN moi_s35_dom` THEN
      UNDISCH_TAC `moi_s35_dom SUBSET moi_s35_cube` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "inja" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN moi_s35_dom` THEN
    UNDISCH_TAC `(y:real^3) IN moi_s35_dom` THEN
    UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) (moi_s35_dom) SUBSET
                 moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
    SET_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `moi_s35_dom` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) (moi_s35_dom)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    REPEAT STRIP_TAC THEN USE_THEN "cla" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN moi_s35_dom` THEN
    UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) (moi_s35_dom) SUBSET
                 moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
    SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
      ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON]];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
             (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`) o
      concl)) THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN moi_s35_bcell UNION moi_s35_upper` THEN
      UNDISCH_TAC `moi_s35_bcell UNION moi_s35_upper SUBSET moi_s35_cube` THEN SET_TAC[];
      UNDISCH_TAC `(y:real^3) IN moi_s35_bcell UNION moi_s35_upper` THEN
      UNDISCH_TAC `moi_s35_bcell UNION moi_s35_upper SUBSET moi_s35_cube` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "injb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN moi_s35_bcell UNION moi_s35_upper` THEN
    UNDISCH_TAC `(y:real^3) IN moi_s35_bcell UNION moi_s35_upper` THEN
    UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) (moi_s35_bcell UNION moi_s35_upper) SUBSET
                 moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
    SET_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `moi_s35_bcell UNION moi_s35_upper` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) (moi_s35_bcell UNION moi_s35_upper)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    REPEAT STRIP_TAC THEN USE_THEN "clb" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN moi_s35_bcell UNION moi_s35_upper` THEN
    UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) (moi_s35_bcell UNION moi_s35_upper) SUBSET
                 moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
    SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_cube
                 SUBSET UNIONS t` THEN ASM_REWRITE_TAC[]]);;
(* Approximation errors are positive (the cells are nonempty), and two     *)
(* approximations keep two disjoint compact source sets apart once the sum  *)
(* of their errors is small.                                                 *)

let MOI_S5A_VERTEX_IN_CELL = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l
     ==> v IN derived_dual_cell t l v /\
         v IN moi_s35_cplus t l av bv psi v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN derived_dual_cell t l v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      GRAPH_TUBE_DUAL_CELLS) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MOI_S5A_CTX_BASIC th)]);
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_REWRITE_TAC[moi_s35_cplus; IN_UNION]]);;

let MOI_S5A_APX_POS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk ff err v.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s5a_apx t l av bv psi h ff err /\
     {v} IN l
     ==> &0 < err v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `v:real^N`] MOI_S5A_VERTEX_IN_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s5a_apx t l av bv psi (h:real^N->real^3) ff err` THEN
  REWRITE_TAC[moi_s5a_apx] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(ff:real^N->real^N->real^3) v v`; `(h:real^N->real^3) v`]
    DIST_POS_LE) THEN
  REAL_ARITH_TAC);;

let MOI_S5A_CPLUS_UNIONS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l
     ==> moi_s35_cplus t l av bv psi v SUBSET UNIONS t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `v:real^N`] MOI_S5A_REGION_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s5a_region t l av bv psi (v:real^N) SUBSET UNIONS t` THEN
  REWRITE_TAC[moi_s5a_region] THEN SET_TAC[]);;

let MOI_S5A_EDGE_SEP = prove
 (`!t l (h:real^N->real^3) w av bv psi kk u v X Y.
     moi_s5a_ctx t l h w av bv psi kk /\ {u} IN l /\ {v} IN l /\
     compact X /\ compact Y /\
     X SUBSET moi_s35_cplus t l av bv psi u /\
     Y SUBSET moi_s35_cplus t l av bv psi v /\ DISJOINT X Y
     ==> ?d. &0 < d /\
             !ff err. moi_s5a_apx t l av bv psi h ff err /\ err u + err v <= d
                      ==> DISJOINT (IMAGE (ff u) X) (IMAGE (ff v) Y)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `X:real^N->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; IMAGE_CLAUSES] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `Y:real^N->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; IMAGE_CLAUSES] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`]
    MOI_S5A_CPLUS_UNIONS) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `u:real^N` th) THEN
                       MP_TAC(SPEC `v:real^N` th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  EXISTS_TAC `setdist(IMAGE (h:real^N->real^3) X,IMAGE h Y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5A_SETDIST_POS THEN
    EXISTS_TAC `UNIONS (t:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5A_APPROX_DISJOINT THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `(err:real^N->real) u`;
                        `(err:real^N->real) v`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s5a_apx t l av bv psi (h:real^N->real^3) ff err` THEN
  REWRITE_TAC[moi_s5a_apx] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `u:real^N` th) THEN
                       MP_TAC(SPEC `v:real^N` th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;
(* An edge e' other than e through one end of e misses the other end.      *)

let MOI_S5A_ENDS_DISTINCT = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e e' x y.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\ moi_s35_edge l e' /\
     ~(e' = e) /\ ((x = av e /\ y = bv e) \/ (x = bv e /\ y = av e)) /\
     (av e' = x \/ bv e' = x)
     ==> ~(av e' = y) /\ ~(bv e' = y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `~((av:(real^N->bool)->real^N) e = bv e)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((av:(real^N->bool)->real^N) e' = av e \/ av e' = bv e) /\
    ((bv:(real^N->bool)->real^N) e' = av e \/ bv e' = bv e) ==> e' = e`
  ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MOI_S5A_EDGE_ENDS THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `((av:(real^N->bool)->real^N) e' = av e \/ av e' = bv e) /\
    ((bv:(real^N->bool)->real^N) e' = av e \/ bv e' = bv e) ==> e' = e` THEN
  UNDISCH_TAC `~((av:(real^N->bool)->real^N) e = bv e)` THEN
  UNDISCH_TAC `~(e':real^N->bool = e)` THEN
  UNDISCH_TAC `((x:real^N) = av(e:real^N->bool) /\ y = bv e) \/
               (x = bv e /\ y = av e)` THEN
  UNDISCH_TAC `(av:(real^N->bool)->real^N) e' = x \/
               (bv:(real^N->bool)->real^N) e' = x` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN MESON_TAC[]);;
(* Edges at one end of e other than e miss the dual cell of the other end, *)
(* and edges at different ends of e (other than e) are different.          *)

let MOI_S5A_OTHER_ENDS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> (!e'. e' IN moi_s5a_edges l av bv (av e) /\ ~(e' = e)
               ==> DISJOINT (derived_dual_cell t l (bv e))
                            (IMAGE (psi e') moi_s35_slab)) /\
         (!e'. e' IN moi_s5a_edges l av bv (bv e) /\ ~(e' = e)
               ==> DISJOINT (derived_dual_cell t l (av e))
                            (IMAGE (psi e') moi_s35_slab)) /\
         (!e' e''. e' IN moi_s5a_edges l av bv (av e) /\ ~(e' = e) /\
                   e'' IN moi_s5a_edges l av bv (bv e) /\ ~(e'' = e)
                   ==> DISJOINT (IMAGE (psi e') moi_s35_slab)
                                (IMAGE (psi e'') moi_s35_slab))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s5a_edges; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `{(av:(real^N->bool)->real^N) e} IN l /\ {(bv:(real^N->bool)->real^N) e} IN l`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `e':real^N->bool` THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`; `e':real^N->bool`;
      `(av:(real^N->bool)->real^N) e`; `(bv:(real^N->bool)->real^N) e`]
      MOI_S5A_ENDS_DISTINCT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC MOI_S5A_CELL_SLAB THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `kk:real^N->real^N->bool`] THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `e':real^N->bool` THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`; `e':real^N->bool`;
      `(bv:(real^N->bool)->real^N) e`; `(av:(real^N->bool)->real^N) e`]
      MOI_S5A_ENDS_DISTINCT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC MOI_S5A_CELL_SLAB THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `kk:real^N->real^N->bool`] THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`e':real^N->bool`; `e'':real^N->bool`] THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    MATCH_MP_TAC MOI_S5A_SLAB_DISJ THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `kk:real^N->real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `e:real^N->bool`; `e'':real^N->bool`;
      `(av:(real^N->bool)->real^N) e`; `(bv:(real^N->bool)->real^N) e`]
      MOI_S5A_ENDS_DISTINCT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]]]);;
(* Set algebra with atomic set variables (fast to use by MATCH_MP_TAC).    *)

let MOI_S5A_SUB_SPLIT = prove
 (`!c d s w q:real^N->bool.
     d SUBSET s UNION w /\ c SUBSET d UNION q
     ==> c SUBSET s UNION (c INTER (w UNION q))`,
  SET_TAC[]);;

let MOI_S5A_DISJ_SPLIT = prove
 (`!k a b x y c:real^N->bool.
     DISJOINT a x /\ DISJOINT a y /\ DISJOINT b x /\ DISJOINT b y /\
     c SUBSET x UNION y
     ==> DISJOINT (k INTER (a UNION b)) c`,
  SET_TAC[]);;

let MOI_S5A_DISJ_UNIONS_L = prove
 (`!(f:A->real^N->bool) P X.
     (!e. P e ==> DISJOINT (f e) X)
     ==> DISJOINT (UNIONS {f e | e | P e}) X`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; UNIONS_GSPEC;
              IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MOI_S5A_DISJ_UNIONS_R = prove
 (`!(f:A->real^N->bool) P X.
     (!e. P e ==> DISJOINT X (f e))
     ==> DISJOINT X (UNIONS {f e | e | P e})`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; UNIONS_GSPEC;
              IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MOI_S5A_INJ_IMAGE_DISJOINT = prove
 (`!(f:real^3->real^N) s a b.
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     a SUBSET s /\ b SUBSET s /\ DISJOINT a b
     ==> DISJOINT (IMAGE f a) (IMAGE f b)`,
  SET_TAC[]);;

let MOI_S5A_DISJ_SUBSET2 = prove
 (`!a b x y:real^N->bool.
     DISJOINT a b /\ x SUBSET a /\ y SUBSET b ==> DISJOINT x y`,
  SET_TAC[]);;
let MOI_S5A_CUBE_AFF_COMPACT = prove
 (`!a b c. compact {x:real^3 | x IN moi_s35_cube /\
                               a * moi_s35_n x + b * x$3 + c <= &0}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SET_RULE `{x:real^3 | x IN s /\ P x} = s INTER {x | P x}`] THEN
  MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
  REWRITE_TAC[MOI_S5A_MODEL_COMPACT; MOI_S5A_AFF_CLOSED_OPEN]);;

let MOI_S5A_KA = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?K. compact K /\ K SUBSET moi_s35_cplus t l av bv psi (av e) /\
             DISJOINT K (moi_s35_cplus t l av bv psi (bv e)) /\
             moi_s35_cplus t l av bv psi (av e) SUBSET
             IMAGE (psi e) moi_s35_slab UNION K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_CPLUS_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MOI_S5A_MODEL_TAC THEN
  ABBREV_TAC `low8 = {x:real^3 | x IN moi_s35_cube /\
                                 &0 * moi_s35_n x + &1 * x$3 + &1 / &8 <= &0}` THEN
  SUBGOAL_THEN `compact (low8:real^3->bool) /\ low8 SUBSET moi_s35_lower /\
                moi_s35_dom SUBSET moi_s35_slab UNION low8 /\
                DISJOINT low8 (moi_s35_bcell UNION moi_s35_upper)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "low8" THEN REWRITE_TAC[MOI_S5A_CUBE_AFF_COMPACT] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; DISJOINT; EXTENSION; IN_INTER;
                NOT_IN_EMPTY] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REPEAT CONJ_TAC THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `oth = UNIONS {IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                        moi_s35_slab | e' |
                  e' IN moi_s5a_edges l av bv (av e) /\ ~(e' = e)}` THEN
  ABBREV_TAC
   `othb = UNIONS {IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                         moi_s35_slab | e' |
                   e' IN moi_s5a_edges l av bv (bv e) /\ ~(e' = e)}` THEN
  SUBGOAL_THEN `compact (oth:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "oth" THEN MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `moi_s5a_edges l av bv ((av:(real^N->bool)->real^N) e)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5A_EDGES_FINITE THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^3`;
          `w:real^N->real^3->bool`; `psi:(real^N->bool)->real^3->real^N`;
          `kk:real^N->real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        SET_TAC[]];
      REWRITE_TAC[FORALL_IN_GSPEC; moi_s5a_edges; IN_ELIM_THM] THEN
      X_GEN_TAC `e':real^N->bool` THEN
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `e':real^N->bool`] MOI_S5A_EDGE_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_OTHER_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "oe1") (CONJUNCTS_THEN2
    (LABEL_TAC "oe2") (LABEL_TAC "oe3"))) THEN
  EXISTS_TAC `moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)
              INTER (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) low8 UNION
                     oth)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `(av:(real^N->bool)->real^N) e`] MOI_S5A_SOURCE_FACTS) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      MATCH_MP_TAC COMPACT_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `low8 SUBSET moi_s35_lower` THEN
      UNDISCH_TAC `moi_s35_lower SUBSET moi_s35_cube` THEN SET_TAC[]];
    REWRITE_TAC[INTER_SUBSET];
    MATCH_MP_TAC MOI_S5A_DISJ_SPLIT THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
             (moi_s35_bcell UNION moi_s35_upper)`; `othb:real^N->bool`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5A_INJ_IMAGE_DISJOINT THEN
      EXISTS_TAC `moi_s35_cube` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `low8 SUBSET moi_s35_lower` THEN
      UNDISCH_TAC `moi_s35_lower SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `moi_s35_upper SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `moi_s35_bcell SUBSET moi_s35_cube` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S5A_DISJ_SUBSET2 THEN
      MAP_EVERY EXISTS_TAC
       [`derived_dual_cell t l ((av:(real^N->bool)->real^N) e)`;
        `othb:real^N->bool`] THEN
      REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [EXPAND_TAC "othb" THEN
        MATCH_MP_TAC MOI_S5A_DISJ_UNIONS_R THEN
        X_GEN_TAC `e'':real^N->bool` THEN DISCH_TAC THEN
        USE_THEN "oe2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
          check (can (term_match []
            `IMAGE (f:real^3->real^N) moi_s35_lower = s`) o concl)) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC MOI_S5A_DISJ_SUBSET2 THEN
      MAP_EVERY EXISTS_TAC
       [`oth:real^N->bool`;
        `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab UNION
         derived_dual_cell t l ((bv:(real^N->bool)->real^N) e)`] THEN
      REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN REWRITE_TAC[DISJOINT_UNION] THEN
        ONCE_REWRITE_TAC[DISJOINT_SYM] THEN EXPAND_TAC "oth" THEN
        CONJ_TAC THEN MATCH_MP_TAC MOI_S5A_DISJ_UNIONS_L THEN
        X_GEN_TAC `e':real^N->bool` THEN DISCH_TAC THENL
         [MATCH_MP_TAC MOI_S5A_SLAB_DISJ THEN
          MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`;
            `l:(real^N->bool)->bool`; `h:real^N->real^3`;
            `w:real^N->real^3->bool`; `av:(real^N->bool)->real^N`;
            `bv:(real^N->bool)->real^N`; `kk:real^N->real^N->bool`] THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `e' IN moi_s5a_edges l av bv
                         ((av:(real^N->bool)->real^N) e) /\ ~(e' = e)` THEN
          SIMP_TAC[moi_s5a_edges; IN_ELIM_THM];
          ONCE_REWRITE_TAC[DISJOINT_SYM] THEN USE_THEN "oe1" MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]];
        UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                       moi_s35_upper = derived_dual_cell t l (bv e)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        UNDISCH_TAC `moi_s35_bcell INTER moi_s35_lower SUBSET moi_s35_slab` THEN
        UNDISCH_TAC `moi_s35_bcell SUBSET moi_s35_cube` THEN
        MP_TAC(last(CONJUNCTS MOI_S5A_MODEL_BASIC)) THEN SET_TAC[]];
      EXPAND_TAC "oth" THEN EXPAND_TAC "othb" THEN
      MATCH_MP_TAC MOI_S5A_DISJ_UNIONS_L THEN
      X_GEN_TAC `e':real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_S5A_DISJ_UNIONS_R THEN
      X_GEN_TAC `e'':real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "oe3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)
                   SUBSET IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                          (moi_s35_bcell UNION moi_s35_upper) UNION othb` THEN
      REWRITE_TAC[]];
    MATCH_MP_TAC MOI_S5A_SUB_SPLIT THEN
    EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_dom`
    THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)
                   SUBSET IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                   moi_s35_dom UNION oth` THEN REWRITE_TAC[]]]);;
let MOI_S5A_KB = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e u.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\ open u
     ==> ?K. compact K /\ K SUBSET moi_s35_cplus t l av bv psi (bv e) /\
             moi_s35_cplus t l av bv psi (bv e) SUBSET
             IMAGE (psi e) (u INTER moi_s35_cube) UNION K /\
             (!s. s SUBSET u INTER moi_s35_slab
                  ==> DISJOINT K (IMAGE (psi e) s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_CPLUS_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MOI_S5A_MODEL_TAC THEN
  ABBREV_TAC
   `othb = UNIONS {IMAGE ((psi:(real^N->bool)->real^3->real^N) e')
                         moi_s35_slab | e' |
                   e' IN moi_s5a_edges l av bv (bv e) /\ ~(e' = e)}` THEN
  SUBGOAL_THEN `compact (othb:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "othb" THEN MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `moi_s5a_edges l av bv ((bv:(real^N->bool)->real^N) e)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5A_EDGES_FINITE THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^3`;
          `w:real^N->real^3->bool`; `psi:(real^N->bool)->real^3->real^N`;
          `kk:real^N->real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        SET_TAC[]];
      REWRITE_TAC[FORALL_IN_GSPEC; moi_s5a_edges; IN_ELIM_THM] THEN
      X_GEN_TAC `e':real^N->bool` THEN
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `e':real^N->bool`] MOI_S5A_EDGE_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)
              INTER (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                       (moi_s35_cube DIFF u) UNION othb)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `(bv:(real^N->bool)->real^N) e`] MOI_S5A_SOURCE_FACTS) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      MATCH_MP_TAC COMPACT_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ASM_SIMP_TAC[COMPACT_DIFF; MOI_S5A_MODEL_COMPACT]]];
    REWRITE_TAC[INTER_SUBSET];
    SUBGOAL_THEN
     `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
            (moi_s35_bcell UNION moi_s35_upper) SUBSET
      IMAGE (psi e) (u INTER moi_s35_cube) UNION
      IMAGE (psi e) (moi_s35_cube DIFF u)`
    MP_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `moi_s35_bcell SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `moi_s35_upper SUBSET moi_s35_cube` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)
                 SUBSET IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                        (moi_s35_bcell UNION moi_s35_upper) UNION othb` THEN
    SPEC_TAC(`othb:real^N->bool`,`b2:real^N->bool`) THEN
    SPEC_TAC(`IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                    (moi_s35_bcell UNION moi_s35_upper)`,`b1:real^N->bool`) THEN
    SPEC_TAC(`IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                    (u INTER moi_s35_cube)`,`a1:real^N->bool`) THEN
    SPEC_TAC(`IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                    (moi_s35_cube DIFF u)`,`a2:real^N->bool`) THEN
    SPEC_TAC(`moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)`,
             `c:real^N->bool`) THEN
    SET_TAC[];
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5A_DISJ_SUBSET2 THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE ((psi:(real^N->bool)->real^3->real^N) e) (moi_s35_cube DIFF u)
       UNION othb`;
      `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) s`] THEN
    REWRITE_TAC[INTER_SUBSET; SUBSET_REFL] THEN
    REWRITE_TAC[DISJOINT_UNION] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5A_INJ_IMAGE_DISJOINT THEN
      EXISTS_TAC `moi_s35_cube` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s SUBSET (u:real^3->bool) INTER moi_s35_slab` THEN
      UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN SET_TAC[];
      EXPAND_TAC "othb" THEN MATCH_MP_TAC MOI_S5A_DISJ_UNIONS_L THEN
      X_GEN_TAC `e':real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_S5A_DISJ_SUBSET2 THEN
      MAP_EVERY EXISTS_TAC
       [`IMAGE ((psi:(real^N->bool)->real^3->real^N) e') moi_s35_slab`;
        `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab`] THEN
      REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5A_SLAB_DISJ THEN
        MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`;
          `l:(real^N->bool)->bool`; `h:real^N->real^3`;
          `w:real^N->real^3->bool`; `av:(real^N->bool)->real^N`;
          `bv:(real^N->bool)->real^N`; `kk:real^N->real^N->bool`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `e' IN moi_s5a_edges l av bv
                       ((bv:(real^N->bool)->real^N) e) /\ ~(e' = e)` THEN
        SIMP_TAC[moi_s5a_edges; IN_ELIM_THM];
        MATCH_MP_TAC IMAGE_SUBSET THEN
        UNDISCH_TAC `s SUBSET (u:real^3->bool) INTER moi_s35_slab` THEN
        SET_TAC[]]]]);;

(* ------------------------------------------------------------------ *)
(* Per-edge clause infrastructure: cell inclusions, model             *)
(* separation facts, source partitions, the band, the edge marker.    *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------- *)
(* 6. Edge clauses of the separation type (frame (2) and conditions (2),    *)
(* (4) of p.249): each holds once err(av e) + err(bv e) is small.           *)
(* ------------------------------------------------------------------------- *)

(* The pierced cells for admissible levels lie in the enlarged cells, and  *)
(* in the pierced cells for the top level 1/512.                             *)

let MOI_S5A_CSRC_IN = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v cc.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l /\
     (!e. abs(cc e) <= &1 / &512)
     ==> moi_s35_csrc t l av bv psi cc v SUBSET moi_s35_cplus t l av bv psi v /\
         moi_s35_csrc t l av bv psi cc v SUBSET
         moi_s35_csrc t l av bv psi (\e. &1 / &512) v`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `cc:(real^N->bool)->real` o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC MOI_S5A_CSRC_MONO THEN GEN_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool`) THEN REAL_ARITH_TAC]);;

let MOI_S5A_CMAX_FACTS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l
     ==> compact (moi_s35_csrc t l av bv psi (\e. &1 / &512) v) /\
         moi_s35_csrc t l av bv psi (\e. &1 / &512) v SUBSET
         moi_s35_cplus t l av bv psi v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `\e:real^N->bool. &1 / &512`)
    (MP_TAC o SPEC `\e:real^N->bool. &1 / &512` o last o CONJUNCTS)) THEN
  BETA_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SIMP_TAC[]);;

let MOI_S5A_C_F2C = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?d. &0 < d /\
             moi_s5a_good t l h av bv psi e d
              (\ff cc. IMAGE (ff (av e)) (moi_s35_csrc t l av bv psi cc (av e))
                       INTER IMAGE (ff (bv e)) (moi_s35_csrc t l av bv psi cc (bv e))
                       SUBSET IMAGE (moi_s35_ach ff av psi e) moi_s35_slab)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_KA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `(av:(real^N->bool)->real^N) e`; `(bv:(real^N->bool)->real^N) e`;
    `K:real^N->bool`;
    `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)`]
    MOI_S5A_EDGE_SEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `w:real^N->real^3->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
      `(bv:(real^N->bool)->real^N) e`] MOI_S5A_SOURCE_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ff:real^N->real^N->real^3`;
                                `err:real^N->real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`]
    MOI_S5A_CSRC_IN) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`(av:(real^N->bool)->real^N) e`; `cc:(real^N->bool)->real`]
           th) THEN
    MP_TAC(SPECL [`(bv:(real^N->bool)->real^N) e`; `cc:(real^N->bool)->real`]
           th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; moi_s35_ach; o_THM] THEN
  X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x1:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                moi_s35_slab` MP_TAC THENL
   [SUBGOAL_THEN `~((x1:real^N) IN K)` MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `DISJOINT (IMAGE ((ff:real^N->real^N->real^3) (av e)) K)
                            (IMAGE (ff (bv e)) (moi_s35_cplus t l av bv psi
                                                  ((bv:(real^N->bool)->real^N) e)))`
      THEN REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `x1:real^N` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `x2:real^N` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ASM SET_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S5A_EDGE_SEP_MODEL = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e s r.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\
     compact s /\ compact r /\ s SUBSET moi_s35_dom /\
     r SUBSET moi_s35_bcell UNION moi_s35_upper /\ DISJOINT s r
     ==> ?d. &0 < d /\
             !ff err. moi_s5a_apx t l av bv psi h ff err /\
                      err (av e) + err (bv e) <= d
                      ==> DISJOINT (IMAGE (moi_s35_ach ff av psi e) s)
                                   (IMAGE (moi_s35_bch ff bv psi e) r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_CPLUS_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MOI_S5A_MODEL_TAC THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET moi_s35_cube /\
                (r:real^3->bool) SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `s SUBSET moi_s35_dom` THEN
    UNDISCH_TAC `r SUBSET moi_s35_bcell UNION moi_s35_upper` THEN
    UNDISCH_TAC `moi_s35_dom SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `moi_s35_bcell SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `moi_s35_upper SUBSET moi_s35_cube` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `(av:(real^N->bool)->real^N) e`; `(bv:(real^N->bool)->real^N) e`;
    `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) s`;
    `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) r`] MOI_S5A_EDGE_SEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_dom`
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                        (moi_s35_bcell UNION moi_s35_upper)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
        REWRITE_TAC[IMAGE_UNION; UNION_SUBSET] THEN CONJ_TAC THEN
        FIRST_ASSUM ACCEPT_TAC];
      MATCH_MP_TAC MOI_S5A_INJ_IMAGE_DISJOINT THEN
      EXISTS_TAC `moi_s35_cube` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s35_ach; moi_s35_bch; IMAGE_o] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `err:real^N->real` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5A_MODEL_SEP_FACTS = prove
 (`DISJOINT moi_s35_stube (moi_s35_level (&1 / &8)) /\
   moi_s35_level (&1 / &8) SUBSET moi_s35_bcell UNION moi_s35_upper /\
   DISJOINT moi_s35_ttube
     (moi_s35_sq (&5 / &32) (--(&3) / &256) UNION
      moi_s35_sq (&11 / &32) (&3 / &256)) /\
   moi_s35_sq (&5 / &32) (--(&3) / &256) UNION
   moi_s35_sq (&11 / &32) (&3 / &256) SUBSET moi_s35_bcell UNION moi_s35_upper /\
   moi_s35_ttube SUBSET moi_s35_dom`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; SUBSET; IN_UNION] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REPEAT CONJ_TAC THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5A_C_F2D_E14 = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?d. &0 < d /\
             moi_s5a_good t l h av bv psi e d
              (\ff cc. DISJOINT (IMAGE (moi_s35_bch ff bv psi e)
                                       (moi_s35_level (&1 / &8)))
                                (IMAGE (moi_s35_ach ff av psi e) moi_s35_stube) /\
                       DISJOINT (IMAGE (moi_s35_bch ff bv psi e)
                                       (moi_s35_sq (&5 / &32) (--(&3) / &256))
                                 UNION
                                 IMAGE (moi_s35_bch ff bv psi e)
                                       (moi_s35_sq (&11 / &32) (&3 / &256)))
                                (IMAGE (moi_s35_ach ff av psi e) moi_s35_ttube))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_MODEL_SEP_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`; `moi_s35_stube`; `moi_s35_level (&1 / &8)`]
    MOI_S5A_EDGE_SEP_MODEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_S5A_MODEL_COMPACT; MOI_S5A_MODEL_BASIC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`; `moi_s35_ttube`;
    `moi_s35_sq (&5 / &32) (--(&3) / &256) UNION
     moi_s35_sq (&11 / &32) (&3 / &256)`] MOI_S5A_EDGE_SEP_MODEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
    MATCH_MP_TAC COMPACT_UNION THEN REWRITE_TAC[MOI_S5A_MODEL_COMPACT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
     check (can (term_match [] `!ff (err:real^N->real). P ff err ==> DISJOINT
       (IMAGE (moi_s35_ach ff (av:(real^N->bool)->real^N) psi e) moi_s35_stube)
       (Q ff)`) o concl)) THEN
    EXISTS_TAC `err:real^N->real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[DISJOINT_SYM] THEN REWRITE_TAC[GSYM IMAGE_UNION] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
     check (can (term_match [] `!ff (err:real^N->real). P ff err ==> DISJOINT
       (IMAGE (moi_s35_ach ff (av:(real^N->bool)->real^N) psi e) moi_s35_ttube)
       (Q ff)`) o concl)) THEN
    EXISTS_TAC `err:real^N->real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S5A_INJ_IMAGE_INTER = prove
 (`!(f:real^3->real^N) c s sl q k.
     (!x y. x IN c /\ y IN c /\ f x = f y ==> x = y) /\
     s SUBSET sl /\ sl SUBSET c /\ q SUBSET c /\ k INTER IMAGE f sl = IMAGE f q
     ==> k INTER IMAGE f s = IMAGE f (s INTER q)`,
  SET_TAC[]);;

(* The pierced cells for any admissible levels meet the chart image of a   *)
(* part s of the slab exactly in the expected model pieces.                 *)

let MOI_S5A_CSRC_PART = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e cc s.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\
     s SUBSET moi_s35_slab
     ==> moi_s35_csrc t l av bv psi cc (av e) INTER IMAGE (psi e) s =
         IMAGE (psi e) (s INTER {x | x IN moi_s35_slab /\ x$3 <= cc e}) /\
         moi_s35_csrc t l av bv psi cc (bv e) INTER IMAGE (psi e) s =
         IMAGE (psi e) (s INTER (moi_s35_bcell INTER moi_s35_slab))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`; `cc:(real^N->bool)->real`] MOI_S5A_CSRC_SLAB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(el 5 (CONJUNCTS th))) THEN
  SUBGOAL_THEN `moi_s35_slab SUBSET moi_s35_cube` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S5A_MODEL_BASIC]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_S5A_INJ_IMAGE_INTER THEN
  MAP_EVERY EXISTS_TAC [`moi_s35_cube`; `moi_s35_slab`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN SET_TAC[]);;

let moi_s5a_band = new_definition
 `moi_s5a_band = {x:real^3 | x IN moi_s35_cube /\
                             -- &1 * moi_s35_n x + &0 * x$3 + &5 / &16 <= &0 /\
                             &1 * moi_s35_n x + &0 * x$3 + -- &5 / &16 <= &0 /\
                             &0 * moi_s35_n x + &1 * x$3 + -- &1 / &512 <= &0 /\
                             &0 * moi_s35_n x + -- &1 * x$3 + -- &1 / &512 <= &0}`;;

let MOI_S5A_BAND_FACTS = prove
 (`compact moi_s5a_band /\ moi_s5a_band SUBSET moi_s35_slab /\
   moi_s5a_band SUBSET moi_s35_dom /\
   DISJOINT moi_s5a_band moi_s35_bcell /\
   (!c. abs c <= &1 / &512 ==> moi_s35_sq (&5 / &16) c SUBSET moi_s5a_band) /\
   DISJOINT (moi_s35_level (&1 / &8))
            {x:real^3 | x IN moi_s35_slab /\ x$3 <= &1 / &512}`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s5a_band; SET_RULE
     `{x:real^3 | x IN s /\ P x /\ Q x /\ R x /\ S x} =
      s INTER {x | P x} INTER {x | Q x} INTER {x | R x} INTER {x | S x}`] THEN
    REPEAT(MATCH_MP_TAC COMPACT_INTER_CLOSED THEN CONJ_TAC) THEN
    REWRITE_TAC[MOI_S5A_MODEL_COMPACT; MOI_S5A_AFF_CLOSED_OPEN] THEN
    REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[MOI_S5A_AFF_CLOSED_OPEN];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s5a_band; SUBSET; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
              NOT_IN_EMPTY] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REPEAT STRIP_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

let MOI_S5A_C_F2E_E17 = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?d. &0 < d /\
             moi_s5a_good t l h av bv psi e d
              (\ff cc. DISJOINT (IMAGE (moi_s35_bch ff bv psi e)
                                       (moi_s35_level (&1 / &8)))
                                (IMAGE (ff (av e))
                                   (moi_s35_csrc t l av bv psi cc (av e))) /\
                       DISJOINT (IMAGE (moi_s35_ach ff av psi e)
                                       (moi_s35_sq (&5 / &16) (cc e)))
                                (IMAGE (ff (bv e))
                                   (moi_s35_csrc t l av bv psi cc (bv e))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_BAND_FACTS THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_CPLUS_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MOI_S5A_MODEL_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`]
    MOI_S5A_CMAX_FACTS) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `(av:(real^N->bool)->real^N) e` th) THEN
                       MP_TAC(SPEC `(bv:(real^N->bool)->real^N) e` th)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. s SUBSET moi_s35_cube /\ compact s
        ==> compact (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `moi_s35_cube` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `(av:(real^N->bool)->real^N) e`; `(bv:(real^N->bool)->real^N) e`;
    `moi_s35_csrc t l av bv psi (\e:real^N->bool. &1 / &512)
                  ((av:(real^N->bool)->real^N) e)`;
    `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) (moi_s35_level (&1 / &8))`]
    MOI_S5A_EDGE_SEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper`
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN ASM SET_TAC[]; FIRST_ASSUM ACCEPT_TAC];
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `e:real^N->bool`; `\e:real^N->bool. &1 / &512`;
        `moi_s35_level (&1 / &8)`] MOI_S5A_CSRC_PART) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN BETA_TAC THEN
      UNDISCH_TAC `DISJOINT (moi_s35_level (&1 / &8))
                     {x:real^3 | x IN moi_s35_slab /\ x$3 <= &1 / &512}` THEN
      REWRITE_TAC[DISJOINT] THEN SIMP_TAC[IMAGE_CLAUSES]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `(av:(real^N->bool)->real^N) e`; `(bv:(real^N->bool)->real^N) e`;
    `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5a_band`;
    `moi_s35_csrc t l av bv psi (\e:real^N->bool. &1 / &512)
                  ((bv:(real^N->bool)->real^N) e)`]
    MOI_S5A_EDGE_SEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_dom`
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `e:real^N->bool`; `\e:real^N->bool. &1 / &512`;
        `moi_s5a_band`] MOI_S5A_CSRC_PART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      UNDISCH_TAC `DISJOINT moi_s5a_band moi_s35_bcell` THEN
      REWRITE_TAC[DISJOINT] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[SET_RULE
        `(s:real^3->bool) INTER (b INTER sl) = (s INTER b) INTER sl`; th]) THEN
      SIMP_TAC[INTER_EMPTY; IMAGE_CLAUSES]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`]
    MOI_S5A_CSRC_IN) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`(av:(real^N->bool)->real^N) e`; `cc:(real^N->bool)->real`]
           th) THEN
    MP_TAC(SPECL [`(bv:(real^N->bool)->real^N) e`; `cc:(real^N->bool)->real`]
           th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`ff:real^N->real^N->real^3`;
                                  `err:real^N->real`] o
      check (can (term_match []
        `!(ff:real^N->real^N->real^3) (err:real^N->real). P ff err ==>
           DISJOINT (IMAGE (ff ((av:(real^N->bool)->real^N) e))
                    (moi_s35_csrc t l av bv psi (\e. &1 / &512) (av e))) Q`) o
        concl)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[moi_s35_bch; IMAGE_o] THEN
    UNDISCH_TAC `moi_s35_csrc t l av bv psi cc ((av:(real^N->bool)->real^N) e)
                 SUBSET moi_s35_csrc t l av bv psi (\e. &1 / &512) (av e)` THEN
    SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`ff:real^N->real^N->real^3`;
                                  `err:real^N->real`] o
      check (can (term_match []
        `!(ff:real^N->real^N->real^3) (err:real^N->real). P ff err ==>
           DISJOINT (IMAGE (ff ((av:(real^N->bool)->real^N) e))
                    (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                     moi_s5a_band)) Q`) o concl)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[moi_s35_ach; IMAGE_o] THEN
    SUBGOAL_THEN `moi_s35_sq (&5 / &16) ((cc:(real^N->bool)->real) e) SUBSET
                  moi_s5a_band` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)
                 SUBSET moi_s35_csrc t l av bv psi (\e. &1 / &512) (bv e)` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. Marker clauses: chart boxes covered by the approximations.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S5A_DIM3 = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l ==> 3 <= dimindex(:N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
  ASM_REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  REWRITE_TAC[INT_OF_NUM_LE]);;

let MOI_S5A_EDGE_PLH = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?q. pl_homeomorphism (moi_s35_cube,IMAGE (psi e) moi_s35_cube) (psi e,q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk` THEN
  REWRITE_TAC[moi_s5a_ctx; moi_s35_charts] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT1 o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `q:real^N->real^3` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5A_CHART_IN_T = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> IMAGE (psi e) moi_s35_cube SUBSET UNIONS t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `(av:(real^N->bool)->real^N) e`] MOI_FTA_CELL_IN_STAR);
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `(bv:(real^N->bool)->real^N) e`] MOI_FTA_CELL_IN_STAR)] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_S5A_EDGE_MARKER = prove
 (mk_imp(MOI_S35_MARKER,
  `!t l (h:real^N->real^3) w av bv psi kk e (a:real^3) b (kb:real^3->bool) u s.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\
     (!i. 1 <= i /\ i <= 3 ==> a$i < b$i) /\
     interval[a,b] SUBSET moi_s35_cube /\
     compact kb /\ kb SUBSET interval(a,b) /\ open u /\ u SUBSET kb /\
     compact s /\ s SUBSET u
     ==> ?r. &0 < r /\
             !f y z. f continuous_on IMAGE (psi e) (interval[a,b]) /\
                     (!x y. x IN IMAGE (psi e) (interval[a,b]) /\
                            y IN IMAGE (psi e) (interval[a,b]) /\ f x = f y
                            ==> x = y) /\
                     (!x. x IN IMAGE (psi e) (interval[a,b]) ==> dist(f x,h x) < r) /\
                     z IN s /\ dist(y,h(psi e z)) < r
                     ==> y IN interior(IMAGE f (IMAGE (psi e) (interval[a,b])))`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_PLH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:real^N->real^3`) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
    `e:real^N->bool`] MOI_S5A_CHART_IN_T) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`(psi:(real^N->bool)->real^3->real^N) e`; `q:real^N->real^3`;
                 `a:real^3`; `b:real^3`; `kb:real^3->bool`; `u:real^3->bool`;
                 `s:real^3->bool`; `h:real^N->real^3`; `UNIONS t:real^N->bool`]
    (UNDISCH MOI_S5A_CHART_MARKER)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5A_DIM3 THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `(av:(real^N->bool)->real^N) e`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`moi_s35_cube`;
                            `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                   moi_s35_cube`] THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_INTERVAL];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_cube` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `z:real^3` THEN
    ASM_REWRITE_TAC[]]);;

(* Boxes of the model used with the marker lemma.                          *)

let MOI_S5A_BOX_TAC : tactic =
  REWRITE_TAC[SUBSET; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; IN_ELIM_THM;
              IN_INTER; IN_DIFF; DISJOINT; EXTENSION; NOT_IN_EMPTY] THEN
  REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REPEAT STRIP_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;;

let moi_s5a_us = new_definition
 `moi_s5a_us = {x:real^3 | -- &1 * moi_s35_n x + &0 * x$3 + &1 / &8 < &0 /\
                           &1 * moi_s35_n x + &0 * x$3 + -- &3 / &8 < &0 /\
                           &0 * moi_s35_n x + &1 * x$3 + -- &1 / &16 < &0 /\
                           &0 * moi_s35_n x + -- &1 * x$3 + -- &1 / &16 < &0}`;;

let MOI_S5A_US_FACTS = prove
 (`open moi_s5a_us /\ moi_s5a_us SUBSET interior moi_s35_stube /\
   moi_s35_bann SUBSET moi_s5a_us`,
  SUBGOAL_THEN `open moi_s5a_us` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5a_us; SET_RULE
     `{x:real^3 | P x /\ Q x /\ R x /\ S x} =
      {x | P x} INTER {x | Q x} INTER {x | R x} INTER {x | S x}`] THEN
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[MOI_S5A_AFF_CLOSED_OPEN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_s5a_us] THEN MOI_S5A_BOX_TAC;
    REWRITE_TAC[moi_s5a_us] THEN MOI_S5A_BOX_TAC]);;

let MOI_S5A_MARK_MODEL = prove
 (`interval[vector[-- &7 / &32; -- &7 / &32; -- &1 / &256]:real^3,
            vector[&7 / &32; &7 / &32; &1 / &16]]
     SUBSET moi_s35_bcell INTER moi_s35_slab /\
   interval[vector[-- &13 / &64; -- &13 / &64; -- &3 / &1024]:real^3,
            vector[&13 / &64; &13 / &64; &3 / &1024]] SUBSET
   interval(vector[-- &7 / &32; -- &7 / &32; -- &1 / &256],
            vector[&7 / &32; &7 / &32; &1 / &16]) /\
   interval[vector[-- &3 / &16; -- &3 / &16; -- &1 / &512]:real^3,
            vector[&3 / &16; &3 / &16; &1 / &512]] SUBSET
   interval(vector[-- &13 / &64; -- &13 / &64; -- &3 / &1024],
            vector[&13 / &64; &13 / &64; &3 / &1024]) /\
   interval[vector[-- &1 / &2; -- &1 / &2; -- &3 / &32]:real^3,
            vector[&1 / &2; &1 / &2; &3 / &32]] SUBSET moi_s35_dom /\
   interval[vector[-- &3 / &8; -- &3 / &8; -- &1 / &32]:real^3,
            vector[&3 / &8; &3 / &8; &1 / &32]] SUBSET
   interval(vector[-- &1 / &2; -- &1 / &2; -- &3 / &32],
            vector[&1 / &2; &1 / &2; &3 / &32]) /\
   moi_s35_bann SUBSET
   interval(vector[-- &3 / &8; -- &3 / &8; -- &1 / &32],
            vector[&3 / &8; &3 / &8; &1 / &32]) /\
   (!c. abs c <= &1 / &512
        ==> {x | x IN moi_s35_level c /\ moi_s35_n x <= &3 / &16} SUBSET
            interval[vector[-- &3 / &16; -- &3 / &16; -- &1 / &512]:real^3,
                     vector[&3 / &16; &3 / &16; &1 / &512]]) /\
   interval[vector[-- &3 / &16; -- &3 / &16; -- &1 / &512]:real^3,
            vector[&3 / &16; &3 / &16; &1 / &512]] SUBSET moi_s35_dom`,
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN TRY DISCH_TAC THEN MOI_S5A_BOX_TAC);;


(* ------------------------------------------------------------------ *)
(* Clause lemmas (3), (5), (6) of the edge configuration: the         *)
(* inner square, the annulus in the tube, the boundary of xa in xb.   *)
(* ------------------------------------------------------------------ *)

(* Context instantiation helper: the eight context variables in order.      *)

let moi_s5a_ctxl = [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
  `h:real^N->real^3`; `w:real^N->real^3->bool`;
  `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
  `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`];;

let moi_s5a_cs extra th = ISPECL (moi_s5a_ctxl @ extra) th;;

(* Invariance of domain, pointwise form.                                     *)

let MOI_S5A_IOD_INTERIOR = prove
 (`!(g:real^3->real^3) d u x z.
     g continuous_on d /\ (!x y. x IN d /\ y IN d /\ g x = g y ==> x = y) /\
     open u /\ u SUBSET d /\ z IN u /\ IMAGE g u SUBSET x
     ==> g z IN interior x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (g:real^3->real^3) u)` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `IMAGE (g:real^3->real^3) u`]
    INTERIOR_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Interior points of a PL 3-cell go to interior points of the image under  *)
(* any continuous injective map into real^3 (invariance of domain).         *)

let MOI_S5A_CELL_INT_INTERIOR = prove
 (`!(s:real^N->bool) bs (g:real^N->real^3) x.
     pl_cell_with_boundary 3 s bs /\ g continuous_on s /\
     (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\ x IN s /\ ~(x IN bs)
     ==> g x IN interior(IMAGE g s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S5A_CELL_DOWN o
    check (can (term_match [] `pl_cell_with_boundary 3 (s:real^N->bool) bs`) o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^N`
    (X_CHOOSE_THEN `q:real^N->real^3` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `pl_homeomorphism (S,s) ((p:real^3->real^N),(q:real^N->real^3))`
  THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `S:real^3->bool` MOI_STA_SIMPLEX_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?z:real^3. z IN interior S /\ x = (p:real^3->real^N) z`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^N) IN IMAGE (p:real^3->real^N) S` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
      `S DIFF relative_frontier S = interior (S:real^3->bool)`) o concl)) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x:real^N) IN bs)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
      `IMAGE (p:real^3->real^N) (relative_frontier S) = bs`) o concl)) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:real^N->real^3) ((p:real^3->real^N) z) =
                (g o p) z` SUBST1_TAC THENL [REWRITE_TAC[o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5A_IOD_INTERIOR THEN
  MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `interior S:real^3->bool`] THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR; INTERIOR_SUBSET] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^3->real^N) x' = p y` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y. x IN s /\ y IN s /\
                   (g:real^N->real^3) x = g y ==> x = y`) (concl th))) THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[]];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]);;

let MOI_S5A_APX_AT = prove
 (`!t l av bv psi (h:real^N->real^3) ff err v.
     moi_s5a_apx t l av bv psi h ff err /\ {v} IN l
     ==> pl_map_on (moi_s35_cplus t l av bv psi v) (ff v) /\
         (ff v) continuous_on (moi_s35_cplus t l av bv psi v) /\
         (!x y. x IN moi_s35_cplus t l av bv psi v /\
                y IN moi_s35_cplus t l av bv psi v /\ ff v x = ff v y ==> x = y) /\
         (!x. x IN moi_s35_cplus t l av bv psi v ==> dist(ff v x,h x) < err v)`,
  REWRITE_TAC[moi_s5a_apx] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON]);;

let MOI_S5A_IN3_TAC : tactic =
  GEN_TAC THEN REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 3 <=> i = 1 \/ i = 2 \/ i = 3`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3] THEN CONV_TAC REAL_RAT_REDUCE_CONV;;

(* (6) inner square: the level square n <= 3/16 near height 0 lies in the   *)
(* interior of xb (marker lemma for the B-side approximation on a box in    *)
(* bcell INTER slab).                                                        *)

let MOI_S5A_C_E16 = prove
 (mk_imp(MOI_S35_MARKER,
  `!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?d. &0 < d /\
             moi_s5a_good t l h av bv psi e d
              (\ff cc. !z. z IN moi_s35_cube /\ moi_s35_n z <= &3 / &16 /\
                           abs(z$3) <= &1 / &512
                           ==> moi_s35_ach ff av psi e z IN
                               interior (IMAGE (ff (bv e))
                                  (moi_s35_csrc t l av bv psi cc (bv e))))`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_MARK_MODEL THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`;
     `vector[-- &7 / &32; -- &7 / &32; -- &1 / &256]:real^3`;
     `vector[&7 / &32; &7 / &32; &1 / &16]:real^3`;
     `interval[vector[-- &13 / &64; -- &13 / &64; -- &3 / &1024]:real^3,
               vector[&13 / &64; &13 / &64; &3 / &1024]]`;
     `interval(vector[-- &13 / &64; -- &13 / &64; -- &3 / &1024]:real^3,
               vector[&13 / &64; &13 / &64; &3 / &1024])`;
     `interval[vector[-- &3 / &16; -- &3 / &16; -- &1 / &512]:real^3,
               vector[&3 / &16; &3 / &16; &1 / &512]]`]
    (MP MOI_S5A_EDGE_MARKER (ASSUME MOI_S35_MARKER))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL;
                    INTERVAL_OPEN_SUBSET_CLOSED] THEN
    CONJ_TAC THENL [MOI_S5A_IN3_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s35_bcell INTER moi_s35_slab` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s35_slab] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
    `ff:real^N->real^N->real^3`; `err:real^N->real`;
    `(bv:(real^N->bool)->real^N) e`] MOI_S5A_APX_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `(av:(real^N->bool)->real^N) e`] MOI_S5A_APX_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `(bv:(real^N->bool)->real^N) e`] MOI_S5A_APX_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
      (interval[vector[-- &7 / &32; -- &7 / &32; -- &1 / &256],
                vector[&7 / &32; &7 / &32; &1 / &16]]) SUBSET
    moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e) /\
    IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
      (interval[vector[-- &7 / &32; -- &7 / &32; -- &1 / &256],
                vector[&7 / &32; &7 / &32; &1 / &16]]) SUBSET
    moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_bcell`
      THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP (SET_RULE
        `!s a b:real^3->bool. s SUBSET a INTER b ==> s SUBSET a`));
      MP_TAC(moi_s5a_cs [`e:real^N->bool`; `cc:(real^N->bool)->real`;
        `interval[vector[-- &7 / &32; -- &7 / &32; -- &1 / &256]:real^3,
                  vector[&7 / &32; &7 / &32; &1 / &16]]`] MOI_S5A_CSRC_PART) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        FIRST_ASSUM(ACCEPT_TAC o MATCH_MP (SET_RULE
          `!s a b:real^3->bool. s SUBSET a INTER b ==> s SUBSET b`));
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      SUBGOAL_THEN
       `interval[vector[-- &7 / &32; -- &7 / &32; -- &1 / &256]:real^3,
                 vector[&7 / &32; &7 / &32; &1 / &16]] INTER
        (moi_s35_bcell INTER moi_s35_slab) =
        interval[vector[-- &7 / &32; -- &7 / &32; -- &1 / &256],
                 vector[&7 / &32; &7 / &32; &1 / &16]]` SUBST1_TAC THENL
       [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP (SET_RULE
          `!s a b:real^3->bool. s SUBSET a INTER b ==> s INTER a INTER b = s`));
        SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s t. (x:real^3) IN s /\ s SUBSET t ==> x IN t`) THEN
  EXISTS_TAC
   `interior (IMAGE ((ff:real^N->real^N->real^3) (bv e))
      (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
         (interval[vector[-- &7 / &32; -- &7 / &32; -- &1 / &256],
                   vector[&7 / &32; &7 / &32; &1 / &16]])))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `z:real^3` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC(SET_RULE
       `!(f:real^N->real^3) s u.
          (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\ s SUBSET u
          ==> (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`) THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `!a b. &0 < a /\ a + b <= r /\ x < b ==> x < r`) THEN
      MAP_EVERY EXISTS_TAC
       [`(err:real^N->real) ((av:(real^N->bool)->real^N) e)`;
        `(err:real^N->real) ((bv:(real^N->bool)->real^N) e)`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(z:real^3) IN moi_s35_cube` THEN
      UNDISCH_TAC `moi_s35_n z <= &3 / &16` THEN
      UNDISCH_TAC `abs((z:real^3)$3) <= &1 / &512` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
      REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `(z:real^3) IN moi_s35_dom` ASSUME_TAC THENL
       [REWRITE_TAC[moi_s35_dom; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (can (term_match []
        `!x. x IN moi_s35_dom ==> dist(moi_s35_ach ff av psi e x,
                                        (h:real^N->real^3)(psi e x)) < err (av e)`)
        o concl)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S5A_INJ_SUBSET = prove
 (`!(f:A->B) s t.
     (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y) /\ s SUBSET t
     ==> (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)`,
  SET_TAC[]);;

(* (5) first half: the B-annulus lies in the A-image of the open tube us   *)
(* (marker lemma for the A-side approximation on a box around the tube,    *)
(* then model separation of the rest of the box from bann).                 *)

let MOI_S5A_C_E13 = prove
 (mk_imp(MOI_S35_MARKER,
  `!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?d. &0 < d /\
             moi_s5a_good t l h av bv psi e d
              (\ff cc. IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann SUBSET
                       IMAGE (moi_s35_ach ff av psi e) moi_s5a_us)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_MARK_MODEL THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_US_FACTS THEN STRIP_TAC THEN
  MOI_S5A_MODEL_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`;
     `vector[-- &1 / &2; -- &1 / &2; -- &3 / &32]:real^3`;
     `vector[&1 / &2; &1 / &2; &3 / &32]:real^3`;
     `interval[vector[-- &3 / &8; -- &3 / &8; -- &1 / &32]:real^3,
               vector[&3 / &8; &3 / &8; &1 / &32]]`;
     `interval(vector[-- &3 / &8; -- &3 / &8; -- &1 / &32]:real^3,
               vector[&3 / &8; &3 / &8; &1 / &32])`;
     `moi_s35_bann`]
    (MP MOI_S5A_EDGE_MARKER (ASSUME MOI_S35_MARKER))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL; MOI_S5A_MODEL_COMPACT;
                    INTERVAL_OPEN_SUBSET_CLOSED] THEN
    CONJ_TAC THENL [MOI_S5A_IN3_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s35_dom` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`;
     `interval[vector[-- &1 / &2; -- &1 / &2; -- &3 / &32]:real^3,
               vector[&1 / &2; &1 / &2; &3 / &32]] DIFF moi_s5a_us`;
     `moi_s35_bann`] MOI_S5A_EDGE_SEP_MODEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_DIFF THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
      UNDISCH_TAC `interval[vector[-- &1 / &2; -- &1 / &2; -- &3 / &32]:real^3,
                            vector[&1 / &2; &1 / &2; &3 / &32]] SUBSET moi_s35_dom`
      THEN SET_TAC[];
      UNDISCH_TAC `moi_s35_bann SUBSET moi_s35_bcell INTER moi_s35_slab` THEN
      SET_TAC[];
      UNDISCH_TAC `moi_s35_bann SUBSET moi_s5a_us` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "sep2"))) THEN
  EXISTS_TAC `min r d2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
    `ff:real^N->real^N->real^3`; `err:real^N->real`;
    `(av:(real^N->bool)->real^N) e`] MOI_S5A_APX_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `(av:(real^N->bool)->real^N) e`] MOI_S5A_APX_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `(bv:(real^N->bool)->real^N) e`] MOI_S5A_APX_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "sep2" (MP_TAC o SPECL [`ff:real^N->real^N->real^3`;
                                     `err:real^N->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
      (interval[vector[-- &1 / &2; -- &1 / &2; -- &3 / &32],
                vector[&1 / &2; &1 / &2; &3 / &32]]) SUBSET
    moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_dom`
    THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `moi_s35_bch ff bv psi e z IN
    interior (IMAGE ((ff:real^N->real^N->real^3) (av e))
      (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
         (interval[vector[-- &1 / &2; -- &1 / &2; -- &3 / &32],
                   vector[&1 / &2; &1 / &2; &3 / &32]])))`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `z:real^3` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `dist((ff:real^N->real^N->real^3) (av e) x,(h:real^N->real^3) x) <
                    (err:real^N->real) ((av:(real^N->bool)->real^N) e)` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
          `!x. x IN moi_s35_cplus t l av bv psi (av e)
               ==> dist((ff:real^N->real^N->real^3) (av e) x,h x) < err (av e)`)
          o concl)) THEN
        MP_TAC(ASSUME `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
          (interval[vector[-- &1 / &2; -- &1 / &2; -- &3 / &32],
                    vector[&1 / &2; &1 / &2; &3 / &32]]) SUBSET
          moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)`) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `(err:real^N->real) ((av:(real^N->bool)->real^N) e) +
                     err ((bv:(real^N->bool)->real^N) e) <= min r d2` THEN
        UNDISCH_TAC `&0 < (err:real^N->real) ((bv:(real^N->bool)->real^N) e)` THEN
        REAL_ARITH_TAC];
      FIRST_ASSUM ACCEPT_TAC;
      SUBGOAL_THEN `(z:real^3) IN moi_s35_bcell UNION moi_s35_upper`
      ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN moi_s35_bann` THEN
        UNDISCH_TAC `moi_s35_bann SUBSET moi_s35_bcell INTER moi_s35_slab` THEN
        SET_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (can (term_match []
        `!x. x IN moi_s35_bcell UNION moi_s35_upper
             ==> dist(moi_s35_bch ff bv psi e x,
                      (h:real^N->real^3)(psi e x)) < err (bv e)`)
        o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(err:real^N->real) ((av:(real^N->bool)->real^N) e) +
                   err ((bv:(real^N->bool)->real^N) e) <= min r d2` THEN
      UNDISCH_TAC `&0 < (err:real^N->real) ((av:(real^N->bool)->real^N) e)` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET] INTERIOR_SUBSET)) THEN
  REWRITE_TAC[GSYM IMAGE_o; GSYM moi_s35_ach] THEN
  SUBGOAL_THEN `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z IN
                IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann` MP_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SPEC_TAC(`moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z`,`y:real^3`) THEN
  UNDISCH_TAC `DISJOINT
    (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
      (interval[vector[-- &1 / &2; -- &1 / &2; -- &3 / &32],
                vector[&1 / &2; &1 / &2; &3 / &32]] DIFF moi_s5a_us))
    (IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann)` THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_DIFF; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

(* Model sets for (3): the far part of the slab (below -1/16, or outside    *)
(* the square n < 5/16 below the levels) misses bcell; the open box below   *)
(* the level c.                                                             *)

let moi_s5a_zfar = new_definition
 `moi_s5a_zfar =
    {x:real^3 | x IN moi_s35_slab /\
                (x$3 <= -- &1 / &16 \/
                 (x$3 <= &1 / &512 /\ &5 / &16 <= moi_s35_n x))}`;;

let moi_s5a_ob = new_definition
 `moi_s5a_ob c =
    {x:real^3 | moi_s35_n x < &1 / &2 /\ -- &1 / &8 < x$3 /\ x$3 < c}`;;

let MOI_S5A_ZFAR_FACTS = prove
 (`compact moi_s5a_zfar /\ moi_s5a_zfar SUBSET moi_s35_slab /\
   DISJOINT moi_s5a_zfar moi_s35_bcell`,
  let cube = [`&1`,`&0`,`-- &1`; `&0`,`&1`,`-- &1`; `&0`,`-- &1`,`-- &1`] in
  let slab = cube @ [`&0`,`&1`,`-- &1 / &8`; `&0`,`-- &1`,`-- &1 / &8`] in
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      REWRITE_TAC[moi_s35_cube; BOUNDED_INTERVAL] THEN
      REWRITE_TAC[SUBSET; moi_s5a_zfar; moi_s35_slab; IN_ELIM_THM;
                  moi_s35_cube] THEN
      SIMP_TAC[];
      SUBGOAL_THEN
       `moi_s5a_zfar =
        {x:real^3 | x IN moi_s35_slab /\ x$3 <= -- &1 / &16} UNION
        {x:real^3 | x IN moi_s35_slab /\ x$3 <= &1 / &512 /\
                    &5 / &16 <= moi_s35_n x}`
      SUBST1_TAC THENL
       [REWRITE_TAC[moi_s5a_zfar; EXTENSION; IN_UNION; IN_ELIM_THM] THEN
        GEN_TAC THEN CONV_TAC TAUT;
        MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
         [MOI_S5A_AFF_CLOSED_TAC (slab @ [`&0`,`&1`,`&1 / &16`]);
          MOI_S5A_AFF_CLOSED_TAC
            (slab @ [`&0`,`&1`,`-- &1 / &512`; `-- &1`,`&0`,`&5 / &16`])]]];
    REWRITE_TAC[SUBSET; moi_s5a_zfar; IN_ELIM_THM] THEN SIMP_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; moi_s5a_zfar;
                IN_ELIM_THM] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC]);;

let MOI_S5A_OB_FACTS = prove
 (`!c. abs c <= &1 / &512
       ==> open (moi_s5a_ob c) /\ moi_s5a_ob c SUBSET moi_s35_dom /\
           moi_s5a_ob c SUBSET {x | x IN moi_s35_slab /\ x$3 <= c} /\
           (!z. z IN moi_s35_slab /\ z$3 < c /\ ~(z IN moi_s5a_zfar)
                ==> z IN moi_s5a_ob c)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `moi_s5a_ob c =
      {x:real^3 | &1 * moi_s35_n x + &0 * x$3 + -- &1 / &2 < &0} INTER
      {x:real^3 | &0 * moi_s35_n x + -- &1 * x$3 + -- &1 / &8 < &0} INTER
      {x:real^3 | &0 * moi_s35_n x + &1 * x$3 + --c < &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_s5a_ob; EXTENSION; IN_INTER; IN_ELIM_THM] THEN
      GEN_TAC THEN REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[MOI_S5A_AFF_CLOSED_OPEN]];
    REWRITE_TAC[SUBSET; moi_s5a_ob; IN_ELIM_THM] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; moi_s5a_ob; IN_ELIM_THM] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_s5a_ob; moi_s5a_zfar; IN_ELIM_THM] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]);;

let MOI_S5A_XX_FACTS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk ff err cc v.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s5a_apx t l av bv psi h ff err /\
     {v} IN l /\ (!e. abs(cc e) <= &1 / &512)
     ==> compact (IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v)) /\
         frontier (IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v)) SUBSET
         IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
    `ff:real^N->real^N->real^3`; `err:real^N->real`;
    `v:real^N`] MOI_S5A_APX_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (IMAGE ((ff:real^N->real^N->real^3) v)
                           (moi_s35_csrc t l av bv psi cc v))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `moi_s35_cplus t l av bv (psi:(real^N->bool)->real^3->real^N) v` THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED]]);;

let MOI_S5A_IN_IMAGE_MONO = prove
 (`!(f:A->B) s t y. y IN IMAGE f s /\ s SUBSET t ==> y IN IMAGE f t`,
  SET_TAC[]);;

(* (3): the boundary of xa meets xb only in the flat part of the level.    *)

let MOI_S5A_C_E9 = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?d. &0 < d /\
             moi_s5a_good t l h av bv psi e d
              (\ff cc. frontier (IMAGE (ff (av e))
                                   (moi_s35_csrc t l av bv psi cc (av e))) INTER
                       IMAGE (ff (bv e)) (moi_s35_csrc t l av bv psi cc (bv e))
                       SUBSET IMAGE (moi_s35_ach ff av psi e)
                                {x | x IN moi_s35_level (cc e) /\
                                     moi_s35_n x < &5 / &16})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_ZFAR_FACTS THEN STRIP_TAC THEN
  MOI_S5A_MODEL_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`(bv:(real^N->bool)->real^N) e`] MOI_S5A_CMAX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_C_F2C) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "g0"))) THEN
  MP_TAC(moi_s5a_cs [`(av:(real^N->bool)->real^N) e`;
     `(bv:(real^N->bool)->real^N) e`;
     `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5a_zfar`;
     `moi_s35_csrc t l av bv psi (\e:real^N->bool. &1 / &512)
                   ((bv:(real^N->bool)->real^N) e)`]
     MOI_S5A_EDGE_SEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_s5a_zfar SUBSET moi_s35_slab` THEN
      UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab`
      THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
      MP_TAC(moi_s5a_cs [`e:real^N->bool`; `\e:real^N->bool. &1 / &512`;
                         `moi_s5a_zfar`] MOI_S5A_CSRC_PART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      UNDISCH_TAC `DISJOINT moi_s5a_zfar moi_s35_bcell` THEN
      REWRITE_TAC[DISJOINT] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[SET_RULE
        `(s:real^3->bool) INTER (b INTER sl) = (s INTER b) INTER sl`; th]) THEN
      SIMP_TAC[INTER_EMPTY; IMAGE_CLAUSES]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "s1"))) THEN
  EXISTS_TAC `min d0 d1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "g0" (MP_TAC o SPECL [`ff:real^N->real^N->real^3`;
    `err:real^N->real`; `cc:(real^N->bool)->real`] o
    REWRITE_RULE[moi_s5a_good]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  REMOVE_THEN "s1" (MP_TAC o SPECL [`ff:real^N->real^N->real^3`;
                                    `err:real^N->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(moi_s5a_cs [] MOI_S5A_CSRC_IN) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`(av:(real^N->bool)->real^N) e`; `cc:(real^N->bool)->real`]
           th) THEN
    MP_TAC(SPECL [`(bv:(real^N->bool)->real^N) e`; `cc:(real^N->bool)->real`]
           th)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
     `cc:(real^N->bool)->real`; `(av:(real^N->bool)->real^N) e`]
     MOI_S5A_XX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
    `ff:real^N->real^N->real^3`; `err:real^N->real`;
    `(av:(real^N->bool)->real^N) e`] MOI_S5A_APX_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`; `cc:(real^N->bool)->real`;
                     `moi_s35_slab`] MOI_S5A_CSRC_PART) THEN
  REWRITE_TAC[SUBSET_REFL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE ((ff:real^N->real^N->real^3) (av e))
                  (moi_s35_csrc t l av bv psi cc (av e))` ASSUME_TAC THENL
   [MP_TAC(ASSUME `frontier (IMAGE ((ff:real^N->real^N->real^3) (av e))
                     (moi_s35_csrc t l av bv psi cc (av e))) SUBSET
                    IMAGE (ff (av e)) (moi_s35_csrc t l av bv psi cc (av e))`) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^3. z IN moi_s35_slab /\ y = moi_s35_ach (ff:real^N->real^N->real^3) av psi e z`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE ((ff:real^N->real^N->real^3) (av e))
                   (moi_s35_csrc t l av bv psi cc (av e)) INTER
                 IMAGE (ff (bv e)) (moi_s35_csrc t l av bv psi cc (bv e)) SUBSET
                 IMAGE (moi_s35_ach ff av psi e) moi_s35_slab` THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((psi:(real^N->bool)->real^3->real^N) e z) IN
                moi_s35_csrc t l av bv psi cc ((av:(real^N->bool)->real^N) e)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN IMAGE ((ff:real^N->real^N->real^3) (av e))
                  (moi_s35_csrc t l av bv psi cc (av e))` THEN
    ASM_REWRITE_TAC[IN_IMAGE; moi_s35_ach; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e z = p`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN moi_s35_cplus t l av bv psi (av e) /\
             y IN moi_s35_cplus t l av bv psi (av e) /\
             (ff:real^N->real^N->real^3) (av e) x = ff (av e) y ==> x = y`)
      o concl)) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab
                     SUBSET moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)`)
      THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ASSUME `moi_s35_csrc t l av bv psi cc ((av:(real^N->bool)->real^N) e)
                     SUBSET moi_s35_cplus t l av bv psi (av e)`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3)$3 <= cc (e:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `((psi:(real^N->bool)->real^3->real^N) e z) IN
       IMAGE (psi e) (moi_s35_slab INTER
                      {x | x IN moi_s35_slab /\ x$3 <= cc e})` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
        `moi_s35_csrc t l av bv psi cc (av e) INTER
         IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab = s`)
        o concl)) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `z':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z:real^3 = z'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
             (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`)
      o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `(z:real^3) IN moi_s35_slab` THEN
    UNDISCH_TAC `(z':real^3) IN moi_s35_slab` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((z:real^3) IN moi_s5a_zfar)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `DISJOINT (IMAGE ((ff:real^N->real^N->real^3) (av e))
                     (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s5a_zfar))
                   (IMAGE (ff (bv e))
                     (moi_s35_csrc t l av bv psi (\e. &1 / &512) (bv e)))` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[moi_s35_ach; o_THM] THEN
      REPEAT(MATCH_MP_TAC FUN_IN_IMAGE) THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC MOI_S5A_IN_IMAGE_MONO THEN
      EXISTS_TAC `moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)`
      THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3)$3 = cc (e:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPEC `(cc:(real^N->bool)->real) e` MOI_S5A_OB_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN moi_s5a_ob ((cc:(real^N->bool)->real) e)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
        `!z. z IN moi_s35_slab /\ z$3 < c /\ ~(z IN moi_s5a_zfar)
             ==> z IN moi_s5a_ob c`) o concl)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN interior (IMAGE ((ff:real^N->real^N->real^3) (av e))
                     (moi_s35_csrc t l av bv psi cc (av e)))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5A_IOD_INTERIOR THEN
      MAP_EVERY EXISTS_TAC [`moi_s35_dom`; `moi_s5a_ob ((cc:(real^N->bool)->real) e)`] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; moi_s35_ach; o_THM] THEN
      X_GEN_TAC `o1:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      SUBGOAL_THEN `((psi:(real^N->bool)->real^3->real^N) e o1) IN
         IMAGE (psi e) (moi_s35_slab INTER {x | x IN moi_s35_slab /\ x$3 <= cc e})`
      MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `moi_s5a_ob ((cc:(real^N->bool)->real) e) SUBSET
                     {x | x IN moi_s35_slab /\ x$3 <= cc e}` THEN
        UNDISCH_TAC `(o1:real^3) IN moi_s5a_ob ((cc:(real^N->bool)->real) e)` THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
          `moi_s35_csrc t l av bv psi cc (av e) INTER
           IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab = s`)
          o concl)) THEN
        SIMP_TAC[IN_INTER]];
      UNDISCH_TAC `(y:real^3) IN frontier (IMAGE ((ff:real^N->real^N->real^3) (av e))
                     (moi_s35_csrc t l av bv psi cc (av e)))` THEN
      REWRITE_TAC[frontier; IN_DIFF] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `z:real^3` THEN
  ASM_REWRITE_TAC[moi_s35_level; IN_ELIM_THM] THEN CONJ_TAC THENL
   [UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `(z:real^3) IN moi_s35_slab` THEN SET_TAC[];
    UNDISCH_TAC `~((z:real^3) IN moi_s5a_zfar)` THEN
    ASM_REWRITE_TAC[moi_s5a_zfar; IN_ELIM_THM] THEN
    UNDISCH_TAC `!e:real^N->bool. abs(cc e) <= &1 / &512` THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^N->bool`) THEN
    UNDISCH_TAC `(z:real^3)$3 = cc (e:real^N->bool)` THEN REAL_ARITH_TAC]);;

(* Model sets for (5) second half: the open ring u15 around the tube and its *)
(* part strictly above the bcell surface.                                    *)

let moi_s5a_u15 = new_definition
 `moi_s5a_u15 =
    {x:real^3 | -- &1 * moi_s35_n x + &0 * x$3 + &5 / &32 < &0 /\
                &1 * moi_s35_n x + &0 * x$3 + -- &11 / &32 < &0 /\
                &0 * moi_s35_n x + &1 * x$3 + -- &1 / &16 < &0 /\
                &0 * moi_s35_n x + -- &1 * x$3 + -- &1 / &16 < &0}`;;

let moi_s5a_ob15 = new_definition
 `moi_s5a_ob15 =
    {x:real^3 | x IN moi_s5a_u15 /\
                &1 / &8 * moi_s35_n x + -- &1 * x$3 + -- &1 / &32 < &0}`;;

let MOI_S5A_U15_FACTS = prove
 (`open moi_s5a_u15 /\ open moi_s5a_ob15 /\
   moi_s35_ttube SUBSET moi_s5a_u15 INTER moi_s35_slab /\
   moi_s5a_ob15 SUBSET moi_s35_bcell INTER moi_s35_slab /\
   moi_s5a_u15 INTER moi_s35_cube SUBSET moi_s35_slab /\
   (!z. z IN moi_s5a_u15 /\ z IN moi_s35_bcell /\ ~(z IN moi_s5a_ob15)
        ==> z IN moi_s35_bann)`,
  SUBGOAL_THEN `open moi_s5a_u15` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s5a_u15; SET_RULE
     `{x:real^3 | P x /\ Q x /\ R x /\ S x} =
      {x | P x} INTER {x | Q x} INTER {x | R x} INTER {x | S x}`] THEN
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[MOI_S5A_AFF_CLOSED_OPEN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s5a_ob15; SET_RULE
     `{x:real^3 | x IN s /\ P x} = s INTER {x | P x}`] THEN
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[MOI_S5A_AFF_CLOSED_OPEN];
    REWRITE_TAC[moi_s5a_u15; SUBSET; IN_INTER; IN_ELIM_THM] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_s5a_u15; moi_s5a_ob15; SUBSET; IN_INTER; IN_ELIM_THM] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_s5a_u15; SUBSET; IN_INTER; IN_ELIM_THM] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[moi_s5a_u15; moi_s5a_ob15; IN_ELIM_THM] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC]);;

(* (5) second half: the boundary of xb meets the A-image of the thin tube    *)
(* only in the B-annulus.                                                    *)

let MOI_S5A_C_E15 = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?d. &0 < d /\
             moi_s5a_good t l h av bv psi e d
              (\ff cc. frontier (IMAGE (ff (bv e))
                                   (moi_s35_csrc t l av bv psi cc (bv e))) INTER
                       IMAGE (moi_s35_ach ff av psi e) moi_s35_ttube
                       SUBSET IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_U15_FACTS THEN STRIP_TAC THEN
  MOI_S5A_MODEL_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`; `moi_s5a_u15`] MOI_S5A_KB) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(moi_s5a_cs [`(av:(real^N->bool)->real^N) e`;
     `(bv:(real^N->bool)->real^N) e`;
     `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_ttube`;
     `K:real^N->bool`] MOI_S5A_EDGE_SEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_cube` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_s35_ttube SUBSET moi_s35_stube` THEN
      UNDISCH_TAC `moi_s35_stube SUBSET moi_s35_slab` THEN
      UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_dom`
      THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `moi_s35_ttube SUBSET moi_s35_stube` THEN
      UNDISCH_TAC `moi_s35_stube SUBSET moi_s35_dom` THEN SET_TAC[];
      ONCE_REWRITE_TAC[DISJOINT_SYM] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
        `!s. s SUBSET moi_s5a_u15 INTER moi_s35_slab
             ==> DISJOINT K (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) s)`)
        o concl)) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "s1"))) THEN
  EXISTS_TAC `d1:real` THEN ASM_REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "s1" (MP_TAC o SPECL [`ff:real^N->real^N->real^3`;
                                    `err:real^N->real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(moi_s5a_cs [`(bv:(real^N->bool)->real^N) e`; `cc:(real^N->bool)->real`]
    MOI_S5A_CSRC_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
     `cc:(real^N->bool)->real`; `(bv:(real^N->bool)->real^N) e`]
     MOI_S5A_XX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
    `ff:real^N->real^N->real^3`; `err:real^N->real`;
    `(bv:(real^N->bool)->real^N) e`] MOI_S5A_APX_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`; `cc:(real^N->bool)->real`;
                     `moi_s35_slab`] MOI_S5A_CSRC_PART) THEN
  REWRITE_TAC[SUBSET_REFL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE ((ff:real^N->real^N->real^3) (bv e))
                  (moi_s35_csrc t l av bv psi cc (bv e))` MP_TAC THENL
   [MP_TAC(ASSUME `frontier (IMAGE ((ff:real^N->real^N->real^3) (bv e))
                     (moi_s35_csrc t l av bv psi cc (bv e))) SUBSET
                    IMAGE (ff (bv e)) (moi_s35_csrc t l av bv psi cc (bv e))`) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(y:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_ttube` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((q:real^N) IN K)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `DISJOINT (IMAGE ((ff:real^N->real^N->real^3) (av e))
                     (IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_ttube))
                   (IMAGE (ff (bv e)) K)` THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `y = moi_s35_ach (ff:real^N->real^N->real^3) av psi e z` THEN
      REWRITE_TAC[moi_s35_ach; o_THM] THEN DISCH_THEN SUBST1_TAC THEN
      REPEAT(MATCH_MP_TAC FUN_IN_IMAGE) THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z':real^3. z' IN moi_s5a_u15 /\ z' IN moi_s35_cube /\
                            q = (psi:(real^N->bool)->real^3->real^N) e z'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(q:real^N) IN moi_s35_cplus t l av bv psi
                    ((bv:(real^N->bool)->real^N) e)` MP_TAC THENL
     [MP_TAC(ASSUME `moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)
                     SUBSET moi_s35_cplus t l av bv psi (bv e)`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ASSUME `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)
                   SUBSET IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                            (moi_s5a_u15 INTER moi_s35_cube) UNION K`) THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `q:real^N`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z':real^3) IN moi_s35_slab` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5a_u15 INTER moi_s35_cube SUBSET moi_s35_slab` THEN
    UNDISCH_TAC `(z':real^3) IN moi_s5a_u15` THEN
    UNDISCH_TAC `(z':real^3) IN moi_s35_cube` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z':real^3) IN moi_s35_bcell` ASSUME_TAC THENL
   [SUBGOAL_THEN `(q:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
       (moi_s35_slab INTER (moi_s35_bcell INTER moi_s35_slab))` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
        `moi_s35_csrc t l av bv psi cc (bv e) INTER
         IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab = s`)
        o concl)) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z'':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z':real^3 = z''` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
             (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`)
      o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN
    UNDISCH_TAC `(z'':real^3) IN moi_s35_slab` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((z':real^3) IN moi_s5a_ob15)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN interior (IMAGE ((ff:real^N->real^N->real^3) (bv e))
                     (moi_s35_csrc t l av bv psi cc (bv e)))` MP_TAC THENL
     [SUBGOAL_THEN `y = moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z'` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[moi_s35_bch; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_S5A_IOD_INTERIOR THEN
      MAP_EVERY EXISTS_TAC [`moi_s35_bcell UNION moi_s35_upper`; `moi_s5a_ob15`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `moi_s5a_ob15 SUBSET moi_s35_bcell INTER moi_s35_slab` THEN
        SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; moi_s35_bch; o_THM] THEN
      X_GEN_TAC `o1:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      SUBGOAL_THEN `((psi:(real^N->bool)->real^3->real^N) e o1) IN
         IMAGE (psi e) (moi_s35_slab INTER (moi_s35_bcell INTER moi_s35_slab))`
      MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `moi_s5a_ob15 SUBSET moi_s35_bcell INTER moi_s35_slab` THEN
        UNDISCH_TAC `(o1:real^3) IN moi_s5a_ob15` THEN SET_TAC[];
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
          `moi_s35_csrc t l av bv psi cc (bv e) INTER
           IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab = s`)
          o concl)) THEN
        SIMP_TAC[IN_INTER]];
      UNDISCH_TAC `(y:real^3) IN frontier (IMAGE ((ff:real^N->real^N->real^3) (bv e))
                     (moi_s35_csrc t l av bv psi cc (bv e)))` THEN
      REWRITE_TAC[frontier; IN_DIFF] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z':real^3` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[moi_s35_bch; o_THM];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!z. z IN moi_s5a_u15 /\ z IN moi_s35_bcell /\ ~(z IN moi_s5a_ob15)
           ==> z IN moi_s35_bann`) o concl)) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S5A_DOWN = prove
 (`!z:real^3 m.
     (z - m % basis 3)$1 = z$1 /\ (z - m % basis 3)$2 = z$2 /\
     (z - m % basis 3)$3 = z$3 - m /\ dist(z - m % basis 3,z) = abs m`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `(z - m % b) - z:real^3 = --(m % b)`;
              NORM_NEG; NORM_MUL] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

(* (5) the B-annulus lies on the boundary of xb: its points bound the source *)
(* cell (points just below are outside, seen through h), and boundary points *)
(* of a cell are not interior points of any injective image.                 *)

let MOI_S5A_C_E12 = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e ff err cc.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e /\
     moi_s5a_apx t l av bv psi h ff err /\ (!e. abs(cc e) <= &1 / &512)
     ==> IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann SUBSET
         frontier (IMAGE (ff (bv e)) (moi_s35_csrc t l av bv psi cc (bv e)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MOI_S5A_MODEL_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`(bv:(real^N->bool)->real^N) e`] MOI_S5A_SOURCE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `cc:(real^N->bool)->real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `bs:real^N->bool`)) THEN
  MP_TAC(moi_s5a_cs [`(bv:(real^N->bool)->real^N) e`] MOI_S5A_CPLUS_UNIONS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
    `ff:real^N->real^N->real^3`; `err:real^N->real`;
    `(bv:(real^N->bool)->real^N) e`] MOI_S5A_APX_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`; `cc:(real^N->bool)->real`;
                     `moi_s35_slab`] MOI_S5A_CSRC_PART) THEN
  REWRITE_TAC[SUBSET_REFL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)
                SUBSET UNIONS t` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN moi_s35_bcell /\ z IN moi_s35_slab`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_bann SUBSET moi_s35_bcell INTER moi_s35_slab` THEN
    UNDISCH_TAC `(z:real^3) IN moi_s35_bann` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e z IN
                moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e z IN
       IMAGE (psi e) (moi_s35_slab INTER (moi_s35_bcell INTER moi_s35_slab))`
    MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
      `moi_s35_csrc t l av bv psi cc (bv e) INTER
       IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab = s`)
      o concl)) THEN
    SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e z IN bs` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)`;
      `bs:real^N->bool`; `h:real^N->real^3`;
      `(psi:(real^N->bool)->real^3->real^N) e z`] MOI_S5A_CELL_INT_INTERIOR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool`
        THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool`
        THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `interior (IMAGE (h:real^N->real^3)
         (moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)))`
      OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN
    DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^3) ((psi:(real^N->bool)->real^3->real^N) e z)`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `eps:real` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `((h:real^N->real^3) o (psi:(real^N->bool)->real^3->real^N) e)
                 continuous_on moi_s35_cube` THEN
    REWRITE_TAC[continuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `(z:real^3) IN moi_s35_slab` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `eps:real`) THEN ASM_REWRITE_TAC[o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `m = min (del / &2) (&1 / &64)` THEN
    SUBGOAL_THEN `&0 < m /\ m < del /\ m <= &1 / &64` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `z' = (z:real^3) - m % basis 3` THEN
    MP_TAC(ISPECL [`z:real^3`; `m:real`] MOI_S5A_DOWN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z':real^3) IN moi_s35_slab /\ ~(z' IN moi_s35_bcell)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN moi_s35_bann` THEN
      REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN
      ASM_REWRITE_TAC[moi_s35_bann; IN_ELIM_THM] THEN
      UNDISCH_TAC `&0 < m` THEN UNDISCH_TAC `m <= &1 / &64` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z':real^3) IN moi_s35_cube` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN
      UNDISCH_TAC `(z':real^3) IN moi_s35_slab` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist((h:real^N->real^3) ((psi:(real^N->bool)->real^3->real^N) e z'),
                       h (psi e z)) < eps` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < m` THEN UNDISCH_TAC `m < del` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^3) ((psi:(real^N->bool)->real^3->real^N) e z') IN
                  IMAGE h (moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e))`
    MP_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN
      MP_TAC(ASSUME `ball((h:real^N->real^3) ((psi:(real^N->bool)->real^3->real^N) e z),eps)
         SUBSET interior (IMAGE h (moi_s35_csrc t l av bv psi cc
                                     ((bv:(real^N->bool)->real^N) e)))`) THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e z' = q` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
        `!x y. x IN UNIONS t /\ y IN UNIONS t /\
               (h:real^N->real^3) x = h y ==> x = y`) o concl)) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `z':real^3` o check (can (term_match []
          `!x. x IN moi_s35_slab
               ==> (psi:(real^N->bool)->real^3->real^N) e x IN UNIONS t /\
                   (h:real^N->real^3) (psi e x) IN
                     (w:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e) /\
                   h (psi e x) IN w ((bv:(real^N->bool)->real^N) e)`)
          o concl)) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
        MP_TAC(ASSUME `moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)
                       SUBSET UNIONS t`) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(psi:(real^N->bool)->real^3->real^N) e z' IN
       IMAGE (psi e) (moi_s35_slab INTER (moi_s35_bcell INTER moi_s35_slab))`
    MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (can (term_match []
        `moi_s35_csrc t l av bv psi cc (bv e) INTER
         IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab = s`)
        o concl)) THEN
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z'':real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `z':real^3 = z''` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
        `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
               (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`)
        o concl)) THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `moi_s35_slab SUBSET moi_s35_cube` THEN
        UNDISCH_TAC `(z'':real^3) IN moi_s35_slab` THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      UNDISCH_TAC `~((z'':real^3) IN moi_s35_bcell)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[frontier; IN_DIFF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    REWRITE_TAC[moi_s35_bch; o_THM] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[moi_s35_bch; o_THM] THEN
    MATCH_MP_TAC MOI_S5A_CELL_BD_NOT_INTERIOR THEN
    EXISTS_TAC `bs:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN
      EXISTS_TAC `moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)` THEN
      ASM_REWRITE_TAC[]]]);;


(* ------------------------------------------------------------------ *)
(* The orientation clause (2) of the frame.                           *)
(* ------------------------------------------------------------------ *)

(* Orientation clause infrastructure: bcell is convex, a sign rule, and the  *)
(* model boxes (an open box B0 in dom INTER bcell, a marker box inside it).  *)

let MOI_S5A_BCELL_CONVEX = prove
 (`convex moi_s35_bcell`,
  SUBGOAL_THEN
   `moi_s35_bcell =
    interval[--vec 1,vec 1] INTER
    {x:real^3 | vector[&1; &0; -- &8] dot x <= &1 / &4} INTER
    {x:real^3 | vector[-- &1; &0; -- &8] dot x <= &1 / &4} INTER
    {x:real^3 | vector[&0; &1; -- &8] dot x <= &1 / &4} INTER
    {x:real^3 | vector[&0; -- &1; -- &8] dot x <= &1 / &4}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; DOT_3; VECTOR_3] THEN
    REWRITE_TAC[GSYM moi_s35_cube] THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN GEN_TAC THEN REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_INTERVAL; CONVEX_HALFSPACE_LE]]);;

let MOI_S5A_SIGN3 = prove
 (`!a b c d. &0 < a * b /\ &0 < b * c /\ &0 < c * d ==> &0 < a * d`,
  REWRITE_TAC[REAL_MUL_POS_LT] THEN REAL_ARITH_TAC);;

let MOI_S5A_ORIENT_MODEL = prove
 (`interval[vector[-- &1 / &8; -- &1 / &8; &0],
            vector[&1 / &8; &1 / &8; &1 / &16]] SUBSET moi_s35_dom /\
   interval[vector[-- &1 / &8; -- &1 / &8; &0],
            vector[&1 / &8; &1 / &8; &1 / &16]] SUBSET moi_s35_bcell /\
   interval(vector[-- &1 / &8; -- &1 / &8; &0]:real^3,
            vector[&1 / &8; &1 / &8; &1 / &16]) SUBSET interior moi_s35_dom /\
   interval(vector[-- &1 / &8; -- &1 / &8; &0]:real^3,
            vector[&1 / &8; &1 / &8; &1 / &16]) SUBSET interior moi_s35_bcell /\
   ~(interval(vector[-- &1 / &8; -- &1 / &8; &0]:real^3,
              vector[&1 / &8; &1 / &8; &1 / &16]) = {}) /\
   interval[vector[-- &1 / &16; -- &1 / &16; &1 / &128]:real^3,
            vector[&1 / &16; &1 / &16; &1 / &32]] SUBSET
   interval(vector[-- &1 / &8; -- &1 / &8; &0],
            vector[&1 / &8; &1 / &8; &1 / &16]) /\
   interval[vector[-- &1 / &32; -- &1 / &32; &1 / &64]:real^3,
            vector[&1 / &32; &1 / &32; &3 / &128]] SUBSET
   interval(vector[-- &1 / &16; -- &1 / &16; &1 / &128],
            vector[&1 / &16; &1 / &16; &1 / &32]) /\
   vector[&0; &0; &5 / &256] IN
   interval(vector[-- &1 / &32; -- &1 / &32; &1 / &64]:real^3,
            vector[&1 / &32; &1 / &32; &3 / &128]) /\
   interval[vector[-- &1 / &16; -- &1 / &16; &1 / &128]:real^3,
            vector[&1 / &16; &1 / &16; &1 / &32]] SUBSET moi_s35_cube`,
  SUBGOAL_THEN
   `interval[vector[-- &1 / &8; -- &1 / &8; &0],
             vector[&1 / &8; &1 / &8; &1 / &16]] SUBSET moi_s35_dom /\
    interval[vector[-- &1 / &8; -- &1 / &8; &0],
             vector[&1 / &8; &1 / &8; &1 / &16]] SUBSET moi_s35_bcell`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MOI_S5A_BOX_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior(interval[vector[-- &1 / &8; -- &1 / &8; &0]:real^3,
                                  vector[&1 / &8; &1 / &8; &1 / &16]])` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; SUBSET_REFL];
      MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior(interval[vector[-- &1 / &8; -- &1 / &8; &0]:real^3,
                                  vector[&1 / &8; &1 / &8; &1 / &16]])` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; SUBSET_REFL];
      MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    MOI_S5A_BOX_TAC;
    MOI_S5A_BOX_TAC;
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    MOI_S5A_BOX_TAC]);;

(* (2) orientation: the A- and B-charts have the same sign of determinant    *)
(* wherever they are locally affine (CLOSE_SIGN on the open box B0, where    *)
(* both approximate h o psi e and the A-image covers a ball by the marker    *)
(* lemma; LOCAL_SIGN on the connected open sets interior dom and interior    *)
(* bcell).                                                                    *)

let MOI_S5A_C_F2B = prove
 (mk_imp(list_mk_conj[MOI_S35_MARKER; MOI_S35_LOCAL_SIGN; MOI_S35_CLOSE_SIGN],
  `!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?d. &0 < d /\
             moi_s5a_good t l h av bv psi e d
              (\ff cc. moi_s35_same_orient (moi_s35_ach ff av psi e)
                                           (interior moi_s35_dom)
                                           (moi_s35_bch ff bv psi e)
                                           (interior moi_s35_bcell))`),
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ls") (LABEL_TAC "cs"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_ORIENT_MODEL THEN STRIP_TAC THEN
  MOI_S5A_MODEL_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`;
     `vector[-- &1 / &16; -- &1 / &16; &1 / &128]:real^3`;
     `vector[&1 / &16; &1 / &16; &1 / &32]:real^3`;
     `interval[vector[-- &1 / &32; -- &1 / &32; &1 / &64]:real^3,
               vector[&1 / &32; &1 / &32; &3 / &128]]`;
     `interval(vector[-- &1 / &32; -- &1 / &32; &1 / &64]:real^3,
               vector[&1 / &32; &1 / &32; &3 / &128])`;
     `{vector[&0; &0; &5 / &256]:real^3}`]
    (MP MOI_S5A_EDGE_MARKER (ASSUME MOI_S35_MARKER))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL; COMPACT_SING; SING_SUBSET;
                    INTERVAL_OPEN_SUBSET_CLOSED] THEN
    MOI_S5A_IN3_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rm:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "mk"))) THEN
  EXISTS_TAC `rm / &4` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `(av:(real^N->bool)->real^N) e`] MOI_S5A_APX_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `(bv:(real^N->bool)->real^N) e`] MOI_S5A_APX_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
    `ff:real^N->real^N->real^3`; `err:real^N->real`;
    `(av:(real^N->bool)->real^N) e`] MOI_S5A_APX_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `r = (err:real^N->real) ((av:(real^N->bool)->real^N) e) +
                  err ((bv:(real^N->bool)->real^N) e)` THEN
  SUBGOAL_THEN `&0 < r /\ &3 * r < rm /\
                (err:real^N->real) ((av:(real^N->bool)->real^N) e) < rm`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `r <= rm / &4` THEN EXPAND_TAC "r" THEN
    UNDISCH_TAC `&0 < (err:real^N->real) ((av:(real^N->bool)->real^N) e)` THEN
    UNDISCH_TAC `&0 < (err:real^N->real) ((bv:(real^N->bool)->real^N) e)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
      (interval[vector[-- &1 / &16; -- &1 / &16; &1 / &128],
                vector[&1 / &16; &1 / &16; &1 / &32]]) SUBSET
    moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_dom`
    THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MAP_EVERY UNDISCH_TAC
     [`interval[vector[-- &1 / &16; -- &1 / &16; &1 / &128]:real^3,
                vector[&1 / &16; &1 / &16; &1 / &32]] SUBSET
       interval(vector[-- &1 / &8; -- &1 / &8; &0],
                vector[&1 / &8; &1 / &8; &1 / &16])`;
      `interval[vector[-- &1 / &8; -- &1 / &8; &0]:real^3,
                vector[&1 / &8; &1 / &8; &1 / &16]] SUBSET moi_s35_dom`] THEN
    MP_TAC(ISPECL [`vector[-- &1 / &8; -- &1 / &8; &0]:real^3`;
                   `vector[&1 / &8; &1 / &8; &1 / &16]:real^3`]
      INTERVAL_OPEN_SUBSET_CLOSED) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cball((h:real^N->real^3)((psi:(real^N->bool)->real^3->real^N) e
                                (vector[&0; &0; &5 / &256])),&3 * r) SUBSET
    IMAGE (moi_s35_ach ff av psi e)
      (interval(vector[-- &1 / &8; -- &1 / &8; &0],
                vector[&1 / &8; &1 / &8; &1 / &16]))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(y:real^3) IN interior (IMAGE ((ff:real^N->real^N->real^3) (av e))
        (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
           (interval[vector[-- &1 / &16; -- &1 / &16; &1 / &128],
                     vector[&1 / &16; &1 / &16; &1 / &32]])))`
    MP_TAC THENL
     [REMOVE_THEN "mk" MATCH_MP_TAC THEN
      EXISTS_TAC `vector[&0; &0; &5 / &256]:real^3` THEN
      REWRITE_TAC[IN_SING] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)`
        THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN
        EXISTS_TAC `moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)`
        THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LT_TRANS THEN
        EXISTS_TAC `(err:real^N->real) ((av:(real^N->bool)->real^N) e)` THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
          `!x. x IN moi_s35_cplus t l av bv psi (av e)
               ==> dist((ff:real^N->real^N->real^3) (av e) x,h x) < err (av e)`)
          o concl)) THEN
        MP_TAC(ASSUME `IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
          (interval[vector[-- &1 / &16; -- &1 / &16; &1 / &128],
                    vector[&1 / &16; &1 / &16; &1 / &32]]) SUBSET
          moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)`) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC;
        ONCE_REWRITE_TAC[DIST_SYM] THEN
        UNDISCH_TAC `dist((h:real^N->real^3)((psi:(real^N->bool)->real^3->real^N) e
                       (vector[&0; &0; &5 / &256])),y) <= &3 * r` THEN
        UNDISCH_TAC `&3 * r < rm` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET] INTERIOR_SUBSET)) THEN
    REWRITE_TAC[GSYM IMAGE_o; GSYM moi_s35_ach] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5A_IN_IMAGE_MONO THEN
    EXISTS_TAC `interval[vector[-- &1 / &16; -- &1 / &16; &1 / &128]:real^3,
                         vector[&1 / &16; &1 / &16; &1 / &32]]` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `B0 = interval(vector[-- &1 / &8; -- &1 / &8; &0]:real^3,
                            vector[&1 / &8; &1 / &8; &1 / &16])` THEN
  ABBREV_TAC `B0c = interval[vector[-- &1 / &8; -- &1 / &8; &0]:real^3,
                             vector[&1 / &8; &1 / &8; &1 / &16]]` THEN
  SUBGOAL_THEN `open (B0:real^3->bool) /\ connected B0 /\ B0 SUBSET B0c /\
                polytope (B0c:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B0"; "B0c"] THEN
    SIMP_TAC[OPEN_INTERVAL; CONVEX_CONNECTED; CONVEX_INTERVAL;
             INTERVAL_OPEN_SUBSET_CLOSED; POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B0:real^3->bool) SUBSET moi_s35_dom /\
                B0 SUBSET moi_s35_bcell UNION moi_s35_upper /\
                B0c SUBSET moi_s35_bcell UNION moi_s35_upper`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(B0:real^3->bool) SUBSET B0c`; `(B0c:real^3->bool) SUBSET moi_s35_dom`;
      `(B0c:real^3->bool) SUBSET moi_s35_bcell`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "cs" (MP_TAC o ISPECL
    [`moi_s35_ach (ff:real^N->real^N->real^3) av psi e`;
     `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e`;
     `B0:real^3->bool`;
     `(h:real^N->real^3)((psi:(real^N->bool)->real^3->real^N) e
                            (vector[&0; &0; &5 / &256]))`;
     `r:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_bcell UNION moi_s35_upper` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN
      EXISTS_TAC `moi_s35_bcell UNION moi_s35_upper` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN moi_s35_dom /\
                    x IN moi_s35_bcell UNION moi_s35_upper` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(B0:real^3->bool) SUBSET moi_s35_dom`;
          `(B0:real^3->bool) SUBSET moi_s35_bcell UNION moi_s35_upper`;
          `(x:real^3) IN B0`] THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH
       `!c e1 e2. dist(a:real^3,c) < e1 /\ dist(b,c) < e2 /\ e1 + e2 = r
                  ==> dist(a,b) < r`) THEN
      EXISTS_TAC `(h:real^N->real^3)((psi:(real^N->bool)->real^3->real^N) e x)` THEN
      EXISTS_TAC `(err:real^N->real) ((av:(real^N->bool)->real^N) e)` THEN
      EXISTS_TAC `(err:real^N->real) ((bv:(real^N->bool)->real^N) e)` THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN(LABEL_TAC "so0")] THEN
  MP_TAC(ISPECL [`moi_s35_ach (ff:real^N->real^N->real^3) av psi e`;
                 `B0c:real^3->bool`; `B0:real^3->bool`]
    MOI_S5A_PL_LIN_AT_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!s. s SUBSET moi_s35_dom /\ locally_polyhedral s
           ==> pl_map_on s (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)`)
      o concl)) THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE];
    DISCH_THEN(X_CHOOSE_THEN `x0:real^3` (X_CHOOSE_THEN `m0:real^3->real^3`
      STRIP_ASSUME_TAC))] THEN
  MP_TAC(ISPECL [`moi_s35_bch (ff:real^N->real^N->real^3) bv psi e`;
                 `B0c:real^3->bool`; `B0:real^3->bool`]
    MOI_S5A_PL_LIN_AT_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!s. s SUBSET moi_s35_bcell UNION moi_s35_upper /\ locally_polyhedral s
           ==> pl_map_on s (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)`)
      o concl)) THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE];
    DISCH_THEN(X_CHOOSE_THEN `y0:real^3` (X_CHOOSE_THEN `m0':real^3->real^3`
      STRIP_ASSUME_TAC))] THEN
  SUBGOAL_THEN `open (interior moi_s35_dom) /\ connected (interior moi_s35_dom) /\
                open (interior moi_s35_bcell) /\
                connected (interior moi_s35_bcell)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_INTERIOR] THEN CONJ_TAC THEN
    MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTERIOR THEN
    REWRITE_TAC[MOI_S5A_BCELL_CONVEX; MOI_S5A_DOM_INTERVAL; CONVEX_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_same_orient] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `m:real^3->real^3`;
                       `m':real^3->real^3`] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S5A_SIGN3 THEN
  EXISTS_TAC `det(matrix(m0:real^3->real^3))` THEN
  EXISTS_TAC `det(matrix(m0':real^3->real^3))` THEN REPEAT CONJ_TAC THENL
   [USE_THEN "ls" (MP_TAC o ISPECL
      [`moi_s35_ach (ff:real^N->real^N->real^3) av psi e`;
       `interior moi_s35_dom`; `x:real^3`; `x0:real^3`;
       `m:real^3->real^3`; `m0:real^3->real^3`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET];
      MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[INTERIOR_SUBSET];
      MAP_EVERY UNDISCH_TAC
       [`(B0:real^3->bool) SUBSET interior moi_s35_dom`; `(x0:real^3) IN B0`]
      THEN SET_TAC[]];
    USE_THEN "so0" (MP_TAC o REWRITE_RULE[moi_s35_same_orient]) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x0:real^3`; `y0:real^3`] THEN ASM_REWRITE_TAC[];
    USE_THEN "ls" (MP_TAC o ISPECL
      [`moi_s35_bch (ff:real^N->real^N->real^3) bv psi e`;
       `interior moi_s35_bcell`; `y0:real^3`; `y:real^3`;
       `m0':real^3->real^3`; `m':real^3->real^3`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_bcell UNION moi_s35_upper` THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `moi_s35_bcell` INTERIOR_SUBSET) THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN
      EXISTS_TAC `moi_s35_bcell UNION moi_s35_upper` THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `moi_s35_bcell` INTERIOR_SUBSET) THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(B0:real^3->bool) SUBSET interior moi_s35_bcell`; `(y0:real^3) IN B0`]
      THEN SET_TAC[]]]);;


(* ------------------------------------------------------------------ *)
(* The preimage circle set: connected rings of bann, components       *)
(* off the thin tube (7), and the map Phi close to the identity.      *)
(* ------------------------------------------------------------------ *)

(* Rings of the B-annulus are connected: a flat square annulus is a union of *)
(* four boxes, and the graph map onto the bcell surface is continuous.       *)

let MOI_S5A_FLAT_RING_CONNECTED = prove
 (`!r1 r2. &0 < r1 /\ r1 <= r2
           ==> connected {x:real^3 | r1 <= moi_s35_n x /\ moi_s35_n x <= r2 /\
                                     x$3 = &0}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x:real^3 | r1 <= moi_s35_n x /\ moi_s35_n x <= r2 /\ x$3 = &0} =
    ((interval[vector[r1; --r2; &0],vector[r2; r2; &0]] UNION
      interval[vector[--r2; r1; &0],vector[r2; r2; &0]]) UNION
     interval[vector[--r2; --r2; &0],vector[--r1; r2; &0]]) UNION
    interval[vector[--r2; --r2; &0],vector[r2; --r1; &0]]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL; IN_ELIM_THM; DIMINDEX_3;
                FORALL_3; VECTOR_3; moi_s35_n] THEN
    X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[REAL_MAX_LE; REAL_LE_MAX; REAL_ABS_BOUNDS;
                REAL_ARITH `r <= abs a <=> r <= a \/ a <= --r`;
                REAL_ARITH `&0 <= c /\ c <= &0 <=> c = &0`] THEN
    SUBGOAL_THEN `(r1 <= (x:real^3)$1 ==> --r2 <= x$1) /\
                  (x$1 <= --r1 ==> x$1 <= r2) /\
                  (r1 <= x$2 ==> --r2 <= x$2) /\
                  (x$2 <= --r1 ==> x$2 <= r2)` MP_TAC THENL
     [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      CONV_TAC TAUT];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC) THEN
  SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERVAL] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THENL
   [EXISTS_TAC `vector[r2; r2; &0]:real^3`;
    EXISTS_TAC `vector[--r2; r2; &0]:real^3`;
    EXISTS_TAC `vector[--r2; --r2; &0]:real^3`] THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let MOI_S5A_GRAPH_CONT = prove
 (`(\x:real^3. x + ((moi_s35_n x - &1 / &4) / &8 - x$3) % basis 3)
   continuous_on (:real^3)`,
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN X_GEN_TAC `x:real^3` THEN
  DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`&1 / &8`; `-- &1`; `-- &1 / &32`; `x:real^3`]
    MOI_S5A_AFF_CONT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let MOI_S5A_RING_CONNECTED = prove
 (`!r1 r2. &5 / &32 <= r1 /\ r1 <= r2 /\ r2 <= &11 / &32
           ==> connected {z | z IN moi_s35_bann /\ r1 <= moi_s35_n z /\
                              moi_s35_n z <= r2}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{z | z IN moi_s35_bann /\ r1 <= moi_s35_n z /\ moi_s35_n z <= r2} =
    IMAGE (\x:real^3. x + ((moi_s35_n x - &1 / &4) / &8 - x$3) % basis 3)
          {x:real^3 | r1 <= moi_s35_n x /\ moi_s35_n x <= r2 /\ x$3 = &0}`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `!x:real^3 s. (x + s % basis 3)$1 = x$1 /\ (x + s % basis 3)$2 = x$2 /\
                   (x + s % basis 3)$3 = x$3 + s`
    ASSUME_TAC THENL
     [SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
               DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; moi_s35_bann] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `(z:real^3) - z$3 % basis 3` THEN
      REWRITE_TAC[VECTOR_ARITH `z - s % b:real^3 = z + --s % b`] THEN
      ASM_REWRITE_TAC[moi_s35_n] THEN
      UNDISCH_TAC `z$3 = (moi_s35_n z - &1 / &4) / &8` THEN
      REWRITE_TAC[moi_s35_n] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
      UNDISCH_TAC `r1 <= moi_s35_n z` THEN UNDISCH_TAC `moi_s35_n z <= r2` THEN
      REWRITE_TAC[moi_s35_n] THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[moi_s35_n] THEN
      UNDISCH_TAC `r1 <= moi_s35_n x` THEN UNDISCH_TAC `moi_s35_n x <= r2` THEN
      UNDISCH_TAC `(x:real^3)$3 = &0` THEN
      UNDISCH_TAC `&5 / &32 <= r1` THEN UNDISCH_TAC `r1 <= r2` THEN
      UNDISCH_TAC `r2 <= &11 / &32` THEN
      REWRITE_TAC[moi_s35_n] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[MOI_S5A_GRAPH_CONT; SUBSET_UNIV];
      MATCH_MP_TAC MOI_S5A_FLAT_RING_CONNECTED THEN
      UNDISCH_TAC `&5 / &32 <= r1` THEN UNDISCH_TAC `r1 <= r2` THEN
      REAL_ARITH_TAC]]);;

let MOI_S5A_DIST_COMPONENTS = prove
 (`!x z:real^3 d. dist(x,z) < d
                  ==> abs(x$1 - z$1) < d /\ abs(x$2 - z$2) < d /\
                      abs(x$3 - z$3) < d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`x - z:real^3`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`x - z:real^3`; `2`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`x - z:real^3`; `3`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

let MOI_S5A_COMP_GENERIC = prove
 (`!s r (z0:real^3) t.
     connected r /\ z0 IN r /\ r SUBSET s /\
     (!x. x IN s /\ ~(x IN r) ==> x IN t)
     ==> ?k0. k0 IN components s /\
              !k. k IN components s /\ ~(k = k0) ==> k SUBSET t`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `connected_component s (z0:real^3)` THEN
  SUBGOAL_THEN `(z0:real^3) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `z0:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^3->bool) SUBSET connected_component s z0` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) INTER connected_component s z0 = {}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `k:real^3->bool`;
                   `connected_component s (z0:real^3)`] COMPONENTS_NONOVERLAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `z0:real^3` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  ASM SET_TAC[]);;

(* The lower half of the preimage circle set: one component carries the  *)
(* inner end ring of the annulus, all others lie in the thin tube.         *)
let SPDR12_MAX_ABS_LIP = prove
 (`!a b x y e. abs(a - x) < e /\ abs(b - y) < e
               ==> max (abs a) (abs b) < max (abs x) (abs y) + e /\
                   max (abs x) (abs y) < max (abs a) (abs b) + e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[REAL_MAX_LT] THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S5A_COMP_LOW = prove
 (`!(Phi:real^3->real^3) c.
     abs c <= &1 / &512 /\ Phi continuous_on moi_s35_bann /\
     (!z. z IN moi_s35_bann ==> dist(Phi z,z) < &1 / &1024)
     ==> ?k0. k0 IN components {x | x IN IMAGE Phi moi_s35_bann /\ x$3 <= c} /\
              !k. k IN components {x | x IN IMAGE Phi moi_s35_bann /\ x$3 <= c} /\
                  ~(k = k0) ==> k SUBSET moi_s35_ttube`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN moi_s35_bann
        ==> &5 / &32 <= moi_s35_n z /\ moi_s35_n z <= &11 / &32 /\
            z$3 = (moi_s35_n z - &1 / &4) / &8 /\
            abs((Phi:real^3->real^3) z$1 - z$1) < &1 / &1024 /\
            abs(Phi z$2 - z$2) < &1 / &1024 /\
            abs(Phi z$3 - z$3) < &1 / &1024`
  (LABEL_TAC "zf") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC]] THEN
    TRY(MATCH_MP_TAC MOI_S5A_DIST_COMPONENTS THEN ASM_SIMP_TAC[]) THEN
    UNDISCH_TAC `(z:real^3) IN moi_s35_bann` THEN
    REWRITE_TAC[moi_s35_bann; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5A_COMP_GENERIC THEN
  EXISTS_TAC `IMAGE (Phi:real^3->real^3)
    {z | z IN moi_s35_bann /\ &5 / &32 <= moi_s35_n z /\ moi_s35_n z <= &13 / &64}` THEN
  EXISTS_TAC `(Phi:real^3->real^3) (vector[&5 / &32; &0; -- &3 / &256])` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_bann` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC MOI_S5A_RING_CONNECTED THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_ELIM_THM; moi_s35_bann; moi_s35_n; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
                    ALL_TAC] THEN
    REMOVE_THEN "zf" (MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs c <= &1 / &512` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) MP_TAC) THEN
    REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM; IN_ELIM_THM] THEN
    DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    REMOVE_THEN "zf" (MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_s35_ttube; IN_ELIM_THM; moi_s35_n] THEN
    UNDISCH_TAC `abs c <= &1 / &512` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[moi_s35_n] THEN
    MP_TAC(SPECL [`(Phi:real^3->real^3) z$1`; `(Phi:real^3->real^3) z$2`;
                  `(z:real^3)$1`; `(z:real^3)$2`; `&1 / &1024`]
                 SPDR12_MAX_ABS_LIP) THEN
    SPEC_TAC(`max (abs((Phi:real^3->real^3) z$1)) (abs(Phi z$2))`, `m:real`) THEN
    SPEC_TAC(`max (abs((z:real^3)$1)) (abs(z$2))`, `n:real`) THEN
    REAL_ARITH_TAC]);;

(* The upper half: one component carries the outer end ring.              *)
let MOI_S5A_COMP_HIGH = prove
 (`!(Phi:real^3->real^3) c.
     abs c <= &1 / &512 /\ Phi continuous_on moi_s35_bann /\
     (!z. z IN moi_s35_bann ==> dist(Phi z,z) < &1 / &1024)
     ==> ?k0. k0 IN components {x | x IN IMAGE Phi moi_s35_bann /\ c <= x$3} /\
              !k. k IN components {x | x IN IMAGE Phi moi_s35_bann /\ c <= x$3} /\
                  ~(k = k0) ==> k SUBSET moi_s35_ttube`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN moi_s35_bann
        ==> &5 / &32 <= moi_s35_n z /\ moi_s35_n z <= &11 / &32 /\
            z$3 = (moi_s35_n z - &1 / &4) / &8 /\
            abs((Phi:real^3->real^3) z$1 - z$1) < &1 / &1024 /\
            abs(Phi z$2 - z$2) < &1 / &1024 /\
            abs(Phi z$3 - z$3) < &1 / &1024`
  (LABEL_TAC "zf") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [ALL_TAC; CONJ_TAC THENL [ALL_TAC; CONJ_TAC]] THEN
    TRY(MATCH_MP_TAC MOI_S5A_DIST_COMPONENTS THEN ASM_SIMP_TAC[]) THEN
    UNDISCH_TAC `(z:real^3) IN moi_s35_bann` THEN
    REWRITE_TAC[moi_s35_bann; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5A_COMP_GENERIC THEN
  EXISTS_TAC `IMAGE (Phi:real^3->real^3)
    {z | z IN moi_s35_bann /\ &19 / &64 <= moi_s35_n z /\ moi_s35_n z <= &11 / &32}` THEN
  EXISTS_TAC `(Phi:real^3->real^3) (vector[&11 / &32; &0; &3 / &256])` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_bann` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC MOI_S5A_RING_CONNECTED THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_ELIM_THM; moi_s35_bann; moi_s35_n; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    CONJ_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
                    ALL_TAC] THEN
    REMOVE_THEN "zf" (MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs c <= &1 / &512` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) MP_TAC) THEN
    REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM; IN_ELIM_THM] THEN
    DISCH_TAC THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    REMOVE_THEN "zf" (MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_s35_ttube; IN_ELIM_THM; moi_s35_n] THEN
    UNDISCH_TAC `abs c <= &1 / &512` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[moi_s35_n] THEN
    MP_TAC(SPECL [`(Phi:real^3->real^3) z$1`; `(Phi:real^3->real^3) z$2`;
                  `(z:real^3)$1`; `(z:real^3)$2`; `&1 / &1024`]
                 SPDR12_MAX_ABS_LIP) THEN
    SPEC_TAC(`max (abs((Phi:real^3->real^3) z$1)) (abs(Phi z$2))`, `m:real`) THEN
    SPEC_TAC(`max (abs((z:real^3)$1)) (abs(z$2))`, `n:real`) THEN
    REAL_ARITH_TAC]);;

let MOI_S5A_HPSI = prove
 (`!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> (h o psi e) continuous_on moi_s35_cube /\
         (!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
                (h o psi e) x = (h o psi e) y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CHART_IN_T) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN moi_s35_cube /\ y IN moi_s35_cube /\
             (psi:(real^N->bool)->real^3->real^N) e x = psi e y ==> x = y`)
      o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN UNIONS t /\ y IN UNIONS t /\
             (h:real^N->real^3) x = h y ==> x = y`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_cube
                   SUBSET UNIONS t`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]]);;

(* The map Phi = (A-chart)^-1 o (B-chart) on bann: close to the identity in  *)
(* the model (uniform continuity of the inverse of h o psi e on the cube),   *)
(* and its image is the preimage of the B-annulus under the A-chart.         *)

let MOI_S5A_C_PHI = prove
 (mk_imp(MOI_S35_MARKER,
  `!t l (h:real^N->real^3) w av bv psi kk e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s35_edge l e
     ==> ?d. &0 < d /\
             moi_s5a_good t l h av bv psi e d
              (\ff cc. ?(Phi:real^3->real^3) (g:real^3->real^3).
                 homeomorphism (moi_s35_dom,
                                IMAGE (moi_s35_ach ff av psi e) moi_s35_dom)
                               (moi_s35_ach ff av psi e,g) /\
                 IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann SUBSET
                 IMAGE (moi_s35_ach ff av psi e) moi_s35_dom /\
                 Phi = g o moi_s35_bch ff bv psi e /\
                 Phi continuous_on moi_s35_bann /\
                 (!z. z IN moi_s35_bann
                      ==> Phi z IN moi_s35_dom /\
                          moi_s35_ach ff av psi e (Phi z) =
                          moi_s35_bch ff bv psi e z /\
                          dist(Phi z,z) < &1 / &1024) /\
                 {x | x IN moi_s35_dom /\
                      moi_s35_ach ff av psi e x IN
                      IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann} =
                 IMAGE Phi moi_s35_bann)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_US_FACTS THEN STRIP_TAC THEN
  MOI_S5A_MODEL_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] (MP MOI_S5A_C_E13 (ASSUME MOI_S35_MARKER)))
  THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d13:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "g13"))) THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_HPSI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) o (psi:(real^N->bool)->real^3->real^N) e`;
                 `moi_s35_cube`; `&1 / &1024`] MOI_S5A_INVERSE_UCONT) THEN
  ASM_REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "uc"))) THEN
  EXISTS_TAC `min d13 eta` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "g13" (MP_TAC o SPECL [`ff:real^N->real^N->real^3`;
    `err:real^N->real`; `cc:(real^N->bool)->real`] o
    REWRITE_RULE[moi_s5a_good]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  BETA_TAC THEN DISCH_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_s35_dom`; `moi_s35_ach (ff:real^N->real^N->real^3) av psi e`;
                 `IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                        moi_s35_dom`] HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^3`) THEN
  SUBGOAL_THEN `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                  moi_s35_bann SUBSET
                IMAGE (moi_s35_ach ff av psi e) moi_s35_dom`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                      moi_s5a_us` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MAP_EVERY UNDISCH_TAC
     [`moi_s5a_us SUBSET interior moi_s35_stube`;
      `moi_s35_stube SUBSET moi_s35_dom`] THEN
    MP_TAC(ISPEC `moi_s35_stube` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism (moi_s35_dom,
     IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e) moi_s35_dom)
     (moi_s35_ach ff av psi e,(g:real^3->real^3))` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] th)) THEN
  EXISTS_TAC `(g:real^3->real^3) o moi_s35_bch (ff:real^N->real^N->real^3) bv psi e`
  THEN EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z. z IN moi_s35_bann
        ==> ((g:real^3->real^3) o moi_s35_bch (ff:real^N->real^N->real^3) bv psi e) z
              IN moi_s35_dom /\
            moi_s35_ach ff av psi e ((g o moi_s35_bch ff bv psi e) z) =
            moi_s35_bch ff bv psi e z`
  (LABEL_TAC "pz") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z IN
                  IMAGE (moi_s35_ach ff av psi e) moi_s35_dom` ASSUME_TAC THENL
     [MP_TAC(ASSUME `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                       moi_s35_bann SUBSET
                     IMAGE (moi_s35_ach ff av psi e) moi_s35_dom`) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `(g:real^3->real^3) (moi_s35_bch (ff:real^N->real^N->real^3)
                       bv psi e z) IN
                     IMAGE g (IMAGE (moi_s35_ach ff av psi e) moi_s35_dom)`
      MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
        `!y. y IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                        moi_s35_dom
             ==> moi_s35_ach ff av psi e ((g:real^3->real^3) y) = y`) o concl)) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `moi_s35_bcell UNION moi_s35_upper` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_s35_bann SUBSET moi_s35_bcell INTER moi_s35_slab` THEN
      SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                        moi_s35_dom` THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "pz" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ABBREV_TAC `x = ((g:real^3->real^3) o
                     moi_s35_bch (ff:real^N->real^N->real^3) bv psi e) z` THEN
    SUBGOAL_THEN `(z:real^3) IN moi_s35_cube /\ z IN moi_s35_bcell UNION moi_s35_upper /\
                  (x:real^3) IN moi_s35_cube` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`moi_s35_bann SUBSET moi_s35_bcell INTER moi_s35_slab`;
        `moi_s35_slab SUBSET moi_s35_cube`; `moi_s35_dom SUBSET moi_s35_cube`;
        `(z:real^3) IN moi_s35_bann`; `(x:real^3) IN moi_s35_dom`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "uc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC(NORM_ARITH
     `!a b e1 e2. dist(a:real^3,hx) < e1 /\ dist(b,hz) < e2 /\ a = b /\
                  e1 + e2 <= m
            ==> dist(hx,hz) < m`) THEN
    MAP_EVERY EXISTS_TAC
     [`moi_s35_ach (ff:real^N->real^N->real^3) av psi e x`;
      `moi_s35_bch (ff:real^N->real^N->real^3) bv psi e z`;
      `(err:real^N->real) ((av:(real^N->bool)->real^N) e)`;
      `(err:real^N->real) ((bv:(real^N->bool)->real^N) e)`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
        `!x. x IN moi_s35_dom
             ==> (g:real^3->real^3) (moi_s35_ach (ff:real^N->real^N->real^3)
                                        av psi e x) = x`) o concl)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      USE_THEN "pz" (MP_TAC o SPEC `z:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `z:real^3` THEN
      ASM_REWRITE_TAC[]]]);;


(* ------------------------------------------------------------------ *)
(* PL tools, the model annulus map onto bann, clauses (4) and        *)
(* the triangulation of (8).                                          *)
(* ------------------------------------------------------------------ *)

(* PL real-valued and vector-valued maps built from PL components.  The     *)
(* two lemmas below are copies of MOI_FRN_PL_VECTOR3 and                     *)
(* MOI_FRN_PL_REAL_RULES of pc_moi_fnd_rn.ml (not in this load closure),    *)
(* with the proofs unchanged.                                                *)

let MOI_S5A_PL_VECTOR3 = prove
 (`!(s:real^N->bool) f1 f2 f3.
     pl_map_on s (\x. lift(f1 x)) /\ pl_map_on s (\x. lift(f2 x)) /\
     pl_map_on s (\x. lift(f3 x))
     ==> pl_map_on s (\x. vector[f1 x; f2 x; f3 x]:real^3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i (h:real^N->real). pl_map_on s (\x. lift(h x))
        ==> pl_map_on s (\x. h x % basis i:real^3)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\x:real^N. h x % basis i:real^3) =
                  (\z:real^1. drop z % basis i) o (\x. lift(h x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MP_TAC(ISPECL [`(:real^1)`; `\z:real^1. drop z % basis i:real^3`;
                   `vec 0:real^3`] PL_MAP_ON_AFFINE) THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; VECTOR_ADD_RID; ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^N. vector[f1 x; f2 x; f3 x]:real^3) =
    (\x. (\x. f1 x % basis 1 + f2 x % basis 2) x + f3 x % basis 3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_ADD THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC PL_MAP_ON_ADD THEN ASM_SIMP_TAC[]);;

let MOI_S5A_PL_REAL_RULES = prove
 (`!(s:real^N->bool) f g c.
     (pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
      ==> pl_map_on s (\x. lift(f x + g x)) /\
          pl_map_on s (\x. lift(f x - g x)) /\
          pl_map_on s (\x. lift(max (f x) (g x))) /\
          pl_map_on s (\x. lift(min (f x) (g x)))) /\
     (pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(c * f x)))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC PL_MAP_ON_ADD THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_SUB; VECTOR_SUB] THEN MATCH_MP_TAC PL_MAP_ON_ADD THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[VECTOR_ARITH `--x:real^1 = --(&1) % x`] THEN
      MATCH_MP_TAC PL_MAP_ON_CMUL THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(f x)`;
                     `\x:real^N. lift(g x)`] PL_MAP_ON_LIFT_MAX) THEN
      ASM_REWRITE_TAC[LIFT_DROP];
      MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(f x)`;
                     `\x:real^N. lift(g x)`] PL_MAP_ON_LIFT_MIN) THEN
      ASM_REWRITE_TAC[LIFT_DROP]];
    DISCH_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC PL_MAP_ON_CMUL THEN ASM_REWRITE_TAC[]]);;

let MOI_S5A_PL_COMPONENT = prove
 (`!(s:real^N->bool) k. locally_polyhedral s ==> pl_map_on s (\x. lift(x$k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(x$k)`; `vec 0:real^1`]
    PL_MAP_ON_AFFINE) THEN
  ASM_REWRITE_TAC[LINEAR_LIFT_COMPONENT; VECTOR_ADD_RID; ETA_AX]);;

let MOI_S5A_PL_LIFT_CONST = prove
 (`!(s:real^N->bool) c. locally_polyhedral s ==> pl_map_on s (\x. lift c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `lift c`] PL_MAP_ON_CONST) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5A_PL_LIFT_ABS = prove
 (`!(s:real^N->bool) f.
     pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(abs(f x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. lift(abs(f x))) =
                (\x. lift(max (f x) (--(&1) * f x)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->real`;
                 `\x:real^N. --(&1) * f x`; `--(&1)`] MOI_S5A_PL_REAL_RULES) THEN
  BETA_TAC THEN ASM_SIMP_TAC[]);;

(* The model annulus map: the square annulus A0 of pl_annulus_with_ends     *)
(* onto bann, by the PL radial profile ph (slope 5/32 inside [-1,1], 6/32   *)
(* outside) in each coordinate followed by the graph onto the bcell surface. *)

let moi_s5a_ph = new_definition
 `moi_s5a_ph t = (&6 * t - max (-- &1) (min (&1) t)) / &32`;;

let moi_s5a_phinv = new_definition
 `moi_s5a_phinv t = (&32 * t + max (-- &1) (min (&1) (&32 * t / &5))) / &6`;;

let moi_s5a_annf = new_definition
 `moi_s5a_annf (y:real^2) =
    vector[moi_s5a_ph(y$1); moi_s5a_ph(y$2);
           (max (abs(moi_s5a_ph(y$1))) (abs(moi_s5a_ph(y$2))) - &1 / &4) / &8]
    :real^3`;;

let moi_s5a_a0 = new_definition
 `moi_s5a_a0 = interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
               interval(--vector[&1;&1],vector[&1;&1])`;;

let MOI_S5A_PH_FACTS = prove
 (`(!s t. moi_s5a_ph s = moi_s5a_ph t ==> s = t) /\
   (!t. moi_s5a_ph(moi_s5a_phinv t) = t) /\
   (!s. abs s <= &1 ==> abs(moi_s5a_ph s) = &5 / &32 * abs s) /\
   (!s. &1 <= abs s ==> abs(moi_s5a_ph s) = (&6 * abs s - &1) / &32) /\
   (!t. abs t <= &5 / &32 ==> abs(moi_s5a_phinv t) = &32 / &5 * abs t) /\
   (!t. &5 / &32 <= abs t ==> abs(moi_s5a_phinv t) = (&32 * abs t + &1) / &6)`,
  REWRITE_TAC[moi_s5a_ph; moi_s5a_phinv] THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5A_A0_IN = prove
 (`!y:real^2. y IN moi_s5a_a0 <=>
              &1 <= max (abs(y$1)) (abs(y$2)) /\ max (abs(y$1)) (abs(y$2)) <= &2`,
  REWRITE_TAC[moi_s5a_a0; IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_S5A_SQFR_IN = prove
 (`!c y:real^2.
     &0 < c
     ==> (y IN relative_frontier(interval[--vector[c;c],vector[c;c]]) <=>
          max (abs(y$1)) (abs(y$2)) = c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier(interval[--vector[c;c]:real^2,vector[c;c]]) =
                frontier(interval[--vector[c;c],vector[c;c]])` SUBST1_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2;
                FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; IN_DIFF; IN_INTERVAL; DIMINDEX_2;
                FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_S5A_A0_POLY = prove
 (`pl_polyhedron moi_s5a_a0 /\ compact moi_s5a_a0 /\
   locally_polyhedral moi_s5a_a0`,
  SUBGOAL_THEN `pl_polyhedron moi_s5a_a0` ASSUME_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `{interval[vector[&1; -- &2]:real^2,vector[&2; &2]],
                 interval[vector[-- &2; -- &2]:real^2,vector[-- &1; &2]],
                 interval[vector[-- &2; &1]:real^2,vector[&2; &2]],
                 interval[vector[-- &2; -- &2]:real^2,vector[&2; -- &1]]}` THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                POLYTOPE_INTERVAL] THEN
    REWRITE_TAC[EXTENSION; MOI_S5A_A0_IN; UNIONS_INSERT; UNIONS_0; IN_UNION;
                NOT_IN_EMPTY; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
    X_GEN_TAC `x:real^2` THEN
    REWRITE_TAC[REAL_MAX_LE; REAL_LE_MAX; REAL_ABS_BOUNDS;
                REAL_ARITH `r <= abs a <=> r <= a \/ a <= --r`] THEN
    SUBGOAL_THEN `(&1 <= (x:real^2)$1 ==> -- &2 <= x$1) /\
                  (x$1 <= -- &1 ==> x$1 <= &2) /\
                  (&1 <= x$2 ==> -- &2 <= x$2) /\
                  (x$2 <= -- &1 ==> x$2 <= &2)` MP_TAC THENL
     [REAL_ARITH_TAC; CONV_TAC TAUT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
  REWRITE_TAC[moi_s5a_a0] THEN MATCH_MP_TAC COMPACT_DIFF THEN
  REWRITE_TAC[COMPACT_INTERVAL; OPEN_INTERVAL]);;

let MOI_S5A_PLL_ADD = prove
 (`!(s:real^N->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(f x + g x))`,
  SIMP_TAC[MOI_S5A_PL_REAL_RULES]);;

let MOI_S5A_PLL_SUB = prove
 (`!(s:real^N->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(f x - g x))`,
  SIMP_TAC[MOI_S5A_PL_REAL_RULES]);;

let MOI_S5A_PLL_MAX = prove
 (`!(s:real^N->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(max (f x) (g x)))`,
  SIMP_TAC[MOI_S5A_PL_REAL_RULES]);;

let MOI_S5A_PLL_MIN = prove
 (`!(s:real^N->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(min (f x) (g x)))`,
  SIMP_TAC[MOI_S5A_PL_REAL_RULES]);;

let MOI_S5A_PLL_CMUL = prove
 (`!(s:real^N->bool) f c.
     pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(c * f x))`,
  SIMP_TAC[MOI_S5A_PL_REAL_RULES]);;

let rec MOI_S5A_PLL_TAC g =
  FIRST [FIRST_ASSUM MATCH_ACCEPT_TAC;
         MATCH_MP_TAC MOI_S5A_PL_LIFT_CONST THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC MOI_S5A_PL_COMPONENT THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC MOI_S5A_PLL_ADD THEN CONJ_TAC THEN MOI_S5A_PLL_TAC;
         MATCH_MP_TAC MOI_S5A_PLL_SUB THEN CONJ_TAC THEN MOI_S5A_PLL_TAC;
         MATCH_MP_TAC MOI_S5A_PLL_MAX THEN CONJ_TAC THEN MOI_S5A_PLL_TAC;
         MATCH_MP_TAC MOI_S5A_PLL_MIN THEN CONJ_TAC THEN MOI_S5A_PLL_TAC;
         MATCH_MP_TAC MOI_S5A_PLL_CMUL THEN MOI_S5A_PLL_TAC;
         MATCH_MP_TAC MOI_S5A_PL_LIFT_ABS THEN MOI_S5A_PLL_TAC] g;;

let MOI_S5A_PH_PL = prove
 (`!(s:real^N->bool) f.
     locally_polyhedral s /\ pl_map_on s (\x. lift(f x))
     ==> pl_map_on s (\x. lift(moi_s5a_ph(f x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s5a_ph] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x / &32 = inv(&32) * x`] THEN
  MOI_S5A_PLL_TAC);;

let MOI_S5A_ANNF_PL = prove
 (`!s:real^2->bool. locally_polyhedral s ==> pl_map_on s moi_s5a_annf`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s5a_annf =
    (\y:real^2. vector[moi_s5a_ph(y$1); moi_s5a_ph(y$2);
                       (max (abs(moi_s5a_ph(y$1))) (abs(moi_s5a_ph(y$2))) -
                        &1 / &4) / &8]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s5a_annf]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5A_PL_VECTOR3 THEN
  SUBGOAL_THEN `!k. pl_map_on (s:real^2->bool) (\y. lift(moi_s5a_ph(y$k)))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_S5A_PH_PL THEN
    ASM_SIMP_TAC[MOI_S5A_PL_COMPONENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x / &8 = inv(&8) * x`] THEN
  MOI_S5A_PLL_TAC);;

let MOI_S5A_ANNF_COMP = prove
 (`!y:real^2. moi_s5a_annf y$1 = moi_s5a_ph(y$1) /\
              moi_s5a_annf y$2 = moi_s5a_ph(y$2) /\
              moi_s5a_annf y$3 =
              (max (abs(moi_s5a_ph(y$1))) (abs(moi_s5a_ph(y$2))) - &1 / &4) / &8 /\
              moi_s35_n (moi_s5a_annf y) =
              max (abs(moi_s5a_ph(y$1))) (abs(moi_s5a_ph(y$2)))`,
  REWRITE_TAC[moi_s5a_annf; moi_s35_n; VECTOR_3]);;

let MOI_S5A_ANNF_INJ = prove
 (`!y y':real^2. moi_s5a_annf y = moi_s5a_annf y' ==> y = y'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `\x:real^3. x$1`) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x:real^3. x$2`) THEN
  REWRITE_TAC[MOI_S5A_ANNF_COMP] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
  MESON_TAC[MOI_S5A_PH_FACTS]);;

let MOI_S5A_ANNF_PREIM = prove
 (`!x:real^3. moi_s5a_annf (vector[moi_s5a_phinv(x$1); moi_s5a_phinv(x$2)]) =
              vector[x$1; x$2;
                     (max (abs(x$1)) (abs(x$2)) - &1 / &4) / &8]`,
  REWRITE_TAC[moi_s5a_annf; VECTOR_2; MOI_S5A_PH_FACTS]);;

let MOI_S5A_PH_CASES = prove
 (`!s. (abs s <= &1 ==> abs(moi_s5a_ph s) = &5 / &32 * abs s) /\
       (&1 <= abs s ==> abs(moi_s5a_ph s) = (&6 * abs s - &1) / &32)`,
  REWRITE_TAC[MOI_S5A_PH_FACTS]);;

let MOI_S5A_PHINV_CASES = prove
 (`!t. (abs t <= &5 / &32 ==> abs(moi_s5a_phinv t) = &32 / &5 * abs t) /\
       (&5 / &32 <= abs t ==> abs(moi_s5a_phinv t) = (&32 * abs t + &1) / &6)`,
  REWRITE_TAC[MOI_S5A_PH_FACTS]);;

let MOI_S5A_ANNF_SURJ = prove
 (`!x:real^3. x$3 = (max (abs(x$1)) (abs(x$2)) - &1 / &4) / &8
              ==> moi_s5a_annf (vector[moi_s5a_phinv(x$1); moi_s5a_phinv(x$2)]) = x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_S5A_ANNF_PREIM] THEN
  ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3]);;

let SPDR12_PH_MONO = prove
 (`!a b. abs a <= abs b
         ==> abs(moi_s5a_ph a) <= abs(moi_s5a_ph b) /\
             abs(moi_s5a_phinv a) <= abs(moi_s5a_phinv b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPEC `a:real` MOI_S5A_PH_CASES) THEN
    MP_TAC(SPEC `b:real` MOI_S5A_PH_CASES) THEN
    SPEC_TAC(`abs(moi_s5a_ph a)`,`p:real`) THEN
    SPEC_TAC(`abs(moi_s5a_ph b)`,`q:real`);
    MP_TAC(SPEC `a:real` MOI_S5A_PHINV_CASES) THEN
    MP_TAC(SPEC `b:real` MOI_S5A_PHINV_CASES) THEN
    SPEC_TAC(`abs(moi_s5a_phinv a)`,`p:real`) THEN
    SPEC_TAC(`abs(moi_s5a_phinv b)`,`q:real`)] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`abs a`,`u:real`) THEN SPEC_TAC(`abs b`,`v:real`) THEN
  REAL_ARITH_TAC);;

let SPDR12_PH_MAX = prove
 (`!a b. ?c. max (abs a) (abs b) = abs c /\
             max (abs(moi_s5a_ph a)) (abs(moi_s5a_ph b)) = abs(moi_s5a_ph c) /\
             max (abs(moi_s5a_phinv a)) (abs(moi_s5a_phinv b)) = abs(moi_s5a_phinv c)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `abs b <= abs a \/ abs a <= abs b`) THENL
   [EXISTS_TAC `a:real`; EXISTS_TAC `b:real`] THEN
  REWRITE_TAC[REAL_ARITH `max x y = x <=> y <= x`;
              REAL_ARITH `max x y = y <=> x <= y`] THEN
  ASM_SIMP_TAC[SPDR12_PH_MONO]);;

let MOI_S5A_ANNF_IMAGE = prove
 (`IMAGE moi_s5a_annf moi_s5a_a0 = moi_s35_bann /\
   IMAGE moi_s5a_annf (relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])) =
   moi_s35_sq (&5 / &32) (--(&3) / &256) /\
   IMAGE moi_s5a_annf (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])) =
   moi_s35_sq (&11 / &32) (&3 / &256)`,
  MP_TAC(SPEC `&1` MOI_S5A_SQFR_IN) THEN MP_TAC(SPEC `&2` MOI_S5A_SQFR_IN) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_S5A_A0_IN; moi_s35_bann;
                  moi_s35_sq; IN_ELIM_THM; MOI_S5A_ANNF_COMP] THENL
   [X_GEN_TAC `y:real^2` THEN
    X_CHOOSE_THEN `c:real` (fun th -> REWRITE_TAC[th])
      (SPECL [`(y:real^2)$1`; `(y:real^2)$2`] SPDR12_PH_MAX) THEN
    MP_TAC(SPEC `c:real` MOI_S5A_PH_CASES) THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[moi_s35_n] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `vector[moi_s5a_phinv((x:real^3)$1); moi_s5a_phinv(x$2)]:real^2` THEN
    ASM_SIMP_TAC[MOI_S5A_ANNF_SURJ; MOI_S5A_A0_IN; VECTOR_2] THEN
    UNDISCH_TAC `&5 / &32 <= max (abs ((x:real^3)$1)) (abs (x$2))` THEN
    UNDISCH_TAC `max (abs ((x:real^3)$1)) (abs (x$2)) <= &11 / &32` THEN
    X_CHOOSE_THEN `c:real` (fun th -> REWRITE_TAC[th])
      (SPECL [`(x:real^3)$1`; `(x:real^3)$2`] SPDR12_PH_MAX) THEN
    MP_TAC(SPEC `c:real` MOI_S5A_PHINV_CASES) THEN REAL_ARITH_TAC;
    X_GEN_TAC `y:real^2` THEN
    X_CHOOSE_THEN `c:real` (fun th -> REWRITE_TAC[th])
      (SPECL [`(y:real^2)$1`; `(y:real^2)$2`] SPDR12_PH_MAX) THEN
    MP_TAC(SPEC `c:real` MOI_S5A_PH_CASES) THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[moi_s35_n] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `vector[moi_s5a_phinv((x:real^3)$1); moi_s5a_phinv(x$2)]:real^2` THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S5A_ANNF_SURJ THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      UNDISCH_TAC `max (abs ((x:real^3)$1)) (abs (x$2)) = &5 / &32` THEN
      X_CHOOSE_THEN `c:real` (fun th -> REWRITE_TAC[th])
        (SPECL [`(x:real^3)$1`; `(x:real^3)$2`] SPDR12_PH_MAX) THEN
      MP_TAC(SPEC `c:real` MOI_S5A_PHINV_CASES) THEN REAL_ARITH_TAC];
    X_GEN_TAC `y:real^2` THEN
    X_CHOOSE_THEN `c:real` (fun th -> REWRITE_TAC[th])
      (SPECL [`(y:real^2)$1`; `(y:real^2)$2`] SPDR12_PH_MAX) THEN
    MP_TAC(SPEC `c:real` MOI_S5A_PH_CASES) THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[moi_s35_n] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `vector[moi_s5a_phinv((x:real^3)$1); moi_s5a_phinv(x$2)]:real^2` THEN
    ASM_REWRITE_TAC[VECTOR_2] THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S5A_ANNF_SURJ THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      UNDISCH_TAC `max (abs ((x:real^3)$1)) (abs (x$2)) = &11 / &32` THEN
      X_CHOOSE_THEN `c:real` (fun th -> REWRITE_TAC[th])
        (SPECL [`(x:real^3)$1`; `(x:real^3)$2`] SPDR12_PH_MAX) THEN
      MP_TAC(SPEC `c:real` MOI_S5A_PHINV_CASES) THEN REAL_ARITH_TAC]]);;

let MOI_S5A_BANN_POLY = prove
 (`pl_polyhedron moi_s35_bann /\ locally_polyhedral moi_s35_bann`,
  SUBGOAL_THEN `pl_polyhedron moi_s35_bann` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_S5A_ANNF_IMAGE] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    REWRITE_TAC[MOI_S5A_A0_POLY] THEN MATCH_MP_TAC MOI_S5A_ANNF_PL THEN
    REWRITE_TAC[MOI_S5A_A0_POLY];
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]]);;

(* (4) the B-annulus is a PL annulus with the two level squares as ends.    *)

let MOI_S5A_C_E11 = prove
 (`!t l (h:real^N->real^3) w av bv psi kk ff err e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s5a_apx t l av bv psi h ff err /\
     moi_s35_edge l e
     ==> pl_annulus_with_ends (IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann)
           (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_sq (&5 / &32) (--(&3) / &256)))
           (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_sq (&11 / &32) (&3 / &256)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MOI_S5A_MODEL_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_BANN_POLY THEN STRIP_TAC THEN
  MP_TAC MOI_S5A_A0_POLY THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s35_bann SUBSET moi_s35_bcell UNION moi_s35_upper`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_bann SUBSET moi_s35_bcell INTER moi_s35_slab` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on moi_s35_bann (moi_s35_bch (ff:real^N->real^N->real^3)
                                          bv psi e)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!s. s SUBSET moi_s35_bcell UNION moi_s35_upper /\ locally_polyhedral s
           ==> pl_map_on s (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)`)
      o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `f = moi_s35_bch (ff:real^N->real^N->real^3) bv psi e o moi_s5a_annf` THEN
  SUBGOAL_THEN `pl_map_on moi_s5a_a0 (f:real^2->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `moi_s35_bann` THEN ASM_SIMP_TAC[MOI_S5A_ANNF_PL] THEN
    REWRITE_TAC[MOI_S5A_ANNF_IMAGE; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. IMAGE (f:real^2->real^3) s =
                    IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                          (IMAGE moi_s5a_annf s)`
  ASSUME_TAC THENL [EXPAND_TAC "f" THEN REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s5a_a0`; `f:real^2->real^3`;
                 `IMAGE (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)
                        moi_s35_bann`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON; MOI_S5A_ANNF_IMAGE] THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[o_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `y':real^2`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S5A_ANNF_INJ THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!x y. x IN moi_s35_bcell UNION moi_s35_upper /\
             y IN moi_s35_bcell UNION moi_s35_upper /\
             moi_s35_bch (ff:real^N->real^N->real^3) bv psi e x =
             moi_s35_bch ff bv psi e y ==> x = y`) o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!y:real^2. y IN moi_s5a_a0 ==> moi_s5a_annf y IN moi_s35_bann`
    MP_TAC THENL
     [REWRITE_TAC[GSYM MOI_S5A_ANNF_IMAGE] THEN SIMP_TAC[FUN_IN_IMAGE];
      UNDISCH_TAC `moi_s35_bann SUBSET moi_s35_bcell UNION moi_s35_upper` THEN
      UNDISCH_TAC `(y:real^2) IN moi_s5a_a0` THEN
      UNDISCH_TAC `(y':real^2) IN moi_s5a_a0` THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^2`)] THEN
  REWRITE_TAC[pl_annulus_with_ends] THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^3`; `g:real^3->real^2`] THEN
  ASM_REWRITE_TAC[MOI_S5A_ANNF_IMAGE] THEN
  REWRITE_TAC[GSYM moi_s5a_a0] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[]);;

(* (8) the preimage of the B-annulus under the A-chart is triangulable.     *)

let MOI_S5A_E20_TRI = prove
 (`!(phi:real^3->real^3) g (bb:real^3->real^3).
     homeomorphism (moi_s35_dom,IMAGE phi moi_s35_dom) (phi,g) /\
     pl_map_on moi_s35_dom phi /\ pl_map_on moi_s35_bann bb /\
     IMAGE bb moi_s35_bann SUBSET IMAGE phi moi_s35_dom
     ==> ?k. simplicial_complex k /\ UNIONS k = IMAGE (g o bb) moi_s35_bann`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN REWRITE_TAC[MOI_S5A_BANN_POLY] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
  EXISTS_TAC `IMAGE (phi:real^3->real^3) moi_s35_dom` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
  MAP_EVERY EXISTS_TAC [`moi_s35_dom`; `phi:real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S5A_VERT_FINITE = prove
 (`!k:(real^3->bool)->bool.
     simplicial_complex k ==> FINITE {v$3 | v | {v} IN k}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {v:real^3 | {v} IN k}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN
    CONJ_TAC THENL [SET_TAC[]; ASM_MESON_TAC[simplicial_complex]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v$3 | v | {v} IN k} =
                IMAGE (\v:real^3. v$3) {v | {v} IN k}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ASM_SIMP_TAC[FINITE_IMAGE]]);;


(* ------------------------------------------------------------------ *)
(* Vertex radii: kk off the cell boundaries, the marker radius,       *)
(* the fill radius.                                                   *)
(* ------------------------------------------------------------------ *)

(* The compacta kk v miss the boundary of every pierced source cell: their  *)
(* points are relative interior points of the cell inside an open star, on   *)
(* which h is an open embedding (invariance of domain).                      *)

let MOI_S5A_KK_NOT_BD = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v cc bs.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l /\
     (!e. abs(cc e) <= &1 / &512) /\
     pl_cell_with_boundary 3 (moi_s35_csrc t l av bv psi cc v) bs
     ==> DISJOINT (kk v) bs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_REGION_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`v:real^N`; `cc:(real^N->bool)->real`] MOI_S5A_CSRC_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (can (term_match []
    `!v. {v} IN l ==> compact ((kk:real^N->real^N->bool) v) /\ P v`) o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `cc:(real^N->bool)->real` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
  ASM_REWRITE_TAC[interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `U:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(p:real^N) IN moi_s35_csrc t l av bv psi cc v` ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^N) IN u` THEN
    UNDISCH_TAC `u SUBSET moi_s35_csrc t l av bv psi cc (v:real^N)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^N. x IN moi_s5a_nbrs l av bv v /\
                           p IN derived_dual_cell t l x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5a_region t l av bv psi (v:real^N) SUBSET
                 UNIONS {derived_dual_cell t l x | x | x IN moi_s5a_nbrs l av bv v}` THEN
    REWRITE_TAC[moi_s5a_region; SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN ANTS_TAC THENL
     [DISJ1_TAC THEN
      MP_TAC(ASSUME `moi_s35_csrc t l av bv psi cc (v:real^N) SUBSET
                     moi_s35_cplus t l av bv psi v`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:real^N} IN l` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) IN moi_sta_open_star t x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `x:real^N`] MOI_S5A_CELL_OPEN_STAR) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_csrc t l av bv psi cc (v:real^N) SUBSET UNIONS t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s5a_region t l av bv psi (v:real^N)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s5a_region] THEN
    MP_TAC(ASSUME `moi_s35_csrc t l av bv psi cc (v:real^N) SUBSET
                   moi_s35_cplus t l av bv psi v`) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((h:real^N->real^3) p IN
                  interior(IMAGE h (moi_s35_csrc t l av bv psi cc (v:real^N))))`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_S5A_CELL_BD_NOT_INTERIOR THEN
    EXISTS_TAC `bs:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool`
      THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool`
      THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[]] THEN
  MATCH_MP_TAC(SET_RULE `!s. (y:real^3) IN s /\ s SUBSET t ==> y IN t`) THEN
  EXISTS_TAC `IMAGE (h:real^N->real^3) (U INTER moi_sta_open_star t x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `(p:real^N) IN u` THEN
    UNDISCH_TAC `u:real^N->bool = UNIONS t INTER U` THEN SET_TAC[];
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN
      UNDISCH_TAC `u SUBSET moi_s35_csrc t l av bv psi cc (v:real^N)` THEN
      UNDISCH_TAC `u:real^N->bool = UNIONS t INTER U` THEN
      MATCH_MP_TAC(SET_RULE
        `o1 SUBSET ut ==> u = ut INTER U ==> u SUBSET c
         ==> U INTER o1 SUBSET (c:real^N->bool)`) THEN
      REWRITE_TAC[moi_sta_open_star] THEN SET_TAC[];
      MATCH_MP_TAC MOI_S5A_STAR_IMAGE_OPEN THEN
      EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]]);;

(* A separation radius for the marker lemma on the smallest pierced cell:   *)
(* an embedding within r of h on cplus v covers h(kk v) inside its image of *)
(* that cell.                                                                *)

let MOI_S5A_MARK_V = prove
 (mk_imp(MOI_S35_MARKER,
  `!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l
     ==> ?r. &0 < r /\
             !f. f continuous_on moi_s35_cplus t l av bv psi v /\
                 (!x y. x IN moi_s35_cplus t l av bv psi v /\
                        y IN moi_s35_cplus t l av bv psi v /\ f x = f y ==> x = y) /\
                 (!x. x IN moi_s35_cplus t l av bv psi v ==> dist(f x,h x) < r)
                 ==> IMAGE h (kk v) SUBSET
                     interior (IMAGE f (moi_s35_csrc t l av bv psi
                                          (\e. --(&1 / &512)) v))`),
  DISCH_THEN(LABEL_TAC "mk") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  ABBREV_TAC `cm = moi_s35_csrc t l av bv psi
                     (\e:real^N->bool. --(&1 / &512)) (v:real^N)` THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `\e:real^N->bool. --(&1 / &512)` o CONJUNCT1) THEN
  ANTS_TAC THENL [BETA_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `bs:real^N->bool`)) THEN
  MP_TAC(moi_s5a_cs [`v:real^N`; `\e:real^N->bool. --(&1 / &512)`;
                     `bs:real^N->bool`] MOI_S5A_KK_NOT_BD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN BETA_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`3`; `cm:real^N->bool`; `bs:real^N->bool`] MOI_S5A_CELL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_CPLUS_UNIONS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact ((kk:real^N->real^N->bool) v) /\ kk v SUBSET cm`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk` THEN
    REWRITE_TAC[moi_s5a_ctx] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPEC `\e:real^N->bool. --(&1 / &512)` o CONJUNCT1)) THEN
    ANTS_TAC THENL [BETA_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MESON_TAC[INTERIOR_OF_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(cm:real^N->bool) SUBSET UNIONS t` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s35_cplus t l av bv psi (v:real^N)` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\
                    !x y. x IN (kk:real^N->real^N->bool) v /\ y IN bs
                          ==> r <= dist((h:real^N->real^3) x,h y)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(kk:real^N->real^N->bool) v = {}` THENL
     [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
    ASM_CASES_TAC `bs:real^N->bool = {}` THENL
     [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
    EXISTS_TAC `setdist(IMAGE (h:real^N->real^3) ((kk:real^N->real^N->bool) v),IMAGE h bs)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5A_SETDIST_POS THEN EXISTS_TAC `UNIONS t:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cm:real^N->bool` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SETDIST_LE_DIST THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `f:real^N->real^3` THEN STRIP_TAC THEN
  USE_THEN "mk" (MP_TAC o ISPECL [`cm:real^N->bool`; `bs:real^N->bool`;
    `(kk:real^N->real^N->bool) v`; `f:real^N->real^3`; `h:real^N->real^3`;
    `r:real`]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE
     `(s:real^N->bool) SUBSET t DIFF u <=> s SUBSET t /\ DISJOINT s u`] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `moi_s35_cplus t l av bv psi (v:real^N)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN
    EXISTS_TAC `moi_s35_cplus t l av bv psi (v:real^N)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^N) IN bs` THEN
    UNDISCH_TAC `(bs:real^N->bool) SUBSET cm` THEN
    UNDISCH_TAC `(cm:real^N->bool) SUBSET moi_s35_cplus t l av bv psi v` THEN
    SET_TAC[]]);;

let MOI_S5A_CBIG_SUB = prove
 (`!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l
     ==> moi_s35_cbig t l av bv psi v SUBSET
         derived_dual_cell t l v UNION
         UNIONS {IMAGE (psi e) moi_s35_slab | e | e IN moi_s5a_edges l av bv v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MOI_S5A_MODEL_TAC THEN
  SUBGOAL_THEN `!e. IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                      (moi_s35_bcell INTER moi_s35_lower) SUBSET
                    IMAGE (psi e) moi_s35_slab /\
                    IMAGE (psi e) (moi_s35_slab INTER moi_s35_upper) SUBSET
                    IMAGE (psi e) moi_s35_slab`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_cbig; moi_s35_cplus; moi_s5a_edges; UNION_SUBSET] THEN
  REPEAT CONJ_TAC THEN TRY(SET_TAC[]) THEN
  REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_UNION] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* The fill radius of a vertex: compact sets near h(cbig v) together with   *)
(* their bounded complementary pieces stay in w v (FILL; the complement of a *)
(* cell in real^3 is connected).                                             *)

let MOI_S5A_FILL_V = prove
 (mk_imp(MOI_S35_FILL,
  `!t l (h:real^N->real^3) w av bv psi kk v.
     moi_s5a_ctx t l h w av bv psi kk /\ {v} IN l
     ==> ?r. &0 < r /\
             !k'. compact k' /\
                  (!x. x IN k'
                       ==> setdist({x},IMAGE h (moi_s35_cbig t l av bv psi v)) < r)
                  ==> k' UNION inside k' SUBSET w v`),
  DISCH_THEN(LABEL_TAC "fill") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_CBIG_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_REGION_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_VERTEX_IN_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `moi_s35_cbig t l av bv psi (v:real^N) SUBSET UNIONS t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s5a_region t l av bv psi (v:real^N)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s35_cbig t l av bv psi (v:real^N) SUBSET
                 derived_dual_cell t l v UNION
                 UNIONS {IMAGE (psi e) moi_s35_slab | e |
                         e IN moi_s5a_edges l av bv v}` THEN
    REWRITE_TAC[moi_s5a_region; moi_s35_cplus] THEN SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "fill" (MP_TAC o ISPECL
   [`IMAGE (h:real^N->real^3) (moi_s35_cbig t l av bv psi v)`;
    `(w:real^N->real^3->bool) v`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool`
      THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `v:real^N` THEN REWRITE_TAC[moi_s35_cbig; IN_UNION] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S5A_CELL_DOWN o check (can (term_match []
        `pl_cell_with_boundary 3
           (moi_s35_cbig t l av bv (psi:(real^N->bool)->real^3->real^N) v) bs`)
        o concl)) THEN
      DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^N`
        (X_CHOOSE_THEN `q:real^N->real^3` STRIP_ASSUME_TAC))) THEN
      UNDISCH_TAC `pl_homeomorphism (S,moi_s35_cbig t l av bv psi (v:real^N))
                     ((p:real^3->real^N),(q:real^N->real^3))` THEN
      REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
      MATCH_MP_TAC(ISPECL
        [`IMAGE (h:real^N->real^3) (moi_s35_cbig t l av bv psi v)`;
         `S:real^3->bool`] CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
      REWRITE_TAC[DIMINDEX_3; ARITH] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]]
      THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      MP_TAC(ISPECL [`S:real^3->bool`; `(h:real^N->real^3) o (p:real^3->real^N)`;
        `IMAGE (h:real^N->real^3) (moi_s35_cbig t l av bv psi v)`]
        HOMEOMORPHISM_COMPACT) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
          MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `UNIONS t:real^N->bool` THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[IMAGE_o];
          REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
          SUBGOAL_THEN `(p:real^3->real^N) x = p y` MP_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
              `!x y. x IN UNIONS t /\ y IN UNIONS t /\
                     (h:real^N->real^3) x = h y ==> x = y`) o concl)) THEN
            ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `moi_s35_cbig t l av bv psi (v:real^N) SUBSET UNIONS t` THEN
            UNDISCH_TAC `IMAGE (p:real^3->real^N) S =
                         moi_s35_cbig t l av bv psi (v:real^N)` THEN
            ASM SET_TAC[];
            ASM_MESON_TAC[]]];
        MESON_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (can (term_match []
        `!v. {v} IN l
             ==> open ((w:real^N->real^3->bool) v) /\
                 IMAGE (h:real^N->real^3) (derived_dual_cell t l v) SUBSET w v`)
        o concl)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN derived_dual_cell t l v UNION
                     UNIONS {IMAGE (psi e) moi_s35_slab | e |
                             e IN moi_s5a_edges l av bv v}` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN STRIP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (can (term_match []
          `!v. {v} IN l
               ==> open ((w:real^N->real^3->bool) v) /\
                   IMAGE (h:real^N->real^3) (derived_dual_cell t l v) SUBSET w v`)
          o concl)) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        UNDISCH_TAC `(e:real^N->bool) IN moi_s5a_edges l av bv v` THEN
        REWRITE_TAC[moi_s5a_edges; IN_ELIM_THM] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        UNDISCH_TAC `(x:real^N) IN IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                       moi_s35_slab` THEN
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (can (term_match []
          `!x. x IN moi_s35_slab
               ==> (psi:(real^N->bool)->real^3->real^N) e x IN UNIONS t /\
                   (h:real^N->real^3) (psi e x) IN
                     (w:real^N->real^3->bool) ((av:(real^N->bool)->real^N) e) /\
                   h (psi e x) IN w ((bv:(real^N->bool)->real^N) e)`) o concl)) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(av:(real^N->bool)->real^N) e = v \/
                     (bv:(real^N->bool)->real^N) e = v` THEN
        MESON_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[]]);;


(* ------------------------------------------------------------------ *)
(* The combined per-edge good lemma.                                  *)
(* ------------------------------------------------------------------ *)

(* All per-edge clauses that hold for small error sums, combined.            *)

let moi_s5a_edge_lems =
  let a1 = ASSUME MOI_S35_MARKER and a2 = ASSUME MOI_S35_LOCAL_SIGN
  and a3 = ASSUME MOI_S35_CLOSE_SIGN in
  [MP MOI_S5A_C_F2B (CONJ a1 (CONJ a2 a3)); MOI_S5A_C_F2C; MOI_S5A_C_F2D_E14;
   MOI_S5A_C_F2E_E17; MP MOI_S5A_C_E16 a1; MP MOI_S5A_C_E13 a1; MOI_S5A_C_E9;
   MOI_S5A_C_E15; MP MOI_S5A_C_PHI a1];;

let moi_s5a_edge_body =
  let getp th =
    let _,bod = strip_forall(concl th) in
    let _,b = dest_exists(rand bod) in
    snd(strip_abs(rand(rand b))) in
  list_mk_conj (map getp moi_s5a_edge_lems);;

let moi_s5a_edge_stmt =
  let pp = list_mk_abs([`ff:real^N->real^N->real^3`; `cc:(real^N->bool)->real`],
                       moi_s5a_edge_body) in
  let good = mk_comb(`moi_s5a_good (t:(real^N->bool)->bool) l (h:real^N->real^3)
                         av bv psi (e:real^N->bool) d`, pp) in
  let inner = mk_imp(`moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk /\
                      moi_s35_edge l (e:real^N->bool)`,
                     mk_exists(`d:real`, mk_conj(`&0 < d`, good))) in
  list_mk_forall(moi_s5a_ctxl @ [`e:real^N->bool`], inner);;

let MOI_S5A_EDGE_GOOD = prove
 (mk_imp(list_mk_conj[MOI_S35_MARKER; MOI_S35_LOCAL_SIGN; MOI_S35_CLOSE_SIGN],
         moi_s5a_edge_stmt),
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (th,i) ->
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] th) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN (mk_var("d"^string_of_int i,`:real`))
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC ("g"^string_of_int i)))))
    (zip moi_s5a_edge_lems (1--9)) THEN
  EXISTS_TAC `min d1 (min d2 (min d3 (min d4 (min d5 (min d6 (min d7
                (min d8 d9)))))))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s5a_good] THEN
  MAP_EVERY X_GEN_TAC [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `cc:(real^N->bool)->real`] THEN
  REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  MAP_EVERY (fun i ->
    REMOVE_THEN ("g"^string_of_int i) (MP_TAC o SPECL
      [`ff:real^N->real^N->real^3`; `err:real^N->real`;
       `cc:(real^N->bool)->real`] o REWRITE_RULE[moi_s5a_good]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) (1--9) THEN
  ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------ *)
(* The fill clause of a vertex and the disjointness clauses of        *)
(* the frame.                                                         *)
(* ------------------------------------------------------------------ *)

(* The fill clause of a vertex v: the image cell, the A-images of the tubes  *)
(* of its B-side edges and their bounded complementary pieces lie in w v.     *)

let MOI_S5A_F1E = prove
 (`!t l (h:real^N->real^3) w av bv psi kk ff err cc v rf.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s5a_apx t l av bv psi h ff err /\
     {v} IN l /\ (!e. abs(cc e) <= &1 / &512) /\
     (!k'. compact k' /\
           (!x. x IN k'
                ==> setdist({x},IMAGE h (moi_s35_cbig t l av bv psi v)) < rf)
           ==> k' UNION inside k' SUBSET w v) /\
     err v <= rf /\ (!e. moi_s35_edge l e /\ bv e = v ==> err (av e) <= rf)
     ==> IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v) UNION
         UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e |
                 moi_s35_edge l e /\ bv e = v} UNION
         inside (IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v) UNION
                 UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e |
                         moi_s35_edge l e /\ bv e = v}) SUBSET w v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MOI_S5A_MODEL_TAC THEN
  REWRITE_TAC[SET_RULE `(a:real^3->bool) UNION b UNION c = (a UNION b) UNION c`] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
    `!k'. compact k' /\ P k' ==> k' UNION inside k' SUBSET (w:real^3->bool)`) o
    concl)) THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
     `cc:(real^N->bool)->real`; `v:real^N`] MOI_S5A_XX_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`v:real^N`; `cc:(real^N->bool)->real`] MOI_S5A_CSRC_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
    `ff:real^N->real^N->real^3`; `err:real^N->real`;
    `v:real^N`] MOI_S5A_APX_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `FINITE {e | moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `moi_s5a_edges l (av:(real^N->bool)->real^N) bv v` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `v:real^N`] MOI_S5A_EDGES_FINITE) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_s5a_edges] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v
        ==> compact (IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)
                       moi_s35_stube) /\
            (!z. z IN moi_s35_stube
                 ==> dist(moi_s35_ach ff av psi e z,h(psi e z)) < rf /\
                     (psi:(real^N->bool)->real^3->real^N) e z IN
                     moi_s35_cbig t l av bv psi v)`
  (LABEL_TAC "ec") THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_S5A_MODEL_COMPACT] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s35_dom` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `(err:real^N->real) ((av:(real^N->bool)->real^N) e)` THEN
        CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
            `!x. x IN moi_s35_dom
                 ==> dist(moi_s35_ach (ff:real^N->real^N->real^3) av psi e x,
                          (h:real^N->real^3)(psi e x)) < err (av e)`) o concl)) THEN
          UNDISCH_TAC `(z:real^3) IN moi_s35_stube` THEN
          UNDISCH_TAC `moi_s35_stube SUBSET moi_s35_dom` THEN SET_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[moi_s35_cbig; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
        DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `(z:real^3) IN moi_s35_stube` THEN
        UNDISCH_TAC `moi_s35_stube SUBSET moi_s35_slab` THEN SET_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      USE_THEN "ec" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN IMAGE ((ff:real^N->real^N->real^3) v)
                   (moi_s35_csrc t l av bv psi cc v)` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `dist(y:real^3,(h:real^N->real^3) p)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SETDIST_LE_DIST THEN REWRITE_TAC[IN_SING] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[moi_s35_cbig; IN_UNION] THEN DISJ1_TAC THEN
      MP_TAC(ASSUME `moi_s35_csrc t l av bv psi cc (v:real^N) SUBSET
                     moi_s35_cplus t l av bv psi v`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `(err:real^N->real) v` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
        `!x. x IN moi_s35_cplus t l av bv psi v
             ==> dist((ff:real^N->real^N->real^3) v x,(h:real^N->real^3) x) <
                 err v`) o concl)) THEN
      MP_TAC(ASSUME `moi_s35_csrc t l av bv psi cc (v:real^N) SUBSET
                     moi_s35_cplus t l av bv psi v`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC];
    UNDISCH_TAC `(y:real^3) IN IMAGE (moi_s35_ach (ff:real^N->real^N->real^3)
                                        av psi e) moi_s35_stube` THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "ec" (MP_TAC o SPEC `e:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `dist(moi_s35_ach (ff:real^N->real^N->real^3) av psi e z,
                     (h:real^N->real^3)((psi:(real^N->bool)->real^3->real^N) e z))`
    THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SETDIST_LE_DIST THEN REWRITE_TAC[IN_SING] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC]);;

(* Disjointness clauses of the frame from the global separation radii.        *)

let MOI_S5A_FRAME_SEP = prove
 (`!t l (h:real^N->real^3) w av bv psi kk eta ff err cc.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s5a_etaok t l h av bv psi kk eta /\
     (!u. {u} IN l ==> &3 * err u <= eta u) /\
     moi_s5a_apx t l av bv psi h ff err /\ (!e. abs(cc e) <= &1 / &512)
     ==> (!e v. moi_s35_edge l e /\ {v} IN l /\ ~(v = av e) /\ ~(v = bv e)
                ==> DISJOINT (IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v))
                             (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab)) /\
         (!e e'. moi_s35_edge l e /\ moi_s35_edge l e' /\ ~(e = e')
                 ==> DISJOINT (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab)
                              (IMAGE (moi_s35_ach ff av psi e') moi_s35_slab) /\
                     DISJOINT (IMAGE (moi_s35_bch ff bv psi e)
                                     (moi_s35_level (&1 / &8)))
                              (IMAGE (moi_s35_ach ff av psi e') moi_s35_slab)) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
                ==> DISJOINT (IMAGE (ff u) (moi_s35_csrc t l av bv psi cc u))
                             (IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v))) /\
         (!v e. {v} IN l /\ moi_s35_edge l e
                ==> DISJOINT (IMAGE h (kk v))
                             (IMAGE (moi_s35_ach ff av psi e) moi_s35_stube))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u v X Y. {u} IN l /\ {v} IN l /\
              X IN moi_s5a_pieces t l av bv psi kk u /\
              Y IN moi_s5a_pieces t l av bv psi kk v /\ DISJOINT X Y /\
              X SUBSET moi_s35_cplus t l av bv psi u /\
              Y SUBSET moi_s35_cplus t l av bv psi v
              ==> DISJOINT (IMAGE ((ff:real^N->real^N->real^3) u) X)
                           (IMAGE (ff v) Y)`
  (LABEL_TAC "gs") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5A_GLOBAL_SEP THEN
    MAP_EVERY EXISTS_TAC
     [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `av:(real^N->bool)->real^N`;
      `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
      `kk:real^N->real^N->bool`; `eta:real^N->real`; `err:real^N->real`;
      `u:real^N`; `v:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s5a_apx t l av bv psi (h:real^N->real^3) ff err` THEN
    REWRITE_TAC[moi_s5a_apx] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `u:real^N` th) THEN MP_TAC(SPEC `v:real^N` th))
    THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v e. {v} IN l /\ moi_s35_edge l e /\ (av e = v \/ bv e = v)
          ==> IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab IN
              moi_s5a_pieces t l av bv psi kk v /\
              IMAGE (psi e) moi_s35_stube IN moi_s5a_pieces t l av bv psi kk v /\
              IMAGE (psi e) (moi_s35_level (&1 / &8)) IN
              moi_s5a_pieces t l av bv psi kk v`
  (LABEL_TAC "pc") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    REWRITE_TAC[moi_s5a_pieces; IN_UNION; IN_IMAGE; moi_s5a_edges; IN_ELIM_THM;
                IN_INSERT] THEN
    REPEAT CONJ_TAC THENL
     [DISJ2_TAC THEN DISJ1_TAC; DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC;
      DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC] THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. {v} IN l
        ==> moi_s35_cplus t l av bv psi v IN moi_s5a_pieces t l av bv psi kk v /\
            (kk:real^N->real^N->bool) v IN moi_s5a_pieces t l av bv psi kk v`
  (LABEL_TAC "pv") THENL
   [REWRITE_TAC[moi_s5a_pieces; IN_UNION; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(moi_s5a_cs [`v:real^N`; `cc:(real^N->bool)->real`] MOI_S5A_CSRC_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[moi_s35_ach; IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE
     `!s'. s SUBSET s' /\ DISJOINT (IMAGE (f:real^N->real^3) s') t
           ==> DISJOINT (IMAGE f s) t`) THEN
    EXISTS_TAC `moi_s35_cplus t l av bv psi (v:real^N)` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "pv" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "pc" (MP_TAC o SPECL [`(av:(real^N->bool)->real^N) e`;
                                   `e:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REMOVE_THEN "gs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC MOI_S5A_CPLUS_SLAB_DISJ THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
                          `kk:real^N->real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(moi_s5a_cs [`e':real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(moi_s5a_cs [`e':real^N->bool`] MOI_S5A_CPLUS_A) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_B) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`; `e':real^N->bool`] MOI_S5A_SLAB_DISJ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MOI_S5A_MODEL_TAC THEN
    USE_THEN "pc" (MP_TAC o SPECL [`(av:(real^N->bool)->real^N) e`;
                                   `e:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "pc" (MP_TAC o SPECL [`(av:(real^N->bool)->real^N) e'`;
                                   `e':real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "pc" (MP_TAC o SPECL [`(bv:(real^N->bool)->real^N) e`;
                                   `e:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                (moi_s35_level (&1 / &8)))
                          (IMAGE (psi e') moi_s35_slab) /\
                  IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                        (moi_s35_level (&1 / &8)) SUBSET
                  moi_s35_cplus t l av bv psi ((bv:(real^N->bool)->real^N) e)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `DISJOINT (IMAGE ((psi:(real^N->bool)->real^3->real^N) e)
                                    moi_s35_slab)
                              (IMAGE (psi e') moi_s35_slab)` THEN
        MATCH_MP_TAC(SET_RULE
         `(s:real^3->bool) SUBSET s'
          ==> DISJOINT (IMAGE (f:real^3->real^N) s') t
              ==> DISJOINT (IMAGE f s) t`) THEN
        MAP_EVERY UNDISCH_TAC
         [`moi_s35_level (&1 / &8) SUBSET moi_s35_slab INTER moi_s35_upper`] THEN
        SET_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_upper`
        THEN CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN
          MAP_EVERY UNDISCH_TAC
           [`moi_s35_level (&1 / &8) SUBSET moi_s35_slab INTER moi_s35_upper`] THEN
          SET_TAC[];
          FIRST_ASSUM ACCEPT_TAC]];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s35_ach; moi_s35_bch; IMAGE_o] THEN CONJ_TAC THEN
    REMOVE_THEN "gs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(moi_s5a_cs [`u:real^N`; `cc:(real^N->bool)->real`] MOI_S5A_CSRC_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(moi_s5a_cs [`v:real^N`; `cc:(real^N->bool)->real`] MOI_S5A_CSRC_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!s' t'. s SUBSET s' /\ t SUBSET t' /\
              DISJOINT (IMAGE (f:real^N->real^3) s') (IMAGE (g:real^N->real^3) t')
              ==> DISJOINT (IMAGE f s) (IMAGE g t)`) THEN
    MAP_EVERY EXISTS_TAC [`moi_s35_cplus t l av bv psi (u:real^N)`;
                          `moi_s35_cplus t l av bv psi (v:real^N)`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "pv" (MP_TAC o SPEC `u:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "pv" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REMOVE_THEN "gs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC MOI_S5A_CPLUS_DISJ THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
                          `kk:real^N->real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                       `v:real^N`] MOI_S5A_APX_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MOI_S5A_MODEL_TAC THEN
    REWRITE_TAC[moi_s35_ach; IMAGE_o] THEN
    MATCH_MP_TAC MOI_S5A_GLOBAL_SEP THEN
    MAP_EVERY EXISTS_TAC
     [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`; `av:(real^N->bool)->real^N`;
      `bv:(real^N->bool)->real^N`; `psi:(real^N->bool)->real^3->real^N`;
      `kk:real^N->real^N->bool`; `eta:real^N->real`; `err:real^N->real`;
      `v:real^N`; `(av:(real^N->bool)->real^N) e`] THEN
    USE_THEN "pv" (MP_TAC o SPEC `v:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "pc" (MP_TAC o SPECL [`(av:(real^N->bool)->real^N) e`;
                                   `e:real^N->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[DIST_REFL] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk` THEN
      REWRITE_TAC[moi_s5a_ctx] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^N` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `moi_s5a_apx t l av bv psi (h:real^N->real^3) ff err` THEN
      REWRITE_TAC[moi_s5a_apx] THEN
      DISCH_THEN(MP_TAC o SPEC `(av:(real^N->bool)->real^N) e`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      UNDISCH_TAC `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab
                   SUBSET moi_s35_cplus t l av bv psi (av e)` THEN
      UNDISCH_TAC `moi_s35_stube SUBSET moi_s35_slab` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN MESON_TAC[]]]);;


(* ------------------------------------------------------------------ *)
(* Flatness (2), the cell images are PL balls, and the full           *)
(* configuration of one edge.                                         *)
(* ------------------------------------------------------------------ *)

let MOI_S5A_IMAGE_INTER_INJ = prove
 (`!(f:A->B) u s t.
     (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\ s SUBSET u /\ t SUBSET u
     ==> IMAGE f s INTER IMAGE f t = IMAGE f (s INTER t)`,
  SET_TAC[]);;

(* (2) A-side flatness: xa meets the A-image of the slab exactly in the part *)
(* below the level (injectivity of the A-approximation on cplus).            *)

let MOI_S5A_E7 = prove
 (`!t l (h:real^N->real^3) w av bv psi kk ff err cc e.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s5a_apx t l av bv psi h ff err /\
     (!e. abs(cc e) <= &1 / &512) /\ moi_s35_edge l e
     ==> IMAGE (ff (av e)) (moi_s35_csrc t l av bv psi cc (av e)) INTER
         IMAGE (moi_s35_ach ff av psi e) moi_s35_slab =
         IMAGE (moi_s35_ach ff av psi e) {x | x IN moi_s35_slab /\ x$3 <= cc e}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_CPLUS_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`(av:(real^N->bool)->real^N) e`; `cc:(real^N->bool)->real`]
    MOI_S5A_CSRC_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
    `ff:real^N->real^N->real^3`; `err:real^N->real`;
    `(av:(real^N->bool)->real^N) e`] MOI_S5A_APX_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`; `cc:(real^N->bool)->real`;
                     `moi_s35_slab`] MOI_S5A_CSRC_PART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  REWRITE_TAC[moi_s35_ach; IMAGE_o] THEN
  MP_TAC(ISPECL [`(ff:real^N->real^N->real^3) ((av:(real^N->bool)->real^N) e)`;
    `moi_s35_cplus t l av bv psi ((av:(real^N->bool)->real^N) e)`;
    `moi_s35_csrc t l av bv psi cc ((av:(real^N->bool)->real^N) e)`;
    `IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab`]
    MOI_S5A_IMAGE_INTER_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match []
    `moi_s35_csrc t l av bv psi cc (av e) INTER
     IMAGE ((psi:(real^N->bool)->real^3->real^N) e) moi_s35_slab = s`) o concl)) THEN
  AP_TERM_TAC THEN SET_TAC[]);;

let MOI_S5A_E45 = prove
 (`!t l (h:real^N->real^3) w av bv psi kk ff err cc v.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s5a_apx t l av bv psi h ff err /\
     (!e. abs(cc e) <= &1 / &512) /\ {v} IN l
     ==> pl_ball 3 (IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `cc:(real^N->bool)->real` o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `bs:real^N->bool`)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
    `ff:real^N->real^N->real^3`; `err:real^N->real`;
    `v:real^N`] MOI_S5A_APX_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC MOI_S5A_PL_BALL_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`bs:real^N->bool`;
                        `moi_s35_cplus t l av bv psi (v:real^N)`] THEN
  ASM_REWRITE_TAC[]);;

(* The configuration of one edge (the clauses of moi_s35_edge_conf) from the  *)
(* per-edge good clauses, the fill clause of its B-end and a triangulation    *)
(* of the preimage set avoiding the level.                                    *)

let moi_s5a_fill_hyp =
 `IMAGE ((ff:real^N->real^N->real^3) ((bv:(real^N->bool)->real^N) e))
        (moi_s35_csrc t l av bv psi cc (bv e)) UNION
  UNIONS {IMAGE (moi_s35_ach ff av psi e') moi_s35_stube | e' |
          moi_s35_edge l e' /\ bv e' = bv e} UNION
  inside (IMAGE (ff (bv e)) (moi_s35_csrc t l av bv psi cc (bv e)) UNION
          UNIONS {IMAGE (moi_s35_ach ff av psi e') moi_s35_stube | e' |
                  moi_s35_edge l e' /\ bv e' = bv e})
  SUBSET (w:real^N->real^3->bool) (bv e)`;;

let moi_s5a_tri_hyp =
 `?k. simplicial_complex k /\
      UNIONS k = {x | x IN moi_s35_dom /\
                      moi_s35_ach (ff:real^N->real^N->real^3) av psi e x IN
                      IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann} /\
      !v. {v} IN k ==> ~(v$3 = (cc:(real^N->bool)->real) e)`;;

let moi_s5a_conf_concl =
 `moi_s35_edge_conf
    (moi_s35_ach (ff:real^N->real^N->real^3) av
                 (psi:(real^N->bool)->real^3->real^N) e)
    (IMAGE (ff (av e)) (moi_s35_csrc t l av bv psi cc (av e)))
    (IMAGE (ff (bv e)) (moi_s35_csrc t l av bv psi cc (bv e)))
    ((w:real^N->real^3->bool) (bv e))
    (IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann)
    (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_sq (&5 / &32) (--(&3) / &256)))
    (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_sq (&11 / &32) (&3 / &256)))
    ((cc:(real^N->bool)->real) e)`;;


let MOI_S5A_FILL_SUB = prove
 (`!a s u w:real^3->bool.
     a UNION s SUBSET a UNION u /\ a UNION u UNION inside (a UNION u) SUBSET w
     ==> a UNION s UNION inside (a UNION s) SUBSET w`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INSIDE_MONO_ALT) THEN
  UNDISCH_TAC `a UNION s SUBSET (a:real^3->bool) UNION u` THEN SET_TAC[]);;

let MOI_S5A_PRE_EDGE = prove
 (list_mk_forall(moi_s5a_ctxl @ [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                                 `cc:(real^N->bool)->real`; `e:real^N->bool`],
   mk_imp(list_mk_conj
    [`moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`;
     `moi_s5a_apx t l av bv psi (h:real^N->real^3) ff err`;
     `!e:real^N->bool. abs((cc:(real^N->bool)->real) e) <= &1 / &512`;
     `moi_s35_edge l (e:real^N->bool)`;
     moi_s5a_edge_body; moi_s5a_fill_hyp; moi_s5a_tri_hyp],
    moi_s5a_conf_concl)),
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN
   `IMAGE ((ff:real^N->real^N->real^3) ((bv:(real^N->bool)->real^N) e))
          (moi_s35_csrc t l av bv psi cc (bv e)) UNION
    IMAGE (moi_s35_ach ff av psi e) moi_s35_stube UNION
    inside (IMAGE (ff (bv e)) (moi_s35_csrc t l av bv psi cc (bv e)) UNION
            IMAGE (moi_s35_ach ff av psi e) moi_s35_stube) SUBSET
    (w:real^N->real^3->bool) (bv e)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5A_FILL_SUB THEN
    EXISTS_TAC `UNIONS {IMAGE (moi_s35_ach (ff:real^N->real^N->real^3) av psi e')
                          moi_s35_stube | e' |
                        moi_s35_edge l e' /\
                        (bv:(real^N->bool)->real^N) e' = bv e}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
      ACCEPT_TAC(ASSUME moi_s5a_fill_hyp)];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `K:(real^3->bool)->bool`
    (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) o
    check (fun th -> is_exists(concl th) &&
      can (find_term ((=) `simplicial_complex:((real^3->bool)->bool)->bool`))
          (concl th))) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `Phi:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))) o
    check (is_exists o concl)) THEN
  MP_TAC MOI_S5A_US_FACTS THEN STRIP_TAC THEN
  MOI_S5A_MODEL_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
     `cc:(real^N->bool)->real`; `(bv:(real^N->bool)->real^N) e`]
     MOI_S5A_XX_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPEC `e:real^N->bool` (ASSUME
    `!e:real^N->bool. abs((cc:(real^N->bool)->real) e) <= &1 / &512`)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `pl_map_on moi_s35_dom
                  (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!s. s SUBSET moi_s35_dom /\ locally_polyhedral s
           ==> pl_map_on s (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)`)
      o concl)) THEN
    REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
    REWRITE_TAC[MOI_S5A_DOM_INTERVAL; POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_ball 3 (IMAGE ((ff:real^N->real^N->real^3) (av e))
                (moi_s35_csrc t l av bv psi cc ((av:(real^N->bool)->real^N) e))) /\
    pl_ball 3 (IMAGE ((ff:real^N->real^N->real^3) (bv e))
                (moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S5A_E45 THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
      `kk:real^N->real^N->bool`; `err:real^N->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open ((w:real^N->real^3->bool) ((bv:(real^N->bool)->real^N) e))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(bv:(real^N->bool)->real^N) e` o check
      (can (term_match []
        `!v. {v} IN l
             ==> open ((w:real^N->real^3->bool) v) /\
                 IMAGE (h:real^N->real^3) (derived_dual_cell t l v) SUBSET w v`)
        o concl)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
     `cc:(real^N->bool)->real`; `e:real^N->bool`] MOI_S5A_E7) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
     `e:real^N->bool`] MOI_S5A_C_E11) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(moi_s5a_cs [`e:real^N->bool`; `ff:real^N->real^N->real^3`;
     `err:real^N->real`; `cc:(real^N->bool)->real`] MOI_S5A_C_E12) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `xa = IMAGE ((ff:real^N->real^N->real^3) (av e))
                     (moi_s35_csrc t l av bv psi cc ((av:(real^N->bool)->real^N) e))` THEN
  ABBREV_TAC `xb = IMAGE ((ff:real^N->real^N->real^3) (bv e))
                     (moi_s35_csrc t l av bv psi cc ((bv:(real^N->bool)->real^N) e))` THEN
  ABBREV_TAC `phi = moi_s35_ach (ff:real^N->real^N->real^3) av psi e` THEN
  ABBREV_TAC `bb = moi_s35_bch (ff:real^N->real^N->real^3) bv psi e` THEN
  SUBGOAL_THEN
   `frontier xa INTER frontier xb SUBSET
    IMAGE (phi:real^3->real^3) (moi_s35_aflat ((cc:(real^N->bool)->real) e))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (phi:real^3->real^3)
                    {x | x IN moi_s35_level ((cc:(real^N->bool)->real) e) /\
                         moi_s35_n x < &5 / &16}` MP_TAC THENL
     [MP_TAC(ASSUME `frontier xa INTER xb SUBSET
                     IMAGE (phi:real^3->real^3)
                       {x | x IN moi_s35_level ((cc:(real^N->bool)->real) e) /\
                            moi_s35_n x < &5 / &16}`) THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `frontier (xb:real^3->bool) SUBSET xb`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; moi_s35_level] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[moi_s35_aflat; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ALL_TAC; UNDISCH_TAC `moi_s35_n z < &5 / &16` THEN
                    REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN interior xb` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
        `!z. z IN moi_s35_cube /\ moi_s35_n z <= &3 / &16 /\
             abs(z$3) <= &1 / &512 ==> (phi:real^3->real^3) z IN interior xb`)
        o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `abs((cc:(real^N->bool)->real) e) <= &1 / &512` THEN
      UNDISCH_TAC `moi_s35_n z < &3 / &16` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(y:real^3) IN frontier xb` THEN
      REWRITE_TAC[frontier; IN_DIFF] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (phi:real^3->real^3) (moi_s35_sq (&3 / &16) ((cc:(real^N->bool)->real) e))
    SUBSET interior xb`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; moi_s35_sq; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!z. z IN moi_s35_cube /\ moi_s35_n z <= &3 / &16 /\
           abs(z$3) <= &1 / &512 ==> (phi:real^3->real^3) z IN interior xb`)
      o concl)) THEN
    UNDISCH_TAC `abs((cc:(real^N->bool)->real) e) <= &1 / &512` THEN
    UNDISCH_TAC `moi_s35_n z = &3 / &16` THEN
    UNDISCH_TAC `(z:real^3)$3 = (cc:(real^N->bool)->real) e` THEN
    REWRITE_TAC MOI_S5A_MODEL_CONV_THMS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Q. {x | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN IMAGE bb moi_s35_bann /\
             Q x} =
        {x | x IN IMAGE (Phi:real^3->real^3) moi_s35_bann /\ Q x}`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ASSUME `{x | x IN moi_s35_dom /\
                        (phi:real^3->real^3) x IN IMAGE bb moi_s35_bann} =
                   IMAGE (Phi:real^3->real^3) moi_s35_bann`) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN moi_s35_bann ==> dist((Phi:real^3->real^3) z,z) < &1 / &1024`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (can (term_match []
      `!z. z IN moi_s35_bann ==> (Phi:real^3->real^3) z IN moi_s35_dom /\ P z`)
      o concl)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^3->real^3`; `(cc:(real^N->bool)->real) e`]
    MOI_S5A_COMP_LOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^3->real^3`; `(cc:(real^N->bool)->real) e`]
    MOI_S5A_COMP_HIGH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[moi_s35_edge_conf] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (phi:real^3->real^3) moi_s5a_us` THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC];
    REWRITE_TAC[ASSUME
     `!Q. {x | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN IMAGE bb moi_s35_bann /\
               Q x} =
          {x | x IN IMAGE (Phi:real^3->real^3) moi_s35_bann /\ Q x}`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[ASSUME
     `!Q. {x | x IN moi_s35_dom /\ (phi:real^3->real^3) x IN IMAGE bb moi_s35_bann /\
               Q x} =
          {x | x IN IMAGE (Phi:real^3->real^3) moi_s35_bann /\ Q x}`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC `K:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `simplicial_complex (K:(real^3->bool)->bool)` THEN
    SIMP_TAC[simplicial_complex]]);;


(* ------------------------------------------------------------------ *)
(* Assembly: context, error function, approximations (34.1 for        *)
(* cells), levels, the frame, and the main theorem APPROX.            *)
(* ------------------------------------------------------------------ *)

(* Assembly: the context from the hypotheses of APPROX, the error function,  *)
(* the approximations (34.1 for cells), and the levels.                       *)

let MOI_S5A_CTX_INTRO = prove
 (`!(t:(real^N->bool)->bool) l (h:real^N->real^3) w av bv psi.
     graph_in_complex t l /\ h continuous_on UNIONS t /\
     (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
     (!v. {v} IN l ==> open (w v) /\ IMAGE h (derived_dual_cell t l v) SUBSET w v) /\
     moi_s35_charts t l (\v. {x | x IN UNIONS t /\ h x IN w v}) av bv psi /\
     moi_s35_source_ok t l av bv psi
     ==> ?kk. moi_s5a_ctx t l h w av bv psi kk`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o REWRITE_RULE[moi_s35_source_ok]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `kk:real^N->real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[moi_s5a_ctx]);;

let MOI_S5A_ERR_CHOICE = prove
 (`!t l (h:real^N->real^3) w av bv psi kk eta rm rf d.
     moi_s5a_ctx t l h w av bv psi kk /\
     (!v. {v} IN l ==> &0 < eta v /\ &0 < rm v /\ &0 < rf v) /\
     (!e. moi_s35_edge l e ==> &0 < d e)
     ==> ?err. !v. {v} IN l
                   ==> &0 < err v /\ &3 * err v <= eta v /\ err v <= rm v /\
                       err v <= rf v /\
                       (!e. moi_s35_edge l e /\ (av e = v \/ bv e = v)
                            ==> err v <= d e / &2) /\
                       (!e. moi_s35_edge l e /\ av e = v ==> err v <= rf (bv e))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN
  X_GEN_TAC `v:real^N` THEN
  ASM_CASES_TAC `{v:real^N} IN l` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\(e:real^N->bool) (r:real).
                    (moi_s35_edge l e /\ (av e = v \/ bv e = v) ==> r <= d e / &2) /\
                    (moi_s35_edge l e /\ av e = (v:real^N) ==> r <= rf (bv e))`;
                 `moi_s5a_edges l (av:(real^N->bool)->real^N) bv v`]
    MOI_S5A_FINITE_POS_MIN) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `h:real^N->real^3`; `w:real^N->real^3->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `kk:real^N->real^N->bool`;
        `v:real^N`] MOI_S5A_EDGES_FINITE) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `e:real^N->bool` THEN
      REWRITE_TAC[moi_s5a_edges; IN_ELIM_THM] THEN
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
      MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      EXISTS_TAC `min (d (e:real^N->bool) / &2)
                      ((rf:real^N->real) ((bv:(real^N->bool)->real^N) e))` THEN
      SUBGOAL_THEN `&0 < (d:(real^N->bool)->real) e /\
                    &0 < (rf:real^N->real) ((bv:(real^N->bool)->real^N) e)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      MESON_TAC[REAL_LE_TRANS]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r (min ((eta:real^N->real) v / &3)
                         (min ((rm:real^N->real) v) ((rf:real^N->real) v)))` THEN
  SUBGOAL_THEN `&0 < (eta:real^N->real) v /\ &0 < (rm:real^N->real) v /\
                &0 < (rf:real^N->real) v` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `e:real^N->bool` THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (can (term_match []
      `!x. x IN moi_s5a_edges l (av:(real^N->bool)->real^N) bv v ==> P x`) o concl))
    THEN ASM_REWRITE_TAC[moi_s5a_edges; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    X_GEN_TAC `e:real^N->bool` THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (can (term_match []
      `!x. x IN moi_s5a_edges l (av:(real^N->bool)->real^N) bv v ==> P x`) o concl))
    THEN ASM_REWRITE_TAC[moi_s5a_edges; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let MOI_S5A_FF_CHOICE = prove
 (mk_imp(mk_conj(`MOISE_341_STATEMENT`, MOI_S35_CELL_341),
  `!t l (h:real^N->real^3) w av bv psi kk err.
     moi_s5a_ctx t l h w av bv psi kk /\ (!v. {v} IN l ==> &0 < err v)
     ==> ?ff. moi_s5a_apx t l av bv psi h ff err`),
  DISCH_THEN(fun th -> LABEL_TAC "c341" (MP (CONJUNCT2 th) (CONJUNCT1 th))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  REWRITE_TAC[moi_s5a_apx; GSYM SKOLEM_THM] THEN X_GEN_TAC `v:real^N` THEN
  ASM_CASES_TAC `{v:real^N} IN l` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_SOURCE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `bs:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(moi_s5a_cs [`v:real^N`] MOI_S5A_CPLUS_UNIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "c341" (MP_TAC o ISPECL
    [`moi_s35_cplus t l av bv psi (v:real^N)`; `bs:real^N->bool`;
     `h:real^N->real^3`; `(err:real^N->real) v`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool`
      THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S5A_INJ_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool`
      THEN ASM_REWRITE_TAC[]];
    MESON_TAC[]]);;

let MOI_S5A_TRI_EXISTS = prove
 (`!t l (h:real^N->real^3) w av bv psi kk ff err e (Phi:real^3->real^3) g.
     moi_s5a_ctx t l h w av bv psi kk /\ moi_s5a_apx t l av bv psi h ff err /\
     moi_s35_edge l e /\
     homeomorphism (moi_s35_dom,IMAGE (moi_s35_ach ff av psi e) moi_s35_dom)
                   (moi_s35_ach ff av psi e,g) /\
     IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann SUBSET
     IMAGE (moi_s35_ach ff av psi e) moi_s35_dom /\
     Phi = g o moi_s35_bch ff bv psi e /\
     {x | x IN moi_s35_dom /\
          moi_s35_ach ff av psi e x IN IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann} =
     IMAGE Phi moi_s35_bann
     ==> ?k. simplicial_complex k /\
             UNIONS k = {x | x IN moi_s35_dom /\
                             moi_s35_ach ff av psi e x IN
                             IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ASM_REWRITE_TAC[] THEN
  MOI_S5A_MODEL_TAC THEN
  MP_TAC(moi_s5a_cs [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                     `e:real^N->bool`] MOI_S5A_CHART_MAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC MOI_S5A_BANN_POLY THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S5A_E20_TRI THEN
  EXISTS_TAC `moi_s35_ach (ff:real^N->real^N->real^3) av psi e` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!s. s SUBSET moi_s35_dom /\ locally_polyhedral s
           ==> pl_map_on s (moi_s35_ach (ff:real^N->real^N->real^3) av psi e)`)
      o concl)) THEN
    REWRITE_TAC[SUBSET_REFL] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
    REWRITE_TAC[MOI_S5A_DOM_INTERVAL; POLYTOPE_INTERVAL];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
      `!s. s SUBSET moi_s35_bcell UNION moi_s35_upper /\ locally_polyhedral s
           ==> pl_map_on s (moi_s35_bch (ff:real^N->real^N->real^3) bv psi e)`)
      o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s35_bann SUBSET moi_s35_bcell INTER moi_s35_slab` THEN
    SET_TAC[]]);;

let MOI_S5A_CC_CHOICE = prove
 (`!l (S:(real^N->bool)->real^3->bool).
     (!e. moi_s35_edge l e ==> ?k. simplicial_complex k /\ UNIONS k = S e)
     ==> ?cc. (!e. abs(cc e) <= &1 / &512) /\
              (!e. moi_s35_edge l e
                   ==> ?k. simplicial_complex k /\ UNIONS k = S e /\
                           !v. {v} IN k ==> ~(v$3 = cc e))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!e. ?c. abs c <= &1 / &512 /\
            (moi_s35_edge l e
             ==> ?k. simplicial_complex k /\
                     UNIONS k = (S:(real^N->bool)->real^3->bool) e /\
                     !v. {v} IN k ==> ~(v$3 = c))`
  MP_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN ASM_CASES_TAC `moi_s35_edge l (e:real^N->bool)`
    THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `{v$3 | v | {v:real^3} IN k}` MOI_S5A_AVOID_FINITE) THEN
      ANTS_TAC THENL [MATCH_MP_TAC MOI_S5A_VERT_FINITE THEN ASM_REWRITE_TAC[];
                      ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `k:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      UNDISCH_TAC `~(c IN {v$3 | v | {v:real^3} IN k})` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      EXISTS_TAC `&0` THEN REAL_ARITH_TAC];
    REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]]);;

let MOI_S5A_UNION3_SUB = prove
 (`!a b c w:real^3->bool. a UNION b UNION c SUBSET w ==> a SUBSET w`,
  SET_TAC[]);;

let moi_s5a_fill_v =
 `IMAGE ((ff:real^N->real^N->real^3) v) (moi_s35_csrc t l av bv psi cc v) UNION
  UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e |
          moi_s35_edge l e /\ (bv:(real^N->bool)->real^N) e = v} UNION
  inside (IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v) UNION
          UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e |
                  moi_s35_edge l e /\ bv e = v})
  SUBSET (w:real^N->real^3->bool) v`;;

let moi_s5a_fill_all = mk_forall(`v:real^N`, mk_imp(`{v:real^N} IN l`, moi_s5a_fill_v));;

let moi_s5a_mark_all =
 `!v. {v} IN l
      ==> IMAGE (h:real^N->real^3) ((kk:real^N->real^N->bool) v) SUBSET
          interior (IMAGE ((ff:real^N->real^N->real^3) v)
                      (moi_s35_csrc t l av bv psi (\e. --(&1 / &512)) v))`;;

let moi_s5a_body_all =
  mk_forall(`e:real^N->bool`, mk_imp(`moi_s35_edge l (e:real^N->bool)`,
                                     moi_s5a_edge_body));;

let MOI_S5A_FRAME_ALL = prove
 (list_mk_forall(moi_s5a_ctxl @ [`eta:real^N->real`; `ff:real^N->real^N->real^3`;
                                 `err:real^N->real`; `cc:(real^N->bool)->real`],
   mk_imp(list_mk_conj
    [`moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`;
     `moi_s5a_etaok t l (h:real^N->real^3) av bv psi kk eta`;
     `!u. {u} IN l ==> &3 * (err:real^N->real) u <= eta u`;
     `moi_s5a_apx t l av bv psi (h:real^N->real^3) ff err`;
     `!e:real^N->bool. abs((cc:(real^N->bool)->real) e) <= &1 / &512`;
     moi_s5a_fill_all; moi_s5a_mark_all; moi_s5a_body_all],
    `moi_s35_frame t l (h:real^N->real^3) w av bv psi ff
       (\v. IMAGE ((ff:real^N->real^N->real^3) v)
                  (moi_s35_csrc t l av bv psi cc v)) cc`)),
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(moi_s5a_cs [`eta:real^N->real`; `ff:real^N->real^N->real^3`;
                     `err:real^N->real`; `cc:(real^N->bool)->real`]
    MOI_S5A_FRAME_SEP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  REWRITE_TAC[moi_s35_frame] THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
      `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
      `ff:real^N->real^N->real^3`; `err:real^N->real`;
      `v:real^N`] MOI_S5A_APX_AT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(MP (SPEC `v:real^N` (ASSUME moi_s5a_fill_all)) (ASSUME `{v:real^N} IN l`))
    THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5A_E45 THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `w:real^N->real^3->bool`;
        `kk:real^N->real^N->bool`; `err:real^N->real`] THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP MOI_S5A_UNION3_SUB)];
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(MP (SPEC `e:real^N->bool` (ASSUME moi_s5a_body_all))
              (ASSUME `moi_s35_edge l (e:real^N->bool)`)) THEN
    DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?v:real^N. {v} IN l /\ p IN (kk:real^N->real^N->bool) v`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS l SUBSET UNIONS {(kk:real^N->real^N->bool) v | v | {v} IN l}`
      THEN UNDISCH_TAC `(p:real^N) IN UNIONS l` THEN
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s. (x:real^3) IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `interior (IMAGE ((ff:real^N->real^N->real^3) v)
                    (moi_s35_csrc t l av bv psi (\e. --(&1 / &512)) v))` THEN
      CONJ_TAC THENL
       [MP_TAC(MP (SPEC `v:real^N` (ASSUME moi_s5a_mark_all))
                  (ASSUME `{v:real^N} IN l`)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        MATCH_MP_TAC MOI_S5A_CSRC_MONO THEN GEN_TAC THEN BETA_TAC THEN
        MP_TAC(SPEC `e:real^N->bool` (ASSUME
          `!e:real^N->bool. abs((cc:(real^N->bool)->real) e) <= &1 / &512`)) THEN
        REAL_ARITH_TAC];
      X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N`; `e:real^N->bool`] o check
        (can (term_match []
          `!v e. {v} IN l /\ moi_s35_edge l e
                 ==> DISJOINT (IMAGE (h:real^N->real^3) ((kk:real^N->real^N->bool) v)) X`)
          o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE]]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem APPROX (Moise 35.1, conditions (2)-(8), pp.249-250).      *)
(* ------------------------------------------------------------------------- *)

let moi_s5a_body_gen =
  list_mk_forall([`e:real^N->bool`; `cc:(real^N->bool)->real`],
    mk_imp(`moi_s35_edge l (e:real^N->bool) /\
            (!e:real^N->bool. abs((cc:(real^N->bool)->real) e) <= &1 / &512)`,
           moi_s5a_edge_body));;

let APPROX = prove
 (MOI_S35_APPROX,
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
    `h:real^N->real^3`; `w:real^N->real^3->bool`;
    `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
    `psi:(real^N->bool)->real^3->real^N`] MOI_S5A_CTX_INTRO) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `kk:real^N->real^N->bool`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5A_CTX_BASIC) THEN
  MP_TAC(moi_s5a_cs [] MOI_S5A_ETA_EXISTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `eta:real^N->real`) THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
   (REWRITE_RULE[ASSUME `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`]
     (moi_s5a_cs [] (MP MOI_S5A_MARK_V (ASSUME MOI_S35_MARKER))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `rm:real^N->real` (LABEL_TAC "rm")) THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
   (REWRITE_RULE[ASSUME `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`]
     (moi_s5a_cs [] (MP MOI_S5A_FILL_V (ASSUME MOI_S35_FILL))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `rf:real^N->real` (LABEL_TAC "rf")) THEN
  MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]
   (REWRITE_RULE[ASSUME `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`]
     (moi_s5a_cs [] (MP MOI_S5A_EDGE_GOOD
       (CONJ (ASSUME MOI_S35_MARKER)
             (CONJ (ASSUME MOI_S35_LOCAL_SIGN) (ASSUME MOI_S35_CLOSE_SIGN))))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->real` (LABEL_TAC "dg")) THEN
  MP_TAC(moi_s5a_cs [`eta:real^N->real`; `rm:real^N->real`; `rf:real^N->real`;
                     `d:(real^N->bool)->real`] MOI_S5A_ERR_CHOICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `moi_s5a_etaok t l (h:real^N->real^3) av bv psi kk eta` THEN
        REWRITE_TAC[moi_s5a_etaok] THEN DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
        USE_THEN "rm" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
        USE_THEN "rf" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]];
      X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "dg" (MP_TAC o SPEC `e:real^N->bool`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `err:real^N->real` (LABEL_TAC "err"))] THEN
  MP_TAC(moi_s5a_cs [`err:real^N->real`]
    (MP MOI_S5A_FF_CHOICE (CONJ (ASSUME `MOISE_341_STATEMENT`)
                                (ASSUME MOI_S35_CELL_341)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "err" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `ff:real^N->real^N->real^3`)] THEN
  SUBGOAL_THEN moi_s5a_body_gen (LABEL_TAC "body") THENL
   [MAP_EVERY X_GEN_TAC [`e:real^N->bool`; `cc:(real^N->bool)->real`] THEN
    STRIP_TAC THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "dg" (MP_TAC o SPEC `e:real^N->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[moi_s5a_good] THEN
    DISCH_THEN(MP_TAC o SPECL [`ff:real^N->real^N->real^3`; `err:real^N->real`;
                               `cc:(real^N->bool)->real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "err" (MP_TAC o SPEC `(av:(real^N->bool)->real^N) e`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT2 o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "err" (MP_TAC o SPEC `(bv:(real^N->bool)->real^N) e`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT2 o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      UNDISCH_TAC `(err:real^N->real) ((av:(real^N->bool)->real^N) e) <=
                   (d:(real^N->bool)->real) e / &2` THEN
      UNDISCH_TAC `(err:real^N->real) ((bv:(real^N->bool)->real^N) e) <=
                   (d:(real^N->bool)->real) e / &2` THEN
      REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`;
    `\e. {x | x IN moi_s35_dom /\
              moi_s35_ach (ff:real^N->real^N->real^3) av psi e x IN
              IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann}`] MOI_S5A_CC_CHOICE) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN BETA_TAC THEN
    USE_THEN "body" (MP_TAC o SPECL [`e:real^N->bool`;
                                     `\e:real^N->bool. &0`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_S5A_TRI_EXISTS THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^3`;
      `w:real^N->real^3->bool`; `kk:real^N->real^N->bool`; `err:real^N->real`;
      `Phi:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `cc:(real^N->bool)->real`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cct")))] THEN
  MAP_EVERY EXISTS_TAC
   [`ff:real^N->real^N->real^3`;
    `\v. IMAGE ((ff:real^N->real^N->real^3) v) (moi_s35_csrc t l av bv psi cc v)`;
    `cc:(real^N->bool)->real`] THEN
  SUBGOAL_THEN moi_s5a_fill_all ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5A_F1E THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `kk:real^N->real^N->bool`;
      `err:real^N->real`; `(rf:real^N->real) v`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rf" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      USE_THEN "err" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      X_GEN_TAC `e:real^N->bool` THEN
      DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
      MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "err" (MP_TAC o SPEC `(av:(real^N->bool)->real^N) e`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT2 o CONJUNCT2 o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (can (term_match []
        `(bv:(real^N->bool)->real^N) e = v`) o concl)) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s35_pre] THEN BETA_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5A_FRAME_ALL THEN
    MAP_EVERY EXISTS_TAC [`kk:real^N->real^N->bool`; `eta:real^N->real`;
                          `err:real^N->real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
      USE_THEN "err" (MP_TAC o SPEC `u:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      USE_THEN "rm" (MP_TAC o SPEC `v:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
        `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
        `psi:(real^N->bool)->real^3->real^N`; `h:real^N->real^3`;
        `ff:real^N->real^N->real^3`; `err:real^N->real`;
        `v:real^N`] MOI_S5A_APX_AT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `(err:real^N->real) v` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (can (term_match []
          `!x. x IN moi_s35_cplus t l av bv psi v
               ==> dist((ff:real^N->real^N->real^3) v x,(h:real^N->real^3) x) <
                   err v`) o concl)) THEN
        FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "err" (MP_TAC o SPEC `v:real^N`) THEN
        ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]];
      X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
      ACCEPT_TAC(MP (SPECL [`e:real^N->bool`; `cc:(real^N->bool)->real`]
                     (ASSUME moi_s5a_body_gen))
                    (CONJ (ASSUME `moi_s35_edge l (e:real^N->bool)`)
                          (ASSUME `!e:real^N->bool.
                                     abs((cc:(real^N->bool)->real) e) <=
                                     &1 / &512`)))];
    X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S5A_PRE_EDGE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `kk:real^N->real^N->bool`;
                          `err:real^N->real`] THEN
    MP_TAC(moi_s5a_cs [`e:real^N->bool`] MOI_S5A_EDGE_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "cct" (fun cct -> ACCEPT_TAC(end_itlist CONJ
     [ASSUME `moi_s5a_ctx t l (h:real^N->real^3) w av bv psi kk`;
      ASSUME `moi_s5a_apx t l av bv psi (h:real^N->real^3) ff err`;
      ASSUME `!e:real^N->bool. abs((cc:(real^N->bool)->real) e) <= &1 / &512`;
      ASSUME `moi_s35_edge l (e:real^N->bool)`;
      MP (SPECL [`e:real^N->bool`; `cc:(real^N->bool)->real`]
           (ASSUME moi_s5a_body_gen))
         (CONJ (ASSUME `moi_s35_edge l (e:real^N->bool)`)
               (ASSUME `!e:real^N->bool.
                          abs((cc:(real^N->bool)->real) e) <= &1 / &512`));
      MP (SPEC `(bv:(real^N->bool)->real^N) e` (ASSUME moi_s5a_fill_all))
         (ASSUME `{(bv:(real^N->bool)->real^N) e} IN l`);
      MP (SPEC `e:real^N->bool` cct) (ASSUME `moi_s35_edge l (e:real^N->bool)`)]))]);;


