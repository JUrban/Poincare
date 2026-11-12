(* ========================================================================= *)
(* pc_moi_s26_surf: two triangulated surfaces glued along common boundary    *)
(* components form a triangulated surface (Moise GTM 47, 26.7 proof p.195;   *)
(* the annulus unions of 28.6), SURF_GLUE : |- MOI_S26_SURF_GLUE; the        *)
(* interior of a connected surface with boundary is connected,               *)
(* INT_CONNECTED : |- MOI_S26_INT_CONNECTED.  Route: charts.  Off the common *)
(* boundary the charts of the two surfaces are charts of the union; at a     *)
(* common boundary point two half charts glue to a planar chart              *)
(* (MOI_S6G_HALF_GLUE); a triangulation of the union is then a surface by    *)
(* SURF_LOCAL (pc_moi_s28_trib); the Euler characteristic adds since the     *)
(* common part is a union of circles (valuations).                           *)
(* ========================================================================= *)

needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_s28_cut.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Gluing two half-plane charts along their boundary lines.                 *)
(* If two closed sets x1, x2 have half charts h1, h2 at y (onto the closed  *)
(* upper half plane, y at the origin) and near y each one meets the other   *)
(* exactly in the boundary line of its chart, then y has a planar chart in  *)
(* x1 UNION x2: h1^-1 on the upper half, h2^-1 after the boundary transition *)
(* (s,t) |-> (beta s,t) and the reflection on the lower half.               *)
(* ------------------------------------------------------------------------- *)

let MOI_S6G_CONT_NBHD = prove
 (`!(f:real^M->real^N) s a v.
     f continuous_on s /\ a IN s /\ open v /\ f a IN v
     ==> ?r. &0 < r /\ !z. z IN s /\ norm(z - a) < r ==> f z IN v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^M->real^N) a` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(f:real^M->real^N) continuous_on s` THEN REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[dist]);;

let MOI_S6G_OPEN_IN_UNION_CLOSED = prove
 (`!(x1:real^N->bool) x2 n.
     closed x1 /\ closed x2 /\ n SUBSET x1 UNION x2 /\
     open_in (subtopology euclidean x1) (n INTER x1) /\
     open_in (subtopology euclidean x2) (n INTER x2)
     ==> open_in (subtopology euclidean (x1 UNION x2)) n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `g1:real^N->bool` STRIP_ASSUME_TAC)
                     (X_CHOOSE_THEN `g2:real^N->bool` STRIP_ASSUME_TAC))))) THEN
  EXISTS_TAC `(:real^N) DIFF ((x1 DIFF g1) UNION (x2 DIFF g2))` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNION THEN
    ASM_SIMP_TAC[CLOSED_DIFF];
    ASM SET_TAC[]]);;

let MOI_S6G_HALF_SUPER = prove
 (`!(x:real^N->bool) x' y.
     moi_s28_locally_half x' y /\ open_in (subtopology euclidean x) x'
     ==> moi_s28_locally_half x y`,
  REWRITE_TAC[moi_s28_locally_half] THEN MESON_TAC[OPEN_IN_TRANS]);;

let MOI_S6G_REFL = prove
 (`!z:real^2.
     (z$1 % basis 1 - z$2 % basis 2:real^2)$1 = z$1 /\
     (z$1 % basis 1 - z$2 % basis 2:real^2)$2 = --(z$2) /\
     norm(z$1 % basis 1 - z$2 % basis 2:real^2) = norm z /\
     (z$1 % basis 1 - z$2 % basis 2:real^2)$1 % basis 1 -
     (z$1 % basis 1 - z$2 % basis 2:real^2)$2 % basis 2 = z`,
  GEN_TAC THEN
  SUBGOAL_THEN `((z:real^2)$1 % basis 1 - z$2 % basis 2:real^2)$1 = z$1 /\
                ((z:real^2)$1 % basis 1 - z$2 % basis 2:real^2)$2 = --(z$2)` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[NORM_EQ; DOT_2] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The half-chart gluing lemma MOI_S6G_HALF_GLUE.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S6G_HALF_GLUE = prove
 (`!(x1:real^N->bool) x2 y u1 (h1:real^N->real^2) k1 u2 (h2:real^N->real^2) k2 oo.
     closed x1 /\ closed x2 /\
     open_in (subtopology euclidean x1) u1 /\ y IN u1 /\
     homeomorphism (u1,{z:real^2 | &0 <= z$2}) (h1,k1) /\ h1 y = vec 0 /\
     open_in (subtopology euclidean x2) u2 /\ y IN u2 /\
     homeomorphism (u2,{z:real^2 | &0 <= z$2}) (h2,k2) /\ h2 y = vec 0 /\
     open oo /\ y IN oo /\
     (!p. p IN u1 /\ p IN oo ==> (p IN x2 <=> (h1 p)$2 = &0)) /\
     (!p. p IN u2 /\ p IN oo ==> (p IN x1 <=> (h2 p)$2 = &0))
     ==> moi_s28_locally_r2 (x1 UNION x2) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    aconv (concl th) `homeomorphism (u1,{z:real^2 | &0 <= z$2}) (h1:real^N->real^2,k1)`)) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    aconv (concl th) `homeomorphism (u2,{z:real^2 | &0 <= z$2}) (h2:real^N->real^2,k2)`)) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g1:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) o
    GEN_REWRITE_RULE I [OPEN_IN_OPEN] o check (fun th ->
    aconv (concl th) `open_in (subtopology euclidean x1) (u1:real^N->bool)`)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g2:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) o
    GEN_REWRITE_RULE I [OPEN_IN_OPEN] o check (fun th ->
    aconv (concl th) `open_in (subtopology euclidean x2) (u2:real^N->bool)`)) THEN
  SUBGOAL_THEN `(!z:real^2. &0 <= z$2 ==> (k1:real^2->real^N) z IN u1) /\
                (!z:real^2. &0 <= z$2 ==> (k2:real^2->real^N) z IN u2) /\
                (!p. p IN u1 ==> &0 <= ((h1:real^N->real^2) p)$2) /\
                (!p. p IN u2 ==> &0 <= ((h2:real^N->real^2) p)$2) /\
                (k1:real^2->real^N) (vec 0) = y /\ (k2:real^2->real^N) (vec 0) = y /\
                (y:real^N) IN g1 /\ y IN g2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]; ASM SET_TAC[]; ASM SET_TAC[];
      ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  (* radius for k1: k1 maps a half disk into o INTER g2 *)
  MP_TAC(ISPECL [`k1:real^2->real^N`; `{z:real^2 | &0 <= z$2}`; `vec 0:real^2`;
                 `oo INTER g2:real^N->bool`] MOI_S6G_CONT_NBHD) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; VEC_COMPONENT; REAL_LE_REFL; OPEN_INTER; IN_INTER] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k2:real^2->real^N`; `{z:real^2 | &0 <= z$2}`; `vec 0:real^2`;
                 `oo INTER g1:real^N->bool`] MOI_S6G_CONT_NBHD) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; VEC_COMPONENT; REAL_LE_REFL; OPEN_INTER; IN_INTER] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  (* the boundary points k1 (s,0) near y lie in u2 and h2 maps them to the axis *)
  SUBGOAL_THEN
   `!s. abs s < r1
        ==> (k1:real^2->real^N) (s % basis 1) IN u1 /\ k1 (s % basis 1) IN u2 /\
            k1 (s % basis 1) IN oo /\
            (h2:real^N->real^2) (k1 (s % basis 1)) =
            ((h2 (k1 (s % basis 1)))$1) % basis 1`
  (LABEL_TAC "bt") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (s % basis 1:real^2)$2 /\ norm(s % basis 1:real^2) < r1 /\
                  (s % basis 1:real^2)$2 = &0` STRIP_ASSUME_TAC THENL
     [SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH; NORM_MUL;
               NORM_BASIS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `q = (k1:real^2->real^N) (s % basis 1)` THEN
    SUBGOAL_THEN `(q:real^N) IN u1 /\ q IN oo /\ q IN g2 /\
                  ((h1:real^N->real^2) q)$2 = &0` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "q" THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^N) IN x2 /\ q IN x1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]; ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^N) IN u2` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((h2:real^N->real^2) q)$2 = &0` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the boundary transition is injective *)
  SUBGOAL_THEN
   `!s t. abs s < r1 /\ abs t < r1 /\
          ((h2:real^N->real^2) ((k1:real^2->real^N) (s % basis 1)))$1 =
          (h2 (k1 (t % basis 1)))$1
          ==> s = t`
  (LABEL_TAC "btinj") THENL
   [MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "bt" (fun th -> MP_TAC(SPEC `t:real` th) THEN MP_TAC(SPEC `s:real` th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(h2:real^N->real^2) ((k1:real^2->real^N) (s % basis 1)) =
                  h2 (k1 (t % basis 1))` ASSUME_TAC THENL
     [MAP_EVERY (fun t -> FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq (concl th) && lhand (concl th) = t)))
       [`(h2:real^N->real^2) ((k1:real^2->real^N) (s % basis 1))`;
        `(h2:real^N->real^2) ((k1:real^2->real^N) (t % basis 1))`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(k1:real^2->real^N) (s % basis 1) = k1 (t % basis 1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s % basis 1:real^2 = t % basis 1` MP_TAC THENL
     [SUBGOAL_THEN `&0 <= (s % basis 1:real^2)$2 /\ &0 <= (t % basis 1:real^2)$2`
      STRIP_ASSUME_TAC THENL
       [SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
        ASM_MESON_TAC[]];
      SIMP_TAC[VECTOR_MUL_RCANCEL; BASIS_NONZERO; DIMINDEX_2; ARITH]];
    ALL_TAC] THEN
  (* the transition map ph (s,t) = (beta s,t) on the strip ss *)
  ABBREV_TAC `ph = \z:real^2. ((h2:real^N->real^2) ((k1:real^2->real^N) (z$1 % basis 1)))$1 %
                              basis 1 + z$2 % basis 2:real^2` THEN
  SUBGOAL_THEN `!z:real^2. ((ph:real^2->real^2) z)$1 =
                           ((h2:real^N->real^2) ((k1:real^2->real^N) (z$1 % basis 1)))$1 /\
                           (ph z)$2 = z$2` (LABEL_TAC "phc") THENL
   [EXPAND_TAC "ph" THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `ss = {z:real^2 | abs(z$1) < r1}` THEN
  SUBGOAL_THEN `open (ss:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `ss = {z:real^2 | z$1 > --r1} INTER {z | z$1 < r1}` SUBST1_TAC THENL
     [EXPAND_TAC "ss" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN REAL_ARITH_TAC;
      SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_COMPONENT_GT; OPEN_HALFSPACE_COMPONENT_LT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ph:real^2->real^2) continuous_on ss` ASSUME_TAC THENL
   [EXPAND_TAC "ph" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
      SUBGOAL_THEN
       `(lift o (\z:real^2. ((h2:real^N->real^2) ((k1:real^2->real^N) (z$1 % basis 1)))$1)) =
        (\w:real^2. lift(w$1)) o (h2 o (k1 o (\z:real^2. z$1 % basis 1:real^2)))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
            SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
            MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | &0 <= z$2}` THEN
            ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
            SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
            REAL_ARITH_TAC];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u2:real^N->bool` THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
          EXPAND_TAC "ss" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
          DISCH_TAC THEN USE_THEN "bt" (MP_TAC o SPEC `(z:real^2)$1`) THEN
          ASM_SIMP_TAC[]];
        SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH]];
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z w:real^2. z IN ss /\ w IN ss /\ (ph:real^2->real^2) z = ph w ==> z = w`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:real^2`; `w:real^2`] THEN EXPAND_TAC "ss" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> MP_TAC(AP_TERM `\v:real^2. v$1` th) THEN
                         MP_TAC(AP_TERM `\v:real^2. v$2` th)) THEN
    REWRITE_TAC[] THEN USE_THEN "phc" (fun th -> REWRITE_TAC[th]) THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "btinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ph:real^2->real^2`; `ss:real^2->bool`] INVARIANCE_OF_DOMAIN_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `ph':real^2->real^2` ASSUME_TAC) THEN
  SUBGOAL_THEN `(vec 0:real^2) IN ss /\ (ph:real^2->real^2) (vec 0) = vec 0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT; REAL_ABS_0] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    USE_THEN "phc" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[VEC_COMPONENT; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ph:real^2->real^2`; `ss:real^2->bool`; `vec 0:real^2`;
                 `ball(vec 0:real^2,r2)`] MOI_S6G_CONT_NBHD) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; VECTOR_SUB_RZERO; IN_BALL_0; NORM_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `r3:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min r1 r3` THEN
  SUBGOAL_THEN `&0 < r /\ r <= r1 /\ r <= r3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `ww = ball(vec 0:real^2,r)` THEN
  SUBGOAL_THEN `!z:real^2. z IN ww ==> z IN ss /\ norm z < r1 /\ norm z < r3 /\ norm z < r`
  (LABEL_TAC "inww") THENL
   [X_GEN_TAC `z:real^2` THEN EXPAND_TAC "ww" THEN EXPAND_TAC "ss" THEN
    REWRITE_TAC[IN_BALL_0; IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`z:real^2`; `1`] COMPONENT_LE_NORM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `rf = \z:real^2. z$1 % basis 1 - z$2 % basis 2:real^2` THEN
  SUBGOAL_THEN `!z:real^2. ((rf:real^2->real^2) z)$1 = z$1 /\ (rf z)$2 = --(z$2) /\
                           norm(rf z) = norm z /\ rf (rf z) = z` (LABEL_TAC "rfc") THENL
   [EXPAND_TAC "rf" THEN REWRITE_TAC[MOI_S6G_REFL]; ALL_TAC] THEN
  (* the three kinds of points of the glued chart *)
  SUBGOAL_THEN
   `!z:real^2. z IN ww /\ &0 <= z$2
               ==> (k1:real^2->real^N) z IN u1 /\ k1 z IN oo /\ (h1:real^N->real^2) (k1 z) = z`
  (LABEL_TAC "up") THENL
   [X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN USE_THEN "inww" (MP_TAC o SPEC `z:real^2`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^2. z IN ww /\ z$2 < &0
               ==> (rf:real^2->real^2) z IN ww /\ rf z IN ss /\
                   &0 < ((ph:real^2->real^2) (rf z))$2 /\
                   (k2:real^2->real^N) (ph (rf z)) IN u2 /\ k2 (ph (rf z)) IN oo /\
                   ~(k2 (ph (rf z)) IN x1) /\
                   (h2:real^N->real^2) (k2 (ph (rf z))) = ph (rf z)`
  (LABEL_TAC "down") THENL
   [X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(rf:real^2->real^2) z IN ww` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^2) IN ww` THEN EXPAND_TAC "ww" THEN REWRITE_TAC[IN_BALL_0] THEN
      USE_THEN "rfc" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    USE_THEN "inww" (MP_TAC o SPEC `(rf:real^2->real^2) z`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < ((ph:real^2->real^2) ((rf:real^2->real^2) z))$2` ASSUME_TAC THENL
     [USE_THEN "phc" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "rfc" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm((ph:real^2->real^2) ((rf:real^2->real^2) z)) < r2` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `r3:real`)) (concl th) &&
        is_forall (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) z)) IN u2 /\
                  k2 (ph (rf z)) IN oo /\
                  (h2:real^N->real^2) (k2 (ph (rf z))) = ph (rf z)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(((h2:real^N->real^2) ((k2:real^2->real^N) ((ph:real^2->real^2)
                    ((rf:real^2->real^2) z))))$2 = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^2. z IN ww /\ z$2 = &0
               ==> (ph:real^2->real^2) z = (h2:real^N->real^2) ((k1:real^2->real^N) z) /\
                   (k2:real^2->real^N) (ph z) = k1 z /\ (rf:real^2->real^2) z = z /\
                   k1 z IN u2`
  (LABEL_TAC "axis") THENL
   [X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    USE_THEN "inww" (MP_TAC o SPEC `z:real^2`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `?s0. z:real^2 = s0 % basis 1 /\ abs s0 < r1`
    (X_CHOOSE_THEN `s0:real` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [EXISTS_TAC `(z:real^2)$1` THEN CONJ_TAC THENL
       [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
        SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `(z:real^2) IN ss` THEN EXPAND_TAC "ss" THEN REWRITE_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    USE_THEN "bt" (MP_TAC o SPEC `s0:real`) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
    SUBGOAL_THEN `(ph:real^2->real^2) (s0 % basis 1) =
                  (h2:real^N->real^2) ((k1:real^2->real^N) (s0 % basis 1))` ASSUME_TAC THENL
     [EXPAND_TAC "ph" THEN REWRITE_TAC[] THEN
      SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH; REAL_MUL_RID;
               REAL_MUL_RZERO] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      EXPAND_TAC "rf" THEN REWRITE_TAC[] THEN
      SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH; REAL_MUL_RID;
               REAL_MUL_RZERO] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO]];
    ALL_TAC] THEN
  (* the glued map gg on the ball ww and its basic properties *)
  ABBREV_TAC `gg = \z:real^2. if &0 <= z$2 then (k1:real^2->real^N) z
                              else (k2:real^2->real^N) ((ph:real^2->real^2)
                                     ((rf:real^2->real^2) z))` THEN
  SUBGOAL_THEN `!z:real^2. (gg:real^2->real^N) z =
                           if &0 <= z$2 then (k1:real^2->real^N) z
                           else (k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) z))`
  (LABEL_TAC "ggdef") THENL [EXPAND_TAC "gg" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x1:real^N->bool) INTER g1 = u1 ==> u1 SUBSET x1` MP_TAC THENL
   [SET_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `(x2:real^N->bool) INTER g2 = u2 ==> u2 SUBSET x2` MP_TAC THENL
   [SET_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  (* continuity of gg *)
  SUBGOAL_THEN `(gg:real^2->real^N) continuous_on ww` ASSUME_TAC THENL
   [SUBGOAL_THEN `(ww INTER {z:real^2 | &0 <= z$2}) UNION (ww INTER {z | z$2 <= &0}) = ww`
    (fun th -> MP_TAC(ISPECL [`\z:real^2. &0 <= z$2`; `k1:real^2->real^N`;
                   `\z:real^2. (k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) z))`;
                   `ww INTER {z:real^2 | &0 <= z$2}`; `ww INTER {z:real^2 | z$2 <= &0}`]
      CONTINUOUS_ON_CASES_LOCAL) THEN REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM] THEN MESON_TAC[REAL_LE_TOTAL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x:real^2. if &0 <= x$2 then (k1:real^2->real^N) x
                              else (k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) x))) = gg`
    SUBST1_TAC THENL [EXPAND_TAC "gg" THEN REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
      REWRITE_TAC[REWRITE_RULE[real_ge] CLOSED_HALFSPACE_COMPONENT_GE];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | &0 <= z$2}` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `(\z:real^2. (k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) z))) =
                    k2 o (ph o rf)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [EXPAND_TAC "rf" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
          MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
          SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ss:real^2->bool` THEN
          ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
          X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
          USE_THEN "inww" (MP_TAC o SPEC `(rf:real^2->real^2) z`) THEN
          ANTS_TAC THENL
           [UNDISCH_TAC `(z:real^2) IN ww` THEN EXPAND_TAC "ww" THEN REWRITE_TAC[IN_BALL_0] THEN
            USE_THEN "rfc" (fun th -> REWRITE_TAC[th]);
            SIMP_TAC[]]];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | &0 <= z$2}` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM; o_THM] THEN
        USE_THEN "phc" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "rfc" (fun th -> REWRITE_TAC[th]) THEN
        REAL_ARITH_TAC];
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^2` THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "axis" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* gg is injective on ww *)
  SUBGOAL_THEN `!z w:real^2. z IN ww /\ w IN ww /\ (gg:real^2->real^N) z = gg w ==> z = w`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`z:real^2`; `w:real^2`] THEN
    USE_THEN "ggdef" (fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `&0 <= (z:real^2)$2` THEN ASM_CASES_TAC `&0 <= (w:real^2)$2` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [USE_THEN "up" (MP_TAC o SPEC `z:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "up" (MP_TAC o SPEC `w:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(k1:real^2->real^N) z = k1 w`; `(h1:real^N->real^2) ((k1:real^2->real^N) z) = z`;
        `(h1:real^N->real^2) ((k1:real^2->real^N) w) = w`] THEN
      MESON_TAC[];
      USE_THEN "up" (MP_TAC o SPEC `z:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "down" (MP_TAC o SPEC `w:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(k1:real^2->real^N) z = k2 ((ph:real^2->real^2) ((rf:real^2->real^2) w))`;
        `(k1:real^2->real^N) z IN u1`; `(u1:real^N->bool) SUBSET x1`;
        `~((k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) w)) IN x1)`] THEN
      MESON_TAC[SUBSET];
      USE_THEN "up" (MP_TAC o SPEC `w:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "down" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) z)) = (k1:real^2->real^N) w`;
        `(k1:real^2->real^N) w IN u1`; `(u1:real^N->bool) SUBSET x1`;
        `~((k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) z)) IN x1)`] THEN
      MESON_TAC[SUBSET];
      USE_THEN "down" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      USE_THEN "down" (MP_TAC o SPEC `w:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `(ph:real^2->real^2) ((rf:real^2->real^2) z) = ph (rf w)` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) z)) = k2 (ph (rf w))`;
          `(h2:real^N->real^2) ((k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) z))) =
           ph (rf z)`;
          `(h2:real^N->real^2) ((k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) w))) =
           ph (rf w)`] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(rf:real^2->real^2) z = rf w` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
          can (find_term ((=) `ss:real^2->bool`)) (concl th) &&
          can (find_term ((=) `ph:real^2->real^2`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        USE_THEN "rfc" (fun th -> MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC `z:real^2` th)))) THEN
                                  MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(SPEC `w:real^2` th))))) THEN
        UNDISCH_TAC `(rf:real^2->real^2) z = rf w` THEN MESON_TAC[]]];
    ALL_TAC] THEN
  (* the image nn of the ball: its parts in x1 and x2 are open there *)
  ABBREV_TAC `nn = IMAGE (gg:real^2->real^N) ww` THEN
  SUBGOAL_THEN `(nn:real^N->bool) INTER x1 = {p | p IN u1 /\ (h1:real^N->real^2) p IN ww}`
  ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `p:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      ASM_CASES_TAC `&0 <= (z:real^2)$2` THENL
       [USE_THEN "up" (MP_TAC o SPEC `z:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        UNDISCH_TAC `p:real^N = gg (z:real^2)` THEN USE_THEN "ggdef" (fun th -> REWRITE_TAC[th]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "down" (MP_TAC o SPEC `z:real^2`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
        UNDISCH_TAC `p:real^N = gg (z:real^2)` THEN USE_THEN "ggdef" (fun th -> REWRITE_TAC[th]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
      STRIP_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `(h1:real^N->real^2) p` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "ggdef" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(nn:real^N->bool) INTER x2 =
                {p | p IN u2 /\ (h2:real^N->real^2) p IN IMAGE (ph:real^2->real^2) ww}`
  ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `p:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      ASM_CASES_TAC `&0 <= (z:real^2)$2` THENL
       [USE_THEN "up" (MP_TAC o SPEC `z:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        UNDISCH_TAC `p:real^N = gg (z:real^2)` THEN USE_THEN "ggdef" (fun th -> REWRITE_TAC[th]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
        SUBGOAL_THEN `(z:real^2)$2 = &0` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        USE_THEN "axis" (MP_TAC o SPEC `z:real^2`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `z:real^2` THEN ASM_REWRITE_TAC[];
        USE_THEN "down" (MP_TAC o SPEC `z:real^2`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
        UNDISCH_TAC `p:real^N = gg (z:real^2)` THEN USE_THEN "ggdef" (fun th -> REWRITE_TAC[th]) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `(rf:real^2->real^2) z` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC)) THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      SUBGOAL_THEN `&0 <= (w:real^2)$2` ASSUME_TAC THENL
       [SUBGOAL_THEN `&0 <= ((h2:real^N->real^2) p)$2` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN USE_THEN "phc" (fun th -> REWRITE_TAC[th])];
        ALL_TAC] THEN
      SUBGOAL_THEN `(k2:real^2->real^N) ((ph:real^2->real^2) w) = p` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `(w:real^2)$2 = &0` THENL
       [EXISTS_TAC `w:real^2` THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "axis" (MP_TAC o SPEC `w:real^2`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        USE_THEN "ggdef" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
        ASM_MESON_TAC[];
        EXISTS_TAC `(rf:real^2->real^2) w` THEN
        SUBGOAL_THEN `(rf:real^2->real^2) w IN ww /\ ((rf w)$2 < &0)` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(w:real^2) IN ww` THEN EXPAND_TAC "ww" THEN REWRITE_TAC[IN_BALL_0] THEN
          USE_THEN "rfc" (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  (* nn is open in x1 UNION x2 *)
  SUBGOAL_THEN `(nn:real^N->bool) SUBSET x1 UNION x2` ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN
    DISCH_TAC THEN USE_THEN "ggdef" (fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `&0 <= (z:real^2)$2` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "up" (MP_TAC o SPEC `z:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `(u1:real^N->bool) SUBSET x1` THEN UNDISCH_TAC `(k1:real^2->real^N) z IN u1` THEN
      SET_TAC[];
      USE_THEN "down" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      UNDISCH_TAC `(u2:real^N->bool) SUBSET x2` THEN
      UNDISCH_TAC `(k2:real^2->real^N) ((ph:real^2->real^2) ((rf:real^2->real^2) z)) IN u2` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (ph:real^2->real^2) ww)` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ss:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "inww" MP_TAC THEN SET_TAC[];
      EXPAND_TAC "ww" THEN REWRITE_TAC[OPEN_BALL];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
        can (find_term ((=) `ss:real^2->bool`)) (concl th) &&
        can (find_term ((=) `ph:real^2->real^2`)) (concl th))) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (x1 UNION x2)) (nn:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S6G_OPEN_IN_UNION_CLOSED THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "ww" THEN REWRITE_TAC[OPEN_BALL];
      MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the inverse chart psi *)
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[] o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    aconv (concl th) `homeomorphism (ss,IMAGE (ph:real^2->real^2) ss) (ph,ph')`)) THEN
  STRIP_TAC THEN
  ABBREV_TAC `psi = \p:real^N. if p IN x1 then (h1:real^N->real^2) p
                               else (rf:real^2->real^2) ((ph':real^2->real^2)
                                      ((h2:real^N->real^2) p))` THEN
  SUBGOAL_THEN `!z:real^2. z IN ww ==> (psi:real^N->real^2) ((gg:real^2->real^N) z) = z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN
    USE_THEN "ggdef" (fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `&0 <= (z:real^2)$2` THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "up" (MP_TAC o SPEC `z:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(k1:real^2->real^N) z IN x1` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `(u1:real^N->bool) SUBSET x1` THEN UNDISCH_TAC `(k1:real^2->real^N) z IN u1` THEN
        SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      USE_THEN "down" (MP_TAC o SPEC `z:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(ph':real^2->real^2) ((ph:real^2->real^2) ((rf:real^2->real^2) z)) = rf z`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; USE_THEN "rfc" (fun th -> REWRITE_TAC[th])]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^N->real^2) nn = ww` ASSUME_TAC THENL
   [EXPAND_TAC "nn" THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `(!z:real^2. z IN w ==> f z = z) ==> IMAGE f w = w`) THEN
    ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^N->real^2) continuous_on nn` ASSUME_TAC THENL
   [SUBGOAL_THEN `((nn:real^N->bool) INTER x1) UNION (nn INTER x2) = nn`
    (fun th -> MP_TAC(ISPECL [`\p:real^N. p IN x1`; `h1:real^N->real^2`;
                               `\p:real^N. (rf:real^2->real^2) ((ph':real^2->real^2)
                                              ((h2:real^N->real^2) p))`;
                               `(nn:real^N->bool) INTER x1`; `(nn:real^N->bool) INTER x2`]
                CONTINUOUS_ON_CASES_LOCAL) THEN REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `(nn:real^N->bool) SUBSET x1 UNION x2` THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x:real^N. if x IN x1 then (h1:real^N->real^2) x
                              else (rf:real^2->real^2) ((ph':real^2->real^2) ((h2:real^N->real^2) x))) =
                  psi` SUBST1_TAC THENL [EXPAND_TAC "psi" THEN REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u1:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `(\p:real^N. (rf:real^2->real^2) ((ph':real^2->real^2) ((h2:real^N->real^2) p))) =
                    rf o (ph' o h2)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u2:real^N->bool` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `IMAGE (ph:real^2->real^2) ss` THEN ASM_REWRITE_TAC[] THEN
          ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
          REWRITE_TAC[IN_IMAGE] THEN USE_THEN "inww" MP_TAC THEN MESON_TAC[]];
        EXPAND_TAC "rf" THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN CONJ_TAC THEN
        MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
        SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH]];
      X_GEN_TAC `p:real^N` THEN REWRITE_TAC[IN_INTER] THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(p:real^N) IN nn INTER x1` MP_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> if is_eq (concl th) &&
        lhand (concl th) = `(nn:real^N->bool) INTER x1` then REWRITE_TAC[th] else NO_TAC) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ABBREV_TAC `z = (h1:real^N->real^2) p` THEN
      SUBGOAL_THEN `(k1:real^2->real^N) z = p /\ &0 <= (z:real^2)$2` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "z" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "up" (MP_TAC o SPEC `z:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(z:real^2)$2 = &0` ASSUME_TAC THENL
       [SUBGOAL_THEN `((h1:real^N->real^2) p)$2 = &0` MP_TAC THENL
         [UNDISCH_TAC `!p:real^N. p IN u1 /\ p IN oo ==> (p IN x2 <=> ((h1:real^N->real^2) p)$2 = &0)` THEN
          DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN
          SUBGOAL_THEN `(p:real^N) IN oo` (fun th -> REWRITE_TAC[th]) THENL
           [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      USE_THEN "axis" (MP_TAC o SPEC `z:real^2`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(h2:real^N->real^2) p = (ph:real^2->real^2) z` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(ph':real^2->real^2) ((ph:real^2->real^2) z) = z` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN USE_THEN "inww" (MP_TAC o SPEC `z:real^2`) THEN
        ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* no ASM_SIMP_TAC here: bt, the injectivity facts and ggdef loop as rewrites *)
  MATCH_MP_TAC MOI_S8CU_R2_FROM_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`nn:real^N->bool`; `psi:real^N->real^2`; `gg:real^2->real^N`] THEN
  SUBGOAL_THEN `IMAGE (psi:real^N->real^2) nn = ww` SUBST1_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `IMAGE (gg:real^2->real^N) ww = nn` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN CONJ_TAC THENL
     [USE_THEN "ggdef" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[VEC_COMPONENT; REAL_LE_REFL] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `ball(vec 0:real^2,r) = ww` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    REWRITE_TAC[HOMEOMORPHISM] THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `IMAGE (psi:real^N->real^2) nn = ww` THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `IMAGE (gg:real^2->real^N) ww = nn` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (gg:real^2->real^N) ww = nn` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      AP_TERM_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> aconv (concl th)
        `!z:real^2. z IN ww ==> (psi:real^N->real^2) ((gg:real^2->real^N) z) = z`)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    UNDISCH_TAC `ball(vec 0:real^2,r) = ww` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[OPEN_BALL]]);;

(* ------------------------------------------------------------------------- *)
(* Half charts of a surface, the boundary inside a chart, the                *)
(* common boundary near one of its points, and the planar chart of the      *)
(* union at a point of the common boundary.                                  *)
(* ------------------------------------------------------------------------- *)

(* The part of a half chart over an open set of the plane.                   *)

let MOI_S6G_CHART_PRE = prove
 (`!(x:real^N->bool) u (h:real^N->real^2) k w.
     open_in (subtopology euclidean x) u /\
     homeomorphism (u,{z:real^2 | &0 <= z$2}) (h,k) /\ open w
     ==> open_in (subtopology euclidean x) {p | p IN u /\ h p IN w} /\
         {p | p IN u /\ h p IN w} = IMAGE k (w INTER {z:real^2 | &0 <= z$2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_MESON_TAC[HOMEOMORPHISM];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    ASM SET_TAC[]]);;

(* In a half chart of a combinatorial surface the boundary is the preimage  *)
(* of the boundary line.                                                     *)

let MOI_S6G_CHART_BD = prove
 (`!(c:(real^N->bool)->bool) u (h:real^N->real^2) k p.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     open_in (subtopology euclidean (UNIONS c)) u /\
     homeomorphism (u,{z:real^2 | &0 <= z$2}) (h,k) /\ p IN u
     ==> (p IN surface_boundary c <=> (h p)$2 = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `u:real^N->bool`; `h:real^N->real^2`;
                 `k:real^2->real^N`; `p:real^N`] MOI_S8TA_HCHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= ((h:real^N->real^2) p)$2` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    SUBGOAL_THEN `(h:real^N->real^2) p IN {z:real^2 | &0 <= z$2}` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) IN UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `~moi_s28_locally_r2 (UNIONS c) (p:real^N)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S8TA_BD_NO_R2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `&0 < ((h:real^N->real^2) p)$2` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(&0 < ((h:real^N->real^2) p)$2)` THEN
    UNDISCH_TAC `&0 <= ((h:real^N->real^2) p)$2` THEN REAL_ARITH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC MOI_S8TA_NONR2_BD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S8TA_HALF_NOT_R2 THEN ASM_MESON_TAC[]]);;

(* Near a point y of kk, a union of components of bs, the set kk is the     *)
(* preimage of the boundary line in a half chart in which bs is.            *)

let MOI_S6G_AXIS_IN_K = prove
 (`!(x:real^N->bool) u (h:real^N->real^2) k bs kk y.
     open_in (subtopology euclidean x) u /\ y IN u /\
     homeomorphism (u,{z:real^2 | &0 <= z$2}) (h,k) /\ h y = vec 0 /\
     (!p. p IN u ==> (p IN bs <=> (h p)$2 = &0)) /\
     y IN kk /\ kk SUBSET bs /\
     (!b. b IN components bs /\ ~(b INTER kk = {}) ==> b SUBSET kk)
     ==> ?oo. open oo /\ y IN oo /\
              !p. p IN u /\ p IN oo ==> (p IN kk <=> (h p)$2 = &0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "bsc") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "comp")))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM] o
              GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `u:real^N->bool`; `h:real^N->real^2`;
                 `k:real^2->real^N`; `ball(vec 0:real^2,&1)`] MOI_S6G_CHART_PRE) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET x` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N. p IN u /\ p IN oo ==> (h:real^N->real^2) p IN ball(vec 0,&1)`
  (LABEL_TAC "inb") THENL
   [UNDISCH_TAC `{p:real^N | p IN u /\ (h:real^N->real^2) p IN ball(vec 0,&1)} = x INTER oo` THEN
    UNDISCH_TAC `(u:real^N->bool) SUBSET x` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `oo:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(y:real^N) IN {p:real^N | p IN u /\ (h:real^N->real^2) p IN ball(vec 0,&1)}`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL; REAL_LT_01]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `(p:real^N) IN bs` MP_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]];
    DISCH_TAC] THEN
  ABBREV_TAC `aa = IMAGE (k:real^2->real^N) (ball(vec 0,&1) INTER {z:real^2 | z$2 = &0})` THEN
  SUBGOAL_THEN `connected (aa:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | &0 <= z$2}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
      MESON_TAC[REAL_LE_REFL];
      MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_BALL; CONVEX_STANDARD_HYPERPLANE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aa:real^N->bool) SUBSET bs` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (z:real^2)$2` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    SUBGOAL_THEN `(k:real^2->real^N) z IN u` ASSUME_TAC THENL
     [SUBGOAL_THEN `(z:real^2) IN {z:real^2 | &0 <= z$2}` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (k:real^2->real^N) {z:real^2 | &0 <= z$2} = u` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "bsc" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(k:real^2->real^N) z IN u`)]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN aa` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    EXISTS_TAC `vec 0:real^2` THEN
    REWRITE_TAC[CENTRE_IN_BALL; VEC_COMPONENT; REAL_LT_01] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
      `(h:real^N->real^2) y = vec 0`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) IN aa` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    EXISTS_TAC `(h:real^N->real^2) p` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component bs (y:real^N) SUBSET kk` ASSUME_TAC THENL
   [USE_THEN "comp" MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN ASM SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [IN] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aa:real^N->bool) SUBSET connected_component bs y` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(p:real^N) IN aa` THEN
  UNDISCH_TAC `connected_component bs (y:real^N) SUBSET kk` THEN SET_TAC[]);;

(* Polyhedra of finite combinatorial surfaces and their boundaries are       *)
(* closed.                                                                   *)

let MOI_S6G_CM_CLOSED = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> closed (UNIONS c) /\ closed (surface_boundary c) /\
         surface_boundary c SUBSET UNIONS c`,
  GEN_TAC THEN REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
  STRIP_TAC THEN REWRITE_TAC[surface_boundary] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_CLOSED];
    MATCH_MP_TAC CLOSED_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_CLOSED]];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* Off the closed set x2 the local charts of x1 UNION x2 are those of x1.    *)

let MOI_S6G_OFF_K = prove
 (`!(x1:real^N->bool) x2 y.
     closed x2 /\ y IN x1 /\ ~(y IN x2)
     ==> (moi_s28_locally_r2 (x1 UNION x2) y <=> moi_s28_locally_r2 x1 y) /\
         (moi_s28_locally_half x1 y ==> moi_s28_locally_half (x1 UNION x2) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (x1 UNION x2)) (x1 DIFF x2:real^N->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `x1 DIFF x2 = (x1 UNION x2) INTER ((:real^N) DIFF x2)` SUBST1_TAC THENL
     [SET_TAC[]; MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean x1) (x1 DIFF x2:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `x1 DIFF x2 = x1 INTER ((:real^N) DIFF x2)` SUBST1_TAC THENL
     [SET_TAC[]; MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EQ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC MOI_S8CU_R2_SUPER THEN EXISTS_TAC `x1 DIFF x2:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`x1 UNION x2:real^N->bool`; `x1 DIFF x2:real^N->bool`] THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN SET_TAC[];
      MATCH_MP_TAC MOI_S8CU_R2_SUPER THEN EXISTS_TAC `x1 DIFF x2:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`x1:real^N->bool`; `x1 DIFF x2:real^N->bool`] THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN SET_TAC[]];
    DISCH_TAC THEN MATCH_MP_TAC MOI_S6G_HALF_SUPER THEN
    EXISTS_TAC `x1 DIFF x2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S8CU_HALF_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`x1:real^N->bool`; `x1 DIFF x2:real^N->bool`] THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The union is locally planar at the common boundary; the                  *)
(* common boundary k is a polyhedron with line charts, so chi(k) = 0.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S6G_K_R2 = prove
 (`!(c:(real^N->bool)->bool) d k y.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     FINITE d /\ combinatorial_manifold_with_boundary 2 d /\
     k SUBSET surface_boundary c /\ k SUBSET surface_boundary d /\
     (!b. b IN components (surface_boundary c) /\ ~(b INTER k = {}) ==> b SUBSET k) /\
     (!b. b IN components (surface_boundary d) /\ ~(b INTER k = {}) ==> b SUBSET k) /\
     UNIONS c INTER UNIONS d = k /\ y IN k
     ==> moi_s28_locally_r2 (UNIONS c UNION UNIONS d) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[moi_s28_locally_half] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N->bool` (X_CHOOSE_THEN `h1:real^N->real^2`
    (X_CHOOSE_THEN `k1:real^2->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPEC `d:(real^N->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[moi_s28_locally_half] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:real^N->bool` (X_CHOOSE_THEN `h2:real^N->real^2`
    (X_CHOOSE_THEN `k2:real^2->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `u1:real^N->bool`; `h1:real^N->real^2`;
                 `k1:real^2->real^N`; `surface_boundary c:real^N->bool`; `k:real^N->bool`;
                 `y:real^N`] MOI_S6G_AXIS_IN_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S6G_CHART_BD THEN
    MAP_EVERY EXISTS_TAC [`u1:real^N->bool`; `k1:real^2->real^N`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `oo1:real^N->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`UNIONS d:real^N->bool`; `u2:real^N->bool`; `h2:real^N->real^2`;
                 `k2:real^2->real^N`; `surface_boundary d:real^N->bool`; `k:real^N->bool`;
                 `y:real^N`] MOI_S6G_AXIS_IN_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S6G_CHART_BD THEN
    MAP_EVERY EXISTS_TAC [`u2:real^N->bool`; `k2:real^2->real^N`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `oo2:real^N->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S6G_CM_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:(real^N->bool)->bool` MOI_S6G_CM_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u1:real^N->bool) SUBSET UNIONS c /\ (u2:real^N->bool) SUBSET UNIONS d`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S6G_HALF_GLUE THEN
  MAP_EVERY EXISTS_TAC [`u1:real^N->bool`; `h1:real^N->real^2`; `k1:real^2->real^N`;
                        `u2:real^N->bool`; `h2:real^N->real^2`; `k2:real^2->real^N`;
                        `oo1 INTER oo2:real^N->bool`] THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER] THEN CONJ_TAC THEN
  X_GEN_TAC `p:real^N` THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(p:real^N) IN UNIONS d <=> p IN k` SUBST1_TAC THENL
     [UNDISCH_TAC `UNIONS c INTER UNIONS d = (k:real^N->bool)` THEN
      UNDISCH_TAC `(u1:real^N->bool) SUBSET UNIONS c` THEN
      UNDISCH_TAC `(p:real^N) IN u1` THEN SET_TAC[];
      ASM_MESON_TAC[]];
    SUBGOAL_THEN `(p:real^N) IN UNIONS c <=> p IN k` SUBST1_TAC THENL
     [UNDISCH_TAC `UNIONS c INTER UNIONS d = (k:real^N->bool)` THEN
      UNDISCH_TAC `(u2:real^N->bool) SUBSET UNIONS d` THEN
      UNDISCH_TAC `(p:real^N) IN u2` THEN SET_TAC[];
      ASM_MESON_TAC[]]]);;

(* A union k of boundary components is the union of the simplices of c     *)
(* inside it, so a compact polyhedron.                                       *)

let MOI_S6G_K_EDGES = prove
 (`!(c:(real^N->bool)->bool) k.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     k SUBSET surface_boundary c /\
     (!b. b IN components (surface_boundary c) /\ ~(b INTER k = {}) ==> b SUBSET k)
     ==> UNIONS {s | s IN c /\ s SUBSET k} = k /\ pl_polyhedron k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "comp")))) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c ==> polytope s /\ connected s` ASSUME_TAC THENL
   [MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[simplicial_complex] THEN
    MESON_TAC[SIMPLEX_IMP_POLYTOPE; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {s:real^N->bool | s IN c /\ s SUBSET k} = k` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [MESON_TAC[SUBSET]; DISCH_TAC] THEN
    SUBGOAL_THEN `?s:real^N->bool. s IN c /\ aff_dim s = &1 /\
        CARD {r | r IN c /\ aff_dim r = &2 /\ s SUBSET r} = 1 /\ (x:real^N) IN s`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(x:real^N) IN surface_boundary c` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET surface_boundary c` ASSUME_TAC THENL
     [REWRITE_TAC[surface_boundary] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN f ==> s SUBSET UNIONS f`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `connected_component (surface_boundary c) (x:real^N) SUBSET k` MP_TAC THENL
     [USE_THEN "comp" MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN ASM SET_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^N` THEN
        ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [IN] THEN
        MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET connected_component (surface_boundary c) x`
    MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{s:real^N->bool | s IN c /\ s SUBSET k}` THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM]);;

(* Line charts on k from the half charts of c: the preimage of the boundary *)
(* line, coordinatised by the first coordinate.                             *)

let MOI_S6G_K_LINE_CHARTS = prove
 (`!(c:(real^N->bool)->bool) k.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     k SUBSET surface_boundary c /\
     (!b. b IN components (surface_boundary c) /\ ~(b INTER k = {}) ==> b SUBSET k)
     ==> moi_s4l_line_charts k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s4l_line_charts] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S6G_CM_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[moi_s28_locally_half] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
    (X_CHOOSE_THEN `h':real^2->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `u:real^N->bool`; `h:real^N->real^2`;
                 `h':real^2->real^N`; `surface_boundary c:real^N->bool`; `k:real^N->bool`;
                 `x:real^N`] MOI_S6G_AXIS_IN_K) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S6G_CHART_BD THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `h':real^2->real^N`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `oo:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "kax"))))] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN] o check (fun th ->
    aconv (concl th) `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM] o
    GEN_REWRITE_RULE I [homeomorphism] o check (fun th -> aconv (concl th)
    `homeomorphism (u,{z:real^2 | &0 <= z$2}) (h:real^N->real^2,h':real^2->real^N)`)) THEN
  SUBGOAL_THEN `!z:real^2. &0 <= z$2 ==> (h':real^2->real^N) z IN u` (LABEL_TAC "hu") THENL
   [UNDISCH_TAC `IMAGE (h':real^2->real^N) {z:real^2 | &0 <= z$2} = u` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^2. z$2 = &0 ==> z$1 % basis 1 = z` (LABEL_TAC "ax") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. (s % basis 1:real^2)$1 = s /\ (s % basis 1:real^2)$2 = &0`
  (LABEL_TAC "bc") THENL
   [GEN_TAC THEN SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\t:real^1. (h':real^2->real^N) (drop t % basis 1)) continuous_on (:real^1)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\t:real^1. (h':real^2->real^N) (drop t % basis 1)) =
                  h' o (\t:real^1. drop t % basis 1)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
      VECTOR_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | &0 <= z$2}` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
      USE_THEN "bc" (fun th -> REWRITE_TAC[th; REAL_LE_REFL])];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N. p IN u /\ p IN oo /\ ((h:real^N->real^2) p)$2 = &0
                ==> (h':real^2->real^N) (drop(lift((h p)$1)) % basis 1) = p`
  (LABEL_TAC "inv1") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    USE_THEN "ax" (fun th -> ASM_SIMP_TAC[th]);
    ALL_TAC] THEN
  EXISTS_TAC `g INTER oo:real^N->bool` THEN
  EXISTS_TAC `\p:real^N. lift(((h:real^N->real^2) p)$1)` THEN
  EXISTS_TAC `\t:real^1. (h':real^2->real^N) (drop t % basis 1)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[OPEN_INTER]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `UNIONS c INTER g = (u:real^N->bool)` THEN
    UNDISCH_TAC `(x:real^N) IN u` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k INTER (g INTER oo) =
                {p:real^N | p IN u /\ p IN oo /\ ((h:real^N->real^2) p)$2 = &0}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `p:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN EQ_TAC THEN STRIP_TAC THENL
     [SUBGOAL_THEN `(p:real^N) IN u` ASSUME_TAC THENL
       [UNDISCH_TAC `UNIONS c INTER g = (u:real^N->bool)` THEN
        UNDISCH_TAC `(p:real^N) IN k` THEN UNDISCH_TAC `(p:real^N) IN g` THEN
        UNDISCH_TAC `k SUBSET surface_boundary (c:(real^N->bool)->bool)` THEN
        UNDISCH_TAC `surface_boundary c SUBSET UNIONS (c:(real^N->bool)->bool)` THEN
        SET_TAC[];
        ASM_MESON_TAC[]];
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[];
        UNDISCH_TAC `UNIONS c INTER g = (u:real^N->bool)` THEN
        UNDISCH_TAC `(p:real^N) IN u` THEN SET_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\p:real^N. lift(((h:real^N->real^2) p)$1))
                  {p:real^N | p IN u /\ p IN oo /\ (h p)$2 = &0} =
                {t:real^1 | (h':real^2->real^N) (drop t % basis 1) IN oo}`
  (LABEL_TAC "img") THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^1` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "inv1" (fun th -> ASM_SIMP_TAC[th]);
      DISCH_TAC THEN EXISTS_TAC `(h':real^2->real^N) (drop t % basis 1)` THEN
      USE_THEN "bc" (fun th -> USE_THEN "hu" (fun th' ->
        ASM_SIMP_TAC[th; th'; REAL_LE_REFL; LIFT_DROP]))];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    USE_THEN "img" SUBST1_TAC THEN
    MP_TAC(ISPECL [`\t:real^1. (h':real^2->real^N) (drop t % basis 1)`; `(:real^1)`;
                   `oo:real^N->bool`] CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN USE_THEN "inv1" MATCH_ACCEPT_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `p:real^N` THEN
    STRIP_TAC THEN USE_THEN "inv1" (fun th -> ASM_SIMP_TAC[th]);
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    USE_THEN "inv1" (fun th -> MESON_TAC[th]);
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

(* chi(k) = 0 for a union k of boundary components of a surface.            *)

let MOI_S6G_K_EULER = prove
 (`!(c:(real^N->bool)->bool) k.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     k SUBSET surface_boundary c /\
     (!b. b IN components (surface_boundary c) /\ ~(b INTER k = {}) ==> b SUBSET k)
     ==> moi_feu_euler k (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `k:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[MOI_FEU_EULER_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(k:real^N->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    SUBGOAL_THEN `(x:real^N) IN surface_boundary c` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~({r:real^N->bool | r IN c /\ aff_dim r = &2 /\ s SUBSET r} = {})`
    MP_TAC THENL
     [DISCH_THEN(fun th -> UNDISCH_TAC
        `CARD {r:real^N->bool | r IN c /\ aff_dim r = &2 /\ s SUBSET r} = 1` THEN
        REWRITE_TAC[th; CARD_CLAUSES] THEN ARITH_TAC);
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `r:real^N->bool` AFF_DIM_LE_UNIV) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `{}:real^N->bool`] MOI_S4L_LINE_CHART_COMPLEX) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:real^N->bool`] MOI_S6G_K_EDGES) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC MOI_S6G_K_LINE_CHARTS THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kc:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `complex_euler (kc:(real^N->bool)->bool) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8CU_CM1_EULER THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
      REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TA_K1_LINK THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `kc:(real^N->bool)->bool` MOI_FEU_EULER_SIMPLICIAL_COMPLEX) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The glued surface (the theorem SURF_GLUE).                               *)
(* ------------------------------------------------------------------------- *)

(* Every point of the union has a planar or half-plane chart, and the      *)
(* points without planar chart are the boundary points off k.              *)

let MOI_S6G_UNION_LOCAL = prove
 (`!(c:(real^N->bool)->bool) d k.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     FINITE d /\ combinatorial_manifold_with_boundary 2 d /\
     k SUBSET surface_boundary c /\ k SUBSET surface_boundary d /\
     (!b. b IN components (surface_boundary c) /\ ~(b INTER k = {}) ==> b SUBSET k) /\
     (!b. b IN components (surface_boundary d) /\ ~(b INTER k = {}) ==> b SUBSET k) /\
     UNIONS c INTER UNIONS d = k
     ==> !y. y IN UNIONS c UNION UNIONS d
             ==> (moi_s28_locally_r2 (UNIONS c UNION UNIONS d) y \/
                  moi_s28_locally_half (UNIONS c UNION UNIONS d) y) /\
                 (moi_s28_locally_r2 (UNIONS c UNION UNIONS d) y <=>
                  ~(y IN (surface_boundary c DIFF k) UNION (surface_boundary d DIFF k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S6G_CM_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:(real^N->bool)->bool` MOI_S6G_CM_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ci") (CONJUNCTS_THEN2 (LABEL_TAC "cb") (K ALL_TAC))) THEN
  MP_TAC(SPEC `d:(real^N->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "di") (CONJUNCTS_THEN2 (LABEL_TAC "db") (K ALL_TAC))) THEN
  ASM_CASES_TAC `(y:real^N) IN k` THENL
   [SUBGOAL_THEN `moi_s28_locally_r2 (UNIONS c UNION UNIONS d) (y:real^N)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S6G_K_R2 THEN EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_UNION; IN_DIFF]];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^N) IN UNIONS d` THENL
   [SUBGOAL_THEN `~((y:real^N) IN UNIONS c)` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS c INTER UNIONS d = (k:real^N->bool)` THEN
      UNDISCH_TAC `~((y:real^N) IN k)` THEN UNDISCH_TAC `(y:real^N) IN UNIONS d` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ONCE_REWRITE_RULE[UNION_COMM] (ISPECL
      [`UNIONS d:real^N->bool`; `UNIONS c:real^N->bool`; `y:real^N`] MOI_S6G_OFF_K)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~((y:real^N) IN surface_boundary c)` ASSUME_TAC THENL
     [UNDISCH_TAC `~((y:real^N) IN UNIONS c)` THEN
      UNDISCH_TAC `surface_boundary c SUBSET UNIONS (c:(real^N->bool)->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^N) IN surface_boundary d` THENL
     [USE_THEN "db" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN surface_boundary d`)) THEN
      STRIP_TAC THEN ASM_SIMP_TAC[IN_UNION; IN_DIFF];
      SUBGOAL_THEN `moi_s28_locally_r2 (UNIONS d) (y:real^N)` ASSUME_TAC THENL
       [USE_THEN "di" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_UNION; IN_DIFF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS c` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^N) IN UNIONS c UNION UNIONS d` THEN
    UNDISCH_TAC `~((y:real^N) IN UNIONS d)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `UNIONS d:real^N->bool`; `y:real^N`]
    MOI_S6G_OFF_K) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((y:real^N) IN surface_boundary d)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((y:real^N) IN UNIONS d)` THEN
    UNDISCH_TAC `surface_boundary d SUBSET UNIONS (d:(real^N->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^N) IN surface_boundary c` THENL
   [USE_THEN "cb" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN surface_boundary c`)) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[IN_UNION; IN_DIFF];
    SUBGOAL_THEN `moi_s28_locally_r2 (UNIONS c) (y:real^N)` ASSUME_TAC THENL
     [USE_THEN "ci" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNION; IN_DIFF]]);;

let MOI_S6G_SURF_GLUE_BODY = prove
 (MOI_S26_SURF_GLUE_BODY,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `d:(real^N->bool)->bool`; `k:real^N->bool`]
    MOI_S6G_UNION_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "loc") THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S6G_CM_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:(real^N->bool)->bool` MOI_S6G_CM_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c UNION d:(real^N->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN
    MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN
    MP_TAC(SPEC `d:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN
    ASM_REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)))) THEN
  REWRITE_TAC[UNIONS_UNION] THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:(real^N->bool)->bool` SURF_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      USE_THEN "loc" (MP_TAC o C MATCH_MP
        (ASSUME `(y:real^N) IN UNIONS c UNION UNIONS d`)) THEN
      SIMP_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "bde") (LABEL_TAC "cl")))] THEN
  SUBGOAL_THEN `surface_boundary (e:(real^N->bool)->bool) =
                (surface_boundary c DIFF k) UNION (surface_boundary d DIFF k)`
  ASSUME_TAC THENL
   [REMOVE_THEN "bde" SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `(y:real^N) IN UNIONS c UNION UNIONS d` THENL
     [USE_THEN "loc" (MP_TAC o C MATCH_MP
        (ASSUME `(y:real^N) IN UNIONS c UNION UNIONS d`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((y:real^N) IN UNIONS c UNION UNIONS d)` THEN
      UNDISCH_TAC `surface_boundary c SUBSET UNIONS (c:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `surface_boundary d SUBSET UNIONS (d:(real^N->bool)->bool)` THEN
      SET_TAC[]];
    REMOVE_THEN "bde" (K ALL_TAC)] THEN
  SUBGOAL_THEN `complex_euler (e:(real^N->bool)->bool) =
                complex_euler (c:(real^N->bool)->bool) + complex_euler (d:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FEU_COMPLEX_EULER_EQ_EULER THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `UNIONS d:real^N->bool`;
                   `complex_euler (c:(real^N->bool)->bool)`;
                   `complex_euler (d:(real^N->bool)->bool)`; `&0`] MOI_FEU_EULER_UNION) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FEU_EULER_SIMPLICIAL_COMPLEX THEN ASM_MESON_TAC[MOI_S8TA_CMB_FACTS];
      MATCH_MP_TAC MOI_FEU_EULER_SIMPLICIAL_COMPLEX THEN ASM_MESON_TAC[MOI_S8TA_CMB_FACTS];
      MATCH_MP_TAC MOI_S6G_K_EULER THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `e:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex];
    STRIP_TAC THEN USE_THEN "cl" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[DIFF_EQ_EMPTY; UNION_EMPTY]]);;

let SURF_GLUE = prove
 (MOI_S26_SURF_GLUE,
  DISCH_THEN(K ALL_TAC) THEN ACCEPT_TAC MOI_S6G_SURF_GLUE_BODY);;

(* ------------------------------------------------------------------------- *)
(* The interior of a connected surface is connected (the theorem             *)
(* INT_CONNECTED).  Every open set of |c| meets the interior; at a boundary  *)
(* point the interior part of a half disk is connected, so it lies on one   *)
(* side of a separation of the interior, and the separation extends to |c|. *)
(* ------------------------------------------------------------------------- *)

let MOI_S6G_DENSE = prove
 (`!(c:(real^N->bool)->bool) w y.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     open_in (subtopology euclidean (UNIONS c)) w /\ y IN w
     ==> ~(w INTER (UNIONS c DIFF surface_boundary c) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^N) IN surface_boundary c` THENL
   [ALL_TAC; ASM SET_TAC[]] THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[moi_s28_locally_half] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
    (X_CHOOSE_THEN `h':real^2->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM] o
    GEN_REWRITE_RULE I [homeomorphism] o check (fun th -> aconv (concl th)
    `homeomorphism (u,{z:real^2 | &0 <= z$2}) (h:real^N->real^2,h':real^2->real^N)`)) THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (w:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `(h':real^2->real^N) (vec 0) = y` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> aconv (concl th)
      `(h:real^N->real^2) y = vec 0`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h':real^2->real^N`; `{z:real^2 | &0 <= z$2}`; `vec 0:real^2`;
                 `g:real^N->bool`] MOI_S6G_CONT_NBHD) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT; REAL_LE_REFL] THEN ANTS_TAC THENL
   [UNDISCH_TAC `UNIONS c INTER g = (w:real^N->bool)` THEN
    UNDISCH_TAC `(y:real^N) IN w` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nb"))) THEN
  ABBREV_TAC `z0 = (r / &2) % basis 2:real^2` THEN
  SUBGOAL_THEN `(z0:real^2)$2 = r / &2 /\ norm(z0) = r / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z0" THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH; NORM_MUL;
             NORM_BASIS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (z0:real^2)$2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^2->real^N) z0 IN u` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (h':real^2->real^N) {z:real^2 | &0 <= z$2} = u` THEN
    UNDISCH_TAC `&0 <= (z0:real^2)$2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^2->real^N) z0 IN g` ASSUME_TAC THENL
   [USE_THEN "nb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((h':real^2->real^N) z0 IN surface_boundary c)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `h:real^N->real^2`;
                   `h':real^2->real^N`; `(h':real^2->real^N) z0`] MOI_S6G_CHART_BD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(h':real^2->real^N) z0` THEN
  REWRITE_TAC[IN_INTER; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `UNIONS c INTER g = (w:real^N->bool)` THEN
  UNDISCH_TAC `(h':real^2->real^N) z0 IN g` THEN
  UNDISCH_TAC `(h':real^2->real^N) z0 IN u` THEN
  UNDISCH_TAC `(u:real^N->bool) SUBSET UNIONS c` THEN SET_TAC[]);;

(* At a boundary point, a neighbourhood whose interior part is on one side  *)
(* of a separation a1, a2 of the interior.                                   *)

let MOI_S6G_HALF_DISK_SIDE = prove
 (`!(c:(real^N->bool)->bool) a1 a2 q.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     open_in (subtopology euclidean (UNIONS c DIFF surface_boundary c)) a1 /\
     open_in (subtopology euclidean (UNIONS c DIFF surface_boundary c)) a2 /\
     UNIONS c DIFF surface_boundary c SUBSET a1 UNION a2 /\ a1 INTER a2 = {} /\
     q IN surface_boundary c
     ==> ?v. open_in (subtopology euclidean (UNIONS c)) v /\ q IN v /\
             (v INTER (UNIONS c DIFF surface_boundary c) SUBSET a1 \/
              v INTER (UNIONS c DIFF surface_boundary c) SUBSET a2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `q:real^N` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[moi_s28_locally_half] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
    (X_CHOOSE_THEN `h':real^2->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM] o
    GEN_REWRITE_RULE I [homeomorphism] o check (fun th -> aconv (concl th)
    `homeomorphism (u,{z:real^2 | &0 <= z$2}) (h:real^N->real^2,h':real^2->real^N)`)) THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N. p IN u
                ==> (p IN surface_boundary c <=> ((h:real^N->real^2) p)$2 = &0)`
  (LABEL_TAC "bd") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S6G_CHART_BD THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `h':real^2->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N. p IN u ==> &0 <= ((h:real^N->real^2) p)$2`
  (LABEL_TAC "nonneg") THENL
   [UNDISCH_TAC `IMAGE (h:real^N->real^2) u = {z:real^2 | &0 <= z$2}` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `u:real^N->bool`; `h:real^N->real^2`;
                 `h':real^2->real^N`; `ball(vec 0:real^2,&1)`] MOI_S6G_CHART_PRE) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  EXISTS_TAC `{p:real^N | p IN u /\ (h:real^N->real^2) p IN ball(vec 0,&1)}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL; REAL_LT_01] THEN
  ABBREV_TAC `dd = IMAGE (h':real^2->real^N) (ball(vec 0,&1) INTER {z:real^2 | &0 < z$2})` THEN
  SUBGOAL_THEN `{p:real^N | p IN u /\ (h:real^N->real^2) p IN ball(vec 0,&1)} INTER
                (UNIONS c DIFF surface_boundary c) SUBSET dd` ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `p:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_DIFF; IN_IMAGE] THEN STRIP_TAC THEN
    EXISTS_TAC `(h:real^N->real^2) p` THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `~(((h:real^N->real^2) p)$2 = &0)` MP_TAC THENL
     [USE_THEN "bd" (fun th -> ASM_MESON_TAC[th]); ALL_TAC] THEN
    USE_THEN "nonneg" (MP_TAC o C MATCH_MP (ASSUME `(p:real^N) IN u`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (dd:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | &0 <= z$2}` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
      MESON_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_BALL; GSYM real_gt; CONVEX_HALFSPACE_COMPONENT_GT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(dd:real^N->bool) SUBSET UNIONS c DIFF surface_boundary c` ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(h':real^2->real^N) z IN u` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= (z:real^2)$2` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (h':real^2->real^N) {z:real^2 | &0 <= z$2} = u` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      USE_THEN "bd" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(h':real^2->real^N) z IN u`)]) THEN
      SUBGOAL_THEN `&0 <= (z:real^2)$2` (fun th -> ASM_SIMP_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(dd:real^N->bool) SUBSET a1 \/ dd SUBSET a2` MP_TAC THENL
   [SUBGOAL_THEN `closed_in (subtopology euclidean (UNIONS c DIFF surface_boundary c))
                    (a1:real^N->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN `a1 = (UNIONS c DIFF surface_boundary c) DIFF (a2:real^N->bool)`
      SUBST1_TAC THENL
       [SUBGOAL_THEN `(a1:real^N->bool) SUBSET UNIONS c DIFF surface_boundary c` MP_TAC THENL
         [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
        UNDISCH_TAC `a1 INTER a2:real^N->bool = {}` THEN
        UNDISCH_TAC `UNIONS c DIFF surface_boundary c SUBSET (a1:real^N->bool) UNION a2` THEN
        SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_REFL]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(dd:real^N->bool) INTER a1 = {}` THENL
     [DISJ2_TAC THEN UNDISCH_TAC `(dd:real^N->bool) INTER a1 = {}` THEN
      UNDISCH_TAC `(dd:real^N->bool) SUBSET UNIONS c DIFF surface_boundary c` THEN
      UNDISCH_TAC `UNIONS c DIFF surface_boundary c SUBSET (a1:real^N->bool) UNION a2` THEN
      SET_TAC[];
      DISJ1_TAC THEN MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
      EXISTS_TAC `UNIONS c DIFF surface_boundary (c:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `{p:real^N | p IN u /\ (h:real^N->real^2) p IN ball(vec 0,&1)} INTER
                (UNIONS c DIFF surface_boundary c) SUBSET dd` THEN
  MESON_TAC[SUBSET_TRANS]);;

(* Sets of points of x having a neighbourhood whose part in i lies in a.    *)

let MOI_S6G_SUBOPEN_SET = prove
 (`!(x:real^N->bool) i a.
     open_in (subtopology euclidean x)
       {q | q IN x /\
            ?v. open_in (subtopology euclidean x) v /\ q IN v /\ v INTER i SUBSET a}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `q:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET];
    EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let INT_CONNECTED = prove
 (MOI_S26_INT_CONNECTED,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S6G_CM_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c))
                  (UNIONS c DIFF surface_boundary (c:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^N->bool` (X_CHOOSE_THEN `a2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (a1:real^N->bool) /\
                open_in (subtopology euclidean (UNIONS c)) (a2:real^N->bool) /\
                a1 SUBSET UNIONS c DIFF surface_boundary c /\
                a2 SUBSET UNIONS c DIFF surface_boundary c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_TRANS; OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `connected (UNIONS (c:(real^N->bool)->bool))` THEN
  REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  MAP_EVERY EXISTS_TAC
   [`{q:real^N | q IN UNIONS c /\
                 ?v. open_in (subtopology euclidean (UNIONS c)) v /\ q IN v /\
                     v INTER (UNIONS c DIFF surface_boundary c) SUBSET a1}`;
    `{q:real^N | q IN UNIONS c /\
                 ?v. open_in (subtopology euclidean (UNIONS c)) v /\ q IN v /\
                     v INTER (UNIONS c DIFF surface_boundary c) SUBSET a2}`] THEN
  REWRITE_TAC[MOI_S6G_SUBOPEN_SET] THEN REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(q:real^N) IN surface_boundary c` THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a1:real^N->bool`; `a2:real^N->bool`;
                     `q:real^N`] MOI_S6G_HALF_DISK_SIDE) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^N) IN a1 \/ q IN a2` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS c DIFF surface_boundary c SUBSET (a1:real^N->bool) UNION a2` THEN
      UNDISCH_TAC `~((q:real^N) IN surface_boundary c)` THEN
      UNDISCH_TAC `(q:real^N) IN UNIONS c` THEN SET_TAC[];
      DISJ1_TAC THEN EXISTS_TAC `a1:real^N->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
      DISJ2_TAC THEN EXISTS_TAC `a2:real^N->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `q:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v1:real^N->bool` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v2:real^N->bool` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v1 INTER v2:real^N->bool`; `q:real^N`]
      MOI_S6G_DENSE) THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN
    UNDISCH_TAC `a1 INTER a2:real^N->bool = {}` THEN
    UNDISCH_TAC `v1 INTER (UNIONS c DIFF surface_boundary c) SUBSET (a1:real^N->bool)` THEN
    UNDISCH_TAC `v2 INTER (UNIONS c DIFF surface_boundary c) SUBSET (a2:real^N->bool)` THEN
    SET_TAC[];
    UNDISCH_TAC `~(a1:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:real^N`) THEN EXISTS_TAC `q:real^N` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `a1:real^N->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
    UNDISCH_TAC `~(a2:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:real^N`) THEN EXISTS_TAC `q:real^N` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `a2:real^N->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET]]);;

