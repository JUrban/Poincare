(* ========================================================================= *)
(* pc_moi_s28_tria: charts of combinatorial surfaces (Moise GTM 47, pp.37-38 *)
(* and p.191) -- SURF_CHARTS: a finite combinatorial 2-manifold with         *)
(* boundary has plane charts off its boundary and half-plane charts (and no  *)
(* plane charts) on it; POLYGON_COMPLEX: a PL 1-sphere is triangulated by a  *)
(* connected combinatorial 1-manifold.  The local analysis at edges below is *)
(* shared with pc_moi_s28_trib.                                              *)
(* ========================================================================= *)

needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_fnd_surfa.ml";;
needs "src/pc_moi_pl1m.ml";;
needs "src/pc_moi_fnd_cm2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Model charts.  H, the set of all z with 0 <= z$2, is the closed        *)
(* upper half plane.  The half-open triangle moi_s8ta_tp (the cone from 0 *)
(* over the segment from (-1,1) to (1,1), minus that segment) is          *)
(* homeomorphic to H with 0 -> 0, through the closed wedge of all z with  *)
(* abs(z$1) <= z$2.  A point with a half-plane chart (sent to 0) has no   *)
(* plane chart (invariance of domain).                                     *)
(* ------------------------------------------------------------------------- *)

let moi_s8ta_tp = new_definition
 `moi_s8ta_tp = {z:real^2 | abs(z$1) <= z$2 /\ z$2 < &1}`;;

let MOI_S8TA_HOMEO_INV = prove
 (`!(f:real^M->real^N) g s t.
     f continuous_on s /\ g continuous_on t /\
     (!x. x IN s ==> f x IN t /\ g(f x) = x) /\
     (!y. y IN t ==> g y IN s /\ f(g y) = y)
     ==> homeomorphism (s,t) (f,g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homeomorphism] THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_S8TA_WEDGE_HALF = prove
 (`homeomorphism ({z:real^2 | abs(z$1) <= z$2},{z:real^2 | &0 <= z$2})
                 ((\z. z - abs(z$1) % basis 2),(\w. w + abs(w$1) % basis 2))`,
  MATCH_MP_TAC MOI_S8TA_HOMEO_INV THEN
  SIMP_TAC[IN_ELIM_THM; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           BASIS_COMPONENT; DIMINDEX_2; ARITH; REAL_MUL_RZERO; REAL_MUL_RID;
           REAL_SUB_RZERO; REAL_ADD_RID] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
    SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_ABS THEN
    SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]]);;

let MOI_S8TA_SCALE_LEMMA = prove
 (`!a. a < &1 ==> inv(&1 + inv(&1 - a) * a) * inv(&1 - a) = &1 /\
                  &0 < inv(&1 - a)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&1 - a = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&1 + inv(&1 - a) * a = inv(&1 - a)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(&1 - a = &0)` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[REAL_INV_EQ_0]];
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC]);;

let MOI_S8TA_SCALE_LEMMA2 = prove
 (`!b. &0 <= b ==> inv(&1 - inv(&1 + b) * b) * inv(&1 + b) = &1 /\
                   &0 < inv(&1 + b) /\ inv(&1 + b) * b < &1`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(&1 + b = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `&1 - inv(&1 + b) * b = inv(&1 + b)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(&1 + b = &0)` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[REAL_INV_EQ_0]];
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= b ==> &0 < &1 + b`] THEN
    REAL_ARITH_TAC]);;

let MOI_S8TA_TP_WEDGE = prove
 (`homeomorphism (moi_s8ta_tp,{z:real^2 | abs(z$1) <= z$2})
                 ((\z. inv(&1 - z$2) % z),(\w. inv(&1 + w$2) % w))`,
  MATCH_MP_TAC MOI_S8TA_HOMEO_INV THEN REWRITE_TAC[moi_s8ta_tp; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    SUBGOAL_THEN `(lift o (\z:real^2. inv(&1 - z$2))) = (lift o inv o (\z. &1 - z$2))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
      REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    SUBGOAL_THEN `(lift o (\w:real^2. inv(&1 + w$2))) = (lift o inv o (\w. &1 + w$2))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; DIMINDEX_2; ARITH];
      REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC];
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    MP_TAC(SPEC `(z:real^2)$2` MOI_S8TA_SCALE_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_MUL_ASSOC; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; VECTOR_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (w:real^2)$2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `(w:real^2)$2` MOI_S8TA_SCALE_LEMMA2) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_MUL_ASSOC; REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; VECTOR_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let MOI_S8TA_TP_HALF = prove
 (`?f g. homeomorphism (moi_s8ta_tp,{z:real^2 | &0 <= z$2}) (f,g) /\ f(vec 0) = vec 0`,
  MAP_EVERY EXISTS_TAC
   [`(\z:real^2. z - abs(z$1) % basis 2) o (\z:real^2. inv(&1 - z$2) % z)`;
    `(\w:real^2. inv(&1 + w$2) % w) o (\w:real^2. w + abs(w$1) % basis 2)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `{z:real^2 | abs(z$1) <= z$2}` THEN
    REWRITE_TAC[MOI_S8TA_TP_WEDGE; MOI_S8TA_WEDGE_HALF];
    REWRITE_TAC[o_THM; VEC_COMPONENT; VECTOR_MUL_RZERO; REAL_ABS_0;
                VECTOR_MUL_LZERO; VECTOR_SUB_RZERO]]);;

(* Open half plane, relative interiors of 2-dimensional convex sets.       *)

let MOI_S8TA_OPEN_HALF_R2 = prove
 (`{z:real^2 | &0 < z$2} homeomorphic (:real^2)`,
  MATCH_MP_TAC HOMEOMORPHIC_CONVEX_OPEN_SETS THEN
  REWRITE_TAC[CONVEX_UNIV; OPEN_UNIV; UNIV_NOT_EMPTY] THEN
  REWRITE_TAC[REWRITE_RULE[real_gt] OPEN_HALFSPACE_COMPONENT_GT;
              REWRITE_RULE[real_gt] CONVEX_HALFSPACE_COMPONENT_GT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  EXISTS_TAC `vector[&0; &1]:real^2` THEN REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S8TA_RELINT_R2 = prove
 (`!t:real^N->bool. convex t /\ aff_dim t = &2
                    ==> relative_interior t homeomorphic (:real^2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_RELATIVELY_OPEN_CONVEX_SETS THEN
  ASM_SIMP_TAC[CONVEX_RELATIVE_INTERIOR; AFF_DIM_RELATIVE_INTERIOR; CONVEX_UNIV;
               AFF_DIM_UNIV; DIMINDEX_2; AFFINE_HULL_UNIV; AFFINE_HULL_RELATIVE_INTERIOR;
               OPEN_IN_RELATIVE_INTERIOR] THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_UNIV]);;
(* Charts from a homeomorphism of an open subset u of x onto H: points sent *)
(* into the open half plane have plane charts; points sent to the boundary *)
(* line have half-plane charts (translate along the line).                 *)

let MOI_S8TA_HCHART = prove
 (`!(x:real^N->bool) u (h:real^N->real^2) k y.
     open_in (subtopology euclidean x) u /\
     homeomorphism (u,{z:real^2 | &0 <= z$2}) (h,k) /\ y IN u
     ==> (&0 < (h y)$2 ==> moi_s28_locally_r2 x y) /\
         ((h y)$2 = &0 ==> moi_s28_locally_half x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[moi_s28_locally_r2] THEN
    EXISTS_TAC `{z | z IN u /\ (h:real^N->real^2) z IN {w:real^2 | &0 < w$2}}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
      REWRITE_TAC[REWRITE_RULE[real_gt] OPEN_HALFSPACE_COMPONENT_GT] THEN
      FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                  GEN_REWRITE_RULE I [homeomorphism]);
      ASM_REWRITE_TAC[IN_ELIM_THM];
      MATCH_MP_TAC(INST_TYPE [`:2`,`:N`] HOMEOMORPHIC_TRANS) THEN
      EXISTS_TAC `{w:real^2 | &0 < w$2}` THEN
      REWRITE_TAC[MOI_S8TA_OPEN_HALF_R2; homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^2`; `k:real^2->real^N`] THEN
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `{z:real^2 | &0 <= z$2}`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `homeomorphism (u,{z:real^2 | &0 <= z$2}) (h:real^N->real^2,k)` THEN
      REWRITE_TAC[homeomorphism] THEN
      REWRITE_TAC[EXTENSION; SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [MESON_TAC[];
        GEN_TAC THEN REAL_ARITH_TAC;
        X_GEN_TAC `w:real^2` THEN EQ_TAC THENL
         [STRIP_TAC THEN ASM_REWRITE_TAC[];
          DISCH_TAC THEN EXISTS_TAC `(k:real^2->real^N) w` THEN
          SUBGOAL_THEN `&0 <= (w:real^2)$2` ASSUME_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]]]];
    REWRITE_TAC[moi_s28_locally_half] THEN
    MAP_EVERY EXISTS_TAC
     [`u:real^N->bool`;
      `(\w:real^2. w - ((h:real^N->real^2) y)$1 % basis 1) o (h:real^N->real^2)`;
      `(k:real^2->real^N) o (\w:real^2. w + ((h:real^N->real^2) y)$1 % basis 1)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `{z:real^2 | &0 <= z$2}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_S8TA_HOMEO_INV THEN
      SIMP_TAC[IN_ELIM_THM; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH;
               REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_RID] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
        REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
        REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
        REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC];
      SIMP_TAC[o_THM; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_SUB_COMPONENT;
               VECTOR_MUL_COMPONENT; BASIS_COMPONENT; VEC_COMPONENT; ARITH] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

(* A point with a half-plane chart sending it to 0 has no plane chart: the *)
(* half-plane chart composed with the inverse plane chart is an injective  *)
(* map of an open planar set onto a set inside H containing 0, which is    *)
(* then open (invariance of domain); but H contains no ball at 0.           *)

let MOI_S8TA_HALF_NOT_R2 = prove
 (`!(x:real^N->bool) y. moi_s28_locally_half x y ==> ~moi_s28_locally_r2 x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s28_locally_half; moi_s28_locally_r2; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
    (X_CHOOSE_THEN `k:real^2->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "H") ASSUME_TAC)))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:real^N->real^2`
      (X_CHOOSE_THEN `p':real^2->real^N` (LABEL_TAC "P")))))) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean u') (u INTER u':real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `x:real^N->bool` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
      SET_TAC[];
      UNDISCH_TAC `open_in (subtopology euclidean x) (u':real^N->bool)` THEN
      DISCH_THEN(ACCEPT_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (p:real^N->real^2) (u INTER u'))` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`p':real^2->real^N`; `u':real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "P" (fun th -> EVERY (map2 LABEL_TAC ["p1";"p2";"p3";"p4";"p5";"p6"]
    (CONJUNCTS (REWRITE_RULE[homeomorphism; IN_UNIV] th)))) THEN
  USE_THEN "H" (fun th -> EVERY (map2 LABEL_TAC ["h1";"h2";"h3";"h4";"h5";"h6"]
    (CONJUNCTS (REWRITE_RULE[homeomorphism] th)))) THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^2) (u INTER u') =
                IMAGE ((h:real^N->real^2) o (p':real^2->real^N)) (IMAGE p (u INTER u'))`
  (LABEL_TAC "IE") THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN MATCH_MP_TAC IMAGE_EQ THEN
    REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    USE_THEN "p1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^N) IN u'`)]);
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (h:real^N->real^2) (u INTER u'))` MP_TAC THENL
   [REMOVE_THEN "IE" SUBST1_TAC THEN MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        USE_THEN "p6" (fun th -> REWRITE_TAC[th; SUBSET_UNIV]);
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
        USE_THEN "h3" (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN
        STRIP_TAC THEN
        USE_THEN "p1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z:real^N) IN u'`)]) THEN
        FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_INTER; o_THM] THEN
      X_GEN_TAC `z1:real^N` THEN DISCH_TAC THEN DISCH_TAC THEN
      X_GEN_TAC `z2:real^N` THEN DISCH_TAC THEN DISCH_TAC THEN
      USE_THEN "p1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(z1:real^N) IN u'`);
                                         MATCH_MP th (ASSUME `(z2:real^N) IN u'`)]) THEN
      DISCH_TAC THEN AP_TERM_TAC THEN
      USE_THEN "h1" (fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `(z1:real^N) IN u`));
                                               GSYM(MATCH_MP th (ASSUME `(z2:real^N) IN u`))]) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `--(e / &2) % basis 2:real^2 IN IMAGE (h:real^N->real^2) u` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a b c (x:real^2). x IN a /\ a SUBSET b /\ b SUBSET c ==> x IN c`) THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^2,e)`; `IMAGE (h:real^N->real^2) (u INTER u')`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_BALL_0; NORM_MUL; REAL_ABS_NEG] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    USE_THEN "h2" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Vertex star charts.  The closed star of v is the cone from v over        *)
(* its link (MOI_STA_LINK_FACTS, MOI_CON_CONE_MAP).  For an arc link it is  *)
(* PL homeomorphic to the triangle conv{0,(-1,1),(1,1)} with the link going  *)
(* to the top side and v to 0; the open star then goes onto moi_s8ta_tp,     *)
(* hence onto H with v -> 0.  For a circle link (MOI_FC2_STAR_CIRCLE of    *)
(* pc_moi_fnd_cm2) the open star is homeomorphic to R^2.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S8TA_SEG_PLH = prove
 (`!(a:real^M) b (c:real^N) d.
     ~(a = b) /\ ~(c = d)
     ==> ?f g. pl_homeomorphism (segment[a,b],segment[c,d]) (f,g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `linepath(a:real^M,b)` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  MP_TAC(ISPEC `linepath(c:real^N,d)` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_SIMP_TAC[ARC_LINEPATH; MOI_PL2_PL_LINEPATH; LOCALLY_POLYHEDRAL_POLYTOPE;
               POLYTOPE_INTERVAL; PATH_IMAGE_LINEPATH] THEN
  DISCH_THEN(X_CHOOSE_TAC `h2:real^N->real^1`) THEN
  DISCH_THEN(X_CHOOSE_TAC `h1:real^M->real^1`) THEN
  MAP_EVERY EXISTS_TAC [`linepath(c:real^N,d) o (h1:real^M->real^1)`;
                        `linepath(a:real^M,b) o (h2:real^N->real^1)`] THEN
  MATCH_MP_TAC(INST_TYPE [`:1`,`:N`] PL_HOMEOMORPHISM_COMPOSE) THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The model triangle T = conv{0,(-1,1),(1,1)} and its top side A.         *)

let MOI_S8TA_TRI_MEM = prove
 (`!z:real^2. z IN convex hull {vec 0, vector[-- &1;&1], vector[&1;&1]} <=>
              abs(z$1) <= z$2 /\ z$2 <= &1`,
  GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `w:real`
      STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1 - (z:real^2)$2`; `((z:real^2)$2 - z$1) / &2`;
                          `((z:real^2)$2 + z$1) / &2`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                  VEC_COMPONENT; VECTOR_2] THEN REAL_ARITH_TAC]]);;

let MOI_S8TA_TOP_MEM = prove
 (`!z:real^2. z IN segment[vector[-- &1;&1],vector[&1;&1]] <=>
              z$2 = &1 /\ abs(z$1) <= &1`,
  GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `((z:real^2)$1 + &1) / &2` THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                  VECTOR_2] THEN ASM_REAL_ARITH_TAC]]);;

let MOI_S8TA_TRI_CONE = prove
 (`UNIONS {segment[vec 0,x] | x IN segment[vector[-- &1;&1]:real^2,vector[&1;&1]]} =
   convex hull {vec 0:real^2, vector[-- &1;&1], vector[&1;&1]}`,
  REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS; NOT_INSERT_EMPTY; GSYM SEGMENT_CONVEX_HULL]);;

let MOI_S8TA_TRI_DIFF = prove
 (`convex hull {vec 0:real^2, vector[-- &1;&1], vector[&1;&1]} DIFF
   segment[vector[-- &1;&1],vector[&1;&1]] = moi_s8ta_tp`,
  REWRITE_TAC[EXTENSION; IN_DIFF; MOI_S8TA_TRI_MEM; MOI_S8TA_TOP_MEM; moi_s8ta_tp;
              IN_ELIM_THM] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S8TA_TOP_SEGCOND = prove
 (`~(vec 0 IN segment[vector[-- &1;&1]:real^2,vector[&1;&1]]) /\
   (!x y. x IN segment[vector[-- &1;&1]:real^2,vector[&1;&1]] /\
          y IN segment[vector[-- &1;&1],vector[&1;&1]] /\ y IN segment[vec 0,x]
          ==> y = x) /\
   pl_polyhedron (segment[vector[-- &1;&1]:real^2,vector[&1;&1]]) /\
   ~(segment[vector[-- &1;&1]:real^2,vector[&1;&1]] = {})`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_S8TA_TOP_MEM; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
    REWRITE_TAC[MOI_S8TA_TOP_MEM] THEN REWRITE_TAC[IN_SEGMENT] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `w = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^2)$2 = &1` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[VECTOR_MUL_LID]];
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_SEGMENT];
    REWRITE_TAC[SEGMENT_EQ_EMPTY]]);;
(* The closed star of a vertex with an arc link: the cone over the link is *)
(* PL homeomorphic to the model triangle (link -> top side, v -> 0).      *)

let MOI_S8TA_STAR_ARC = prove
 (`!c (v:real^N).
     lf_simplicial_complex c /\ {v} IN c /\ pl_ball 1 (UNIONS (simplicial_link c v))
     ==> ?p q. pl_homeomorphism
                 (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)},
                  convex hull {vec 0:real^2, vector[-- &1;&1], vector[&1;&1]}) (p,q) /\
               IMAGE p (UNIONS (simplicial_link c v)) =
               segment[vector[-- &1;&1],vector[&1;&1]] /\
               p v = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_ball]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f0:real^N->real^N`
    (X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `&1 simplex (k:real^N->bool)` THEN REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  MP_TAC(ISPECL [`vector[-- &1;&1]:real^2`; `vector[&1;&1]:real^2`; `a:real^N`; `b:real^N`]
    MOI_S8TA_SEG_PLH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^N` (X_CHOOSE_THEN `g1:real^N->real^2`
    ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (segment[vector[-- &1;&1]:real^2,vector[&1;&1]],
                      UNIONS (simplicial_link c (v:real^N)))
                     ((f0:real^N->real^N) o (f1:real^2->real^N),
                      (g1:real^N->real^2) o (g0:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `segment[a:real^N,b]` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((g1:real^N->real^2) o (g0:real^N->real^N))
          (UNIONS (simplicial_link c (v:real^N))) =
    segment[vector[-- &1;&1],vector[&1;&1]] /\
    IMAGE ((f0:real^N->real^N) o (f1:real^2->real^N))
          (segment[vector[-- &1;&1],vector[&1;&1]]) =
    UNIONS (simplicial_link c v)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `pl_homeomorphism (segment[vector[-- &1;&1]:real^2,vector[&1;&1]],
                        UNIONS (simplicial_link c (v:real^N)))
                       ((f0:real^N->real^N) o (f1:real^2->real^N),
                        (g1:real^N->real^2) o (g0:real^N->real^N))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_S8TA_TOP_SEGCOND THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`segment[vector[-- &1;&1]:real^2,vector[&1;&1]]`;
    `UNIONS (simplicial_link c (v:real^N))`; `vec 0:real^2`; `v:real^N`;
    `(f0:real^N->real^N) o (f1:real^2->real^N)`;
    `(g1:real^N->real^2) o (g0:real^N->real^N)`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[MOI_S8TA_TRI_CONE] THEN STRIP_TAC THEN
  EXISTS_TAC `moi_con_conemap (UNIONS (simplicial_link c v)) (v:real^N) (vec 0:real^2)
               ((g1:real^N->real^2) o (g0:real^N->real^N))` THEN
  EXISTS_TAC `moi_con_conemap (segment[vector[-- &1;&1]:real^2,vector[&1;&1]])
               (vec 0:real^2) (v:real^N) ((f0:real^N->real^N) o (f1:real^2->real^N))` THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE ((g1:real^N->real^2) o (g0:real^N->real^N))
                      (UNIONS (simplicial_link c (v:real^N)))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^N. x IN s ==> (f:real^N->real^2) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_CONEMAP_ON_BASE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_CON_CONEMAP_APEX THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE ((f0:real^N->real^N) o (f1:real^2->real^N))
                   (segment[vector[-- &1;&1],vector[&1;&1]]) =
                 UNIONS (simplicial_link c (v:real^N))` THEN
    UNDISCH_TAC `~(segment[vector[-- &1;&1]:real^2,vector[&1;&1]] = {})` THEN
    SET_TAC[]]);;

(* The open star of a vertex with an arc link is homeomorphic to H, with   *)
(* the vertex going to 0.                                                   *)

let MOI_S8TA_ARC_CHART = prove
 (`!c (v:real^N).
     lf_simplicial_complex c /\ {v} IN c /\ pl_ball 1 (UNIONS (simplicial_link c v))
     ==> ?h k. homeomorphism (moi_sta_open_star c v,{z:real^2 | &0 <= z$2}) (h,k) /\
               h v = vec 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:real^N->real^2` (X_CHOOSE_THEN `q:real^2->real^N`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_S8TA_STAR_ARC) THEN
  X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC)
    MOI_S8TA_TP_HALF THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `~(UNIONS (simplicial_link c (v:real^N)) = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (p:real^N->real^2) (UNIONS (simplicial_link c v)) =
                 segment[vector[-- &1;&1],vector[&1;&1]]` THEN
    MP_TAC MOI_S8TA_TOP_SEGCOND THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (simplicial_link c (v:real^N)) SUBSET
                UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `segment[v:real^N,y]` THEN
    REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `y:real^N` THEN
    ASM_REWRITE_TAC[IN_UNIONS];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (moi_sta_open_star c v,moi_s8ta_tp)
                              (p:real^N->real^2,q)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC
     [`UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c (v:real^N))}`;
      `convex hull {vec 0:real^2, vector[-- &1;&1], vector[&1;&1]}`] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism] o
      check (fun th -> can (term_match []
        `pl_homeomorphism (a:real^N->bool,b:real^2->bool) (f,g)`) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_STA_OPEN_STAR_EQ] THEN
    REWRITE_TAC[GSYM MOI_S8TA_TRI_DIFF] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[]; SET_TAC[];
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        rhs(concl th) = `segment[vector[-- &1;&1]:real^2,vector[&1;&1]]`
        then SUBST1_TAC(SYM th) else NO_TAC) THEN
      MATCH_MP_TAC MOI_STA_IMAGE_DIFF THEN EXISTS_TAC `q:real^2->real^N` THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o
        check (fun th -> can (term_match []
          `homeomorphism (a:real^N->bool,b:real^2->bool) (f,g)`) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(f:real^2->real^2) o (p:real^N->real^2)`;
                        `(q:real^2->real^N) o (g:real^2->real^2)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `moi_s8ta_tp` THEN ASM_REWRITE_TAC[]);;

(* The open star of a vertex with a circle link is homeomorphic to R^2.    *)

let MOI_S8TA_CIRCLE_CHART = prove
 (`!c (v:real^N).
     lf_simplicial_complex c /\ {v} IN c /\ pl_sphere 1 (UNIONS (simplicial_link c v))
     ==> moi_sta_open_star c v homeomorphic (:real^2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `S:real^2->bool` (X_CHOOSE_THEN `p:real^N->real^2`
    (X_CHOOSE_THEN `q:real^2->real^N` STRIP_ASSUME_TAC)) o MATCH_MP MOI_FC2_STAR_CIRCLE) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `~(UNIONS (simplicial_link c (v:real^N)) = {})` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCD_PL_SPHERE_NONEMPTY THEN EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (simplicial_link c (v:real^N)) SUBSET
                UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN EXISTS_TAC `segment[v:real^N,y]` THEN
    REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `y:real^N` THEN
    ASM_REWRITE_TAC[IN_UNIONS];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior S:real^2->bool = S DIFF relative_frontier S`
  ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN
    SUBGOAL_THEN `closure S:real^2->bool = S` SUBST1_TAC THENL
     [MATCH_MP_TAC CLOSURE_CLOSED THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
      MP_TAC(ISPEC `S:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:2`,`:N`] HOMEOMORPHIC_TRANS) THEN
  EXISTS_TAC `relative_interior S:real^2->bool` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_S8TA_RELINT_R2 THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; AFF_DIM_SIMPLEX]] THEN
  REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`p:real^N->real^2`; `q:real^2->real^N`] THEN
  MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c (v:real^N))}`;
    `S:real^2->bool`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism] o
    check (fun th -> can (term_match []
      `pl_homeomorphism (a:real^N->bool,b:real^2->bool) (f,g)`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_STA_OPEN_STAR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[]; SET_TAC[];
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
      rhs(concl th) = `relative_frontier (S:real^2->bool)`
      then SUBST1_TAC(SYM th) else NO_TAC) THEN
    MATCH_MP_TAC MOI_STA_IMAGE_DIFF THEN EXISTS_TAC `q:real^2->real^N` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o
      check (fun th -> can (term_match []
        `homeomorphism (a:real^N->bool,b:real^2->bool) (f,g)`) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Local analysis at points of a finite simplicial complex in real^N        *)
(* with 2-dimensional charts (shared with pc_moi_s28_trib).  A 2D chart     *)
(* (moi_s8ta_emb2) is an embedding of a neighbourhood into R^2; plane and   *)
(* half-plane charts are 2D charts, and they contain embedded open disks.   *)
(* Book lemmas at a point y of the relative interior of an edge e:          *)
(* two triangles on e unfold to an open planar set, so a 2D chart at y      *)
(* gives a plane chart (B2) and three triangles on e allow no 2D chart     *)
(* (B4); one triangle allows no plane chart (B3); no triangle allows no    *)
(* plane or half-plane chart (B5).  Triangle interiors have plane charts,   *)
(* and 2D charts everywhere force dimension at most 2.                     *)
(* (After MOI_SCF_SURF_EDGE_NOT1 / _NOT3 of pc_moi_smo_cf, which assume a  *)
(* polyhedron homeomorphic to S^2.)                                         *)
(* ------------------------------------------------------------------------- *)

let moi_s8ta_emb2 = new_definition
 `moi_s8ta_emb2 (x:real^N->bool) (y:real^N) <=>
    ?u (f:real^N->real^2) g. open_in (subtopology euclidean x) u /\ y IN u /\
                             homeomorphism (u,IMAGE f u) (f,g)`;;

let MOI_S8TA_HOMEO_IMAGE = prove
 (`!(f:real^M->real^N) g s t.
     homeomorphism (s,t) (f,g) ==> homeomorphism (s,IMAGE f s) (f,g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MP_TAC th THEN
    SUBST1_TAC(CONJUNCT1(CONJUNCT2(REWRITE_RULE[homeomorphism] th)))) THEN
  REWRITE_TAC[]);;

let MOI_S8TA_EMB2_OF = prove
 (`!(x:real^N->bool) y.
     moi_s28_locally_r2 x y \/ moi_s28_locally_half x y ==> moi_s8ta_emb2 x y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s28_locally_r2; moi_s28_locally_half; homeomorphic; moi_s8ta_emb2] THEN
  MESON_TAC[MOI_S8TA_HOMEO_IMAGE]);;

(* Plane and half-plane charts contain embedded open disks in every         *)
(* neighbourhood.                                                           *)

let MOI_S8TA_DISK_IN_NBHD = prove
 (`!(x:real^N->bool) y v.
     (moi_s28_locally_r2 x y \/ moi_s28_locally_half x y) /\
     open_in (subtopology euclidean x) v /\ y IN v
     ==> ?(psi:real^2->real^N) z r.
           &0 < r /\ psi continuous_on ball(z,r) /\
           (!p q. p IN ball(z,r) /\ q IN ball(z,r) /\ psi p = psi q ==> p = q) /\
           IMAGE psi (ball(z,r)) SUBSET v`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_s28_locally_r2; moi_s28_locally_half; homeomorphic] THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `open_in (subtopology euclidean (:real^2))
                  (IMAGE (f:real^N->real^2) (u INTER v))` MP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`g:real^2->real^N`; `u:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
      EXISTS_TAC `x:real^N->bool` THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET] THEN ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
      REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_CONTAINS_BALL]] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^N->real^2) y`) THEN ANTS_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`g:real^2->real^N`; `(f:real^N->real^2) y`; `r:real`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism; IN_UNIV]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ASM_MESON_TAC[];
      UNDISCH_TAC `ball((f:real^N->real^2) y,r) SUBSET IMAGE f (u INTER v)` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE; IN_INTER] THEN
      ASM_MESON_TAC[]];
    SUBGOAL_THEN `open_in (subtopology euclidean {z:real^2 | &0 <= z$2})
                  (IMAGE (h:real^N->real^2) (u INTER v))` MP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`k:real^2->real^N`; `u:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
      EXISTS_TAC `x:real^N->bool` THEN
      ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET] THEN ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
      REWRITE_TAC[OPEN_IN_OPEN]] THEN
    DISCH_THEN(X_CHOOSE_THEN `oo:real^2->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(vec 0:real^2) IN oo` MP_TAC THENL
     [SUBGOAL_THEN `(vec 0:real^2) IN IMAGE (h:real^N->real^2) (u INTER v)` MP_TAC THENL
       [UNDISCH_TAC `(h:real^N->real^2) y = vec 0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `open(oo:real^2->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`k:real^2->real^N`; `(e / &2) % basis 2:real^2`; `e / &4`] THEN
    SUBGOAL_THEN `ball((e / &2) % basis 2:real^2,e / &4) SUBSET
                  {z:real^2 | &0 <= z$2} INTER ball(vec 0,e)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_BALL; IN_BALL_0] THEN
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`(e / &2) % basis 2 - z:real^2`; `2`] COMPONENT_LE_NORM) THEN
        REWRITE_TAC[GSYM dist; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`vec 0:real^2`; `(e / &2) % basis 2:real^2`; `z:real^2`]
          DIST_TRIANGLE) THEN
        REWRITE_TAC[DIST_0; NORM_MUL] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `{z:real^2 | &0 <= z$2}` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`p:real^2`; `q:real^2`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(p:real^2) IN {z:real^2 | &0 <= z$2} /\ q IN {z:real^2 | &0 <= z$2}`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      SUBGOAL_THEN `{z:real^2 | &0 <= z$2} INTER ball(vec 0,e) SUBSET
                    IMAGE (h:real^N->real^2) (u INTER v)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(p:real^2) IN IMAGE (h:real^N->real^2) (u INTER v)` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[]]]);;
(* Two distinct triangles on an edge of a simplicial complex meet exactly    *)
(* in that edge.                                                            *)

let MOI_S8TA_TRI_INTER_EDGE = prove
 (`!(L:(real^N->bool)->bool) e t1 t2.
     simplicial_complex L /\ e IN L /\ aff_dim e = &1 /\
     t1 IN L /\ t2 IN L /\ aff_dim t1 = &2 /\ aff_dim t2 = &2 /\ ~(t1 = t2) /\
     e SUBSET t1 /\ e SUBSET t2
     ==> t1 INTER t2 = e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t1 INTER t2:real^N->bool) face_of t1` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t1 INTER t2:real^N->bool = t1)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(t1:real^N->bool = t2)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(t1:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t1 INTER t2:real^N->bool) < &2` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_AFF_DIM_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) face_of (t1 INTER t2)` ASSUME_TAC THENL
   [MATCH_MP_TAC FACE_OF_SUBSET THEN EXISTS_TAC `t1:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET; SUBSET_INTER] THEN
    MATCH_MP_TAC MOI_SCF_SUBSET_FACE THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`e:real^N->bool`; `t1 INTER t2:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [MATCH_MP_TAC CONVEX_INTER THEN
           ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
           ASM_MESON_TAC[]];
    ASM_INT_ARITH_TAC]);;

(* The unfolding map of two triangles a b c1 and a b c2 is injective on a   *)
(* closed ball at any point of the open edge.                               *)

let MOI_S8TA_UNFOLD_AT = prove
 (`!a b c1 c2:real^N s0.
     ~affine_dependent {a,b,c1} /\ ~affine_dependent {a,b,c2} /\
     ~(a = b) /\ ~(c1 = a) /\ ~(c1 = b) /\ ~(c2 = a) /\ ~(c2 = b) /\
     convex hull {a,b,c1} INTER convex hull {a,b,c2} = convex hull {a,b} /\
     &0 < s0 /\ s0 < &1
     ==> ?r. &0 < r /\
             (!p q:real^2.
                p IN cball(vector[s0;&0],r) /\ q IN cball(vector[s0;&0],r) /\
                a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
                max (--(p$2)) (&0) % (c2 - a) =
                a + q$1 % (b - a) + max (q$2) (&0) % (c1 - a) +
                max (--(q$2)) (&0) % (c2 - a)
                ==> p = q) /\
             (!p:real^2. p IN cball(vector[s0;&0],r)
                         ==> a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
                             max (--(p$2)) (&0) % (c2 - a) IN
                             convex hull {a,b,c1} UNION convex hull {a,b,c2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `min s0 (&1 - s0) / &4` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^2. p IN cball(vector[s0;&0],min s0 (&1 - s0) / &4)
               ==> &0 <= p$1 /\ abs(p$2) <= &1 - p$1`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^2` THEN REWRITE_TAC[IN_CBALL; dist] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`vector[s0;&0] - p:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`vector[s0;&0] - p:real^2`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:real^2`; `q:real^2`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_SCF_UNFOLD_INJ THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `c1:real^N`; `c2:real^N`] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^2`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNION] THEN ASM_CASES_TAC `&0 <= (p:real^2)$2` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC MOI_SCF_UNFOLD_IN THEN ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN MATCH_MP_TAC MOI_SCF_UNFOLD_IN2 THEN ASM_REAL_ARITH_TAC]]);;
(* An injective continuous image of an open planar set inside the domain of *)
(* a 2D chart is open in the space (invariance of domain).                  *)

let MOI_S8TA_EMB_OPEN = prove
 (`!(x:real^N->bool) u (phi:real^N->real^2) phi' (g:real^2->real^N) w.
     open_in (subtopology euclidean x) u /\ homeomorphism (u,IMAGE phi u) (phi,phi') /\
     open w /\ g continuous_on w /\ IMAGE g w SUBSET u /\
     (!p q. p IN w /\ q IN w /\ g p = g q ==> p = q)
     ==> open_in (subtopology euclidean x) (IMAGE g w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `open (IMAGE ((phi:real^N->real^2) o (g:real^2->real^N)) w)` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MAP_EVERY X_GEN_TAC [`p:real^2`; `q:real^2`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!p q. p IN w /\ q IN w /\ (g:real^2->real^N) p = g q ==> p = q`)
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(g:real^2->real^N) p IN u /\ g q IN u` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE (g:real^2->real^N) w =
    {z | z IN u /\ (phi:real^N->real^2) z IN IMAGE (phi o g) w}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; o_THM] THEN
    X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `p:real^2` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `p:real^2` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:real^2` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `p:real^2` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(g:real^2->real^N) p IN u` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]]];
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[]]);;

(* Unfolding at a point y of the relative interior of an edge e on two     *)
(* distinct triangles: given a 2D chart at y, a small open disk maps        *)
(* homeomorphically onto an open subset of the polyhedron containing y and *)
(* lying in the two triangles.                                              *)

let MOI_S8TA_UNFOLD_OPEN = prove
 (`!(L:(real^N->bool)->bool) e t1 t2 y.
     simplicial_complex L /\ e IN L /\ aff_dim e = &1 /\
     t1 IN L /\ t2 IN L /\ aff_dim t1 = &2 /\ aff_dim t2 = &2 /\ ~(t1 = t2) /\
     e SUBSET t1 /\ e SUBSET t2 /\ y IN relative_interior e /\
     moi_s8ta_emb2 (UNIONS L) y
     ==> ?(ff:real^2->real^N) ff' w.
           open w /\ convex w /\ ~(w = {}) /\ homeomorphism (w,IMAGE ff w) (ff,ff') /\
           open_in (subtopology euclidean (UNIONS L)) (IMAGE ff w) /\
           y IN IMAGE ff w /\ IMAGE ff w SUBSET t1 UNION t2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `t1:real^N->bool`]
    MOI_SCF_TRIANGLE_ON_EDGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `t2:real^N->bool`]
    MOI_SCF_TRIANGLE_ON_EDGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `convex hull {a:real^N,b}`;
                 `t1:real^N->bool`; `t2:real^N->bool`] MOI_S8TA_TRI_INTER_EDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `(y:real^N) IN relative_interior (convex hull {a,b})` THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT; IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "yeq")))) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c1:real^N`; `c2:real^N`; `s0:real`]
    MOI_S8TA_UNFOLD_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `ff = \p:real^2. a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
                               max (--(p$2)) (&0) % (c2 - a:real^N)` THEN
  SUBGOAL_THEN `!p:real^2. a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
                           max (--(p$2)) (&0) % (c2 - a:real^N) = ff p`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "ff" THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "img")))) THEN
  SUBGOAL_THEN `(ff:real^2->real^N) continuous_on (:real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "ff" THEN REWRITE_TAC[MOI_SCF_UNFOLD_CONT]; ALL_TAC] THEN
  SUBGOAL_THEN `(ff:real^2->real^N) (vector[s0;&0]) = y` ASSUME_TAC THENL
   [EXPAND_TAC "ff" THEN USE_THEN "yeq" SUBST1_TAC THEN REWRITE_TAC[VECTOR_2] THEN
    REWRITE_TAC[REAL_ARITH `max (&0) (&0) = &0`; REAL_NEG_0; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "yeq" (K ALL_TAC) THEN
  (* the 2D chart at y *)
  UNDISCH_TAC `moi_s8ta_emb2 (UNIONS L) (y:real^N)` THEN REWRITE_TAC[moi_s8ta_emb2] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `phi:real^N->real^2`
    (X_CHOOSE_THEN `phi':real^2->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS L)) (u:real^N->bool)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(GEN_REWRITE_RULE I [OPEN_IN_OPEN] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r1. &0 < r1 /\ !p:real^2. p IN ball(vector[s0;&0],r1)
                                         ==> (ff:real^2->real^N) p IN oo`
  (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `(ff:real^2->real^N) continuous at (vector[s0;&0])` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[INTERIOR_UNIV; IN_UNIV];
      ALL_TAC] THEN
    UNDISCH_TAC `open(oo:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ee:real` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `ee:real`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_BALL] THEN X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ff:real^2->real^N) p IN ball(y,ee)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?rho. &0 < rho /\
                      cball(vector[s0;&0]:real^2,rho) SUBSET cball(vector[s0;&0],r) /\
                      cball(vector[s0;&0]:real^2,rho) SUBSET ball(vector[s0;&0],r1)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min r r1 / &2` THEN REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN
    REPEAT CONJ_TAC THEN TRY GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ff:real^2->real^N) (cball(vector[s0;&0],rho)) SUBSET u`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ff:real^2->real^N) p IN UNIONS L INTER oo` MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [USE_THEN "img" (MP_TAC o SPEC `p:real^2`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_UNION; IN_UNIONS] THEN ASM_MESON_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(vector[s0;&0]:real^2,rho)`; `ff:real^2->real^N`;
                 `IMAGE (ff:real^2->real^N) (cball(vector[s0;&0],rho))`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `ff':real^N->real^2`) THEN
  MAP_EVERY EXISTS_TAC [`ff:real^2->real^N`; `ff':real^N->real^2`;
                        `ball(vector[s0;&0]:real^2,rho)`] THEN
  REWRITE_TAC[OPEN_BALL; CONVEX_BALL; BALL_EQ_EMPTY] THEN
  SUBGOAL_THEN `ball(vector[s0;&0]:real^2,rho) SUBSET cball(vector[s0;&0],rho)`
  ASSUME_TAC THENL [REWRITE_TAC[BALL_SUBSET_CBALL]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`cball(vector[s0;&0]:real^2,rho)`;
                          `IMAGE (ff:real^2->real^N) (cball(vector[s0;&0],rho))`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC MOI_S8TA_EMB_OPEN THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `phi:real^N->real^2`; `phi':real^2->real^N`] THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ASM SET_TAC[];
      REPEAT STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM SET_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vector[s0;&0]:real^2` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN
    USE_THEN "img" MATCH_MP_TAC THEN ASM SET_TAC[]]);;
(* B2: two triangles on e and a 2D chart at y give a plane chart at y.     *)

let MOI_S8TA_EDGE2_R2 = prove
 (`!(L:(real^N->bool)->bool) e t1 t2 y.
     simplicial_complex L /\ e IN L /\ aff_dim e = &1 /\
     t1 IN L /\ t2 IN L /\ aff_dim t1 = &2 /\ aff_dim t2 = &2 /\ ~(t1 = t2) /\
     e SUBSET t1 /\ e SUBSET t2 /\ y IN relative_interior e /\
     moi_s8ta_emb2 (UNIONS L) y
     ==> moi_s28_locally_r2 (UNIONS L) y`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S8TA_UNFOLD_OPEN) THEN
  REWRITE_TAC[moi_s28_locally_r2] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^2->real^N` (X_CHOOSE_THEN `ff':real^N->real^2`
    (X_CHOOSE_THEN `w:real^2->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `IMAGE (ff:real^2->real^N) w` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(INST_TYPE [`:2`,`:N`] HOMEOMORPHIC_TRANS) THEN
  EXISTS_TAC `w:real^2->bool` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`ff:real^2->real^N`; `ff':real^N->real^2`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMEOMORPHIC_CONVEX_OPEN_SETS THEN
    ASM_REWRITE_TAC[CONVEX_UNIV; OPEN_UNIV; UNIV_NOT_EMPTY]]);;

(* B4: three triangles on e allow no 2D chart at y.                        *)

let MOI_S8TA_EDGE3_NO = prove
 (`!(L:(real^N->bool)->bool) e t1 t2 t3 y.
     simplicial_complex L /\ e IN L /\ aff_dim e = &1 /\
     t1 IN L /\ t2 IN L /\ t3 IN L /\
     aff_dim t1 = &2 /\ aff_dim t2 = &2 /\ aff_dim t3 = &2 /\
     ~(t1 = t2) /\ ~(t1 = t3) /\ ~(t2 = t3) /\
     e SUBSET t1 /\ e SUBSET t2 /\ e SUBSET t3 /\ y IN relative_interior e
     ==> ~moi_s8ta_emb2 (UNIONS L) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`; `t1:real^N->bool`;
                 `t2:real^N->bool`; `y:real^N`] MOI_S8TA_UNFOLD_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^2->real^N` (X_CHOOSE_THEN `ff':real^N->real^2`
    (X_CHOOSE_THEN `w:real^2->bool` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS L)) (IMAGE (ff:real^2->real^N) w)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN oo /\ y IN t3` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. z IN relative_interior t3 /\ z IN oo` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(oo INTER closure(relative_interior t3:real^N->bool) = {})` MP_TAC THENL
     [SUBGOAL_THEN `closure(relative_interior t3:real^N->bool) = t3` SUBST1_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `closure(t3:real^N->bool)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CLOSURE_RELATIVE_INTERIOR THEN
          ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
          MATCH_MP_TAC CLOSURE_CLOSED THEN ASM_MESON_TAC[MOI_SCF_SC_CLOSED]];
        ASM SET_TAC[]];
      ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN t1 UNION t2` MP_TAC THENL
   [SUBGOAL_THEN `(z:real^N) IN IMAGE (ff:real^2->real^N) w` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; IN_UNIONS] THEN EXISTS_TAC `t3:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [UNDISCH_TAC `~(t1:real^N->bool = t3)`; UNDISCH_TAC `~(t2:real^N->bool = t3)`] THEN
  REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `z:real^N`] THEN ASM_REWRITE_TAC[]);;

(* Near a point of the relative interior of an edge, the polyhedron lies in *)
(* the edge and the triangles on it (dimension at most 2).                  *)

let MOI_S8TA_LOCAL_EDGE = prove
 (`!(L:(real^N->bool)->bool) e y.
     simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &2) /\
     e IN L /\ aff_dim e = &1 /\ y IN relative_interior e
     ==> ?r. &0 < r /\
             UNIONS L INTER ball(y,r) SUBSET
             e UNION UNIONS {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `y:real^N`] MOI_FSA_LOCAL_STAR) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN X_GEN_TAC `z:real^N` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &1 \/ aff_dim s = &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= aff_dim(s:real^N->bool) /\ aff_dim s <= &2` MP_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_SUBSET]; INT_ARITH_TAC];
    REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    SUBGOAL_THEN `e:real^N->bool = s` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN DISJ2_TAC THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* B3: one triangle on e allows no plane chart at y.                       *)

let MOI_S8TA_EDGE1_NO_R2 = prove
 (`!(L:(real^N->bool)->bool) e t y.
     simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &2) /\
     e IN L /\ aff_dim e = &1 /\ t IN L /\ aff_dim t = &2 /\ e SUBSET t /\
     (!t'. t' IN L /\ aff_dim t' = &2 /\ e SUBSET t' ==> t' = t) /\
     y IN relative_interior e
     ==> ~moi_s28_locally_r2 (UNIONS L) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`; `y:real^N`]
    MOI_S8TA_LOCAL_EDGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS L INTER ball(y:real^N,r) SUBSET t` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `e UNION UNIONS {t | t IN L /\ aff_dim t = &2 /\ (e:real^N->bool) SUBSET t}` THEN
    ASM_REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s28_locally_r2; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:real^N->real^2`
      (X_CHOOSE_THEN `p':real^2->real^N` ASSUME_TAC))))) THEN
  ABBREV_TAC `v = u INTER ball(y:real^N,r)` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean u) (v:real^N->bool) /\ v SUBSET t /\ y IN v`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
      FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (p:real^N->real^2) v)` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_UNIV] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`p':real^2->real^N`; `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism; IN_UNIV] o
    check (fun th -> can (term_match []
      `homeomorphism (u:real^N->bool,(:real^2)) (f,g)`) (concl th))) THEN
  SUBGOAL_THEN `IMAGE (p':real^2->real^N) (IMAGE p v) = v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (\x:real^N. x) v` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET o
        check (fun th -> concl th = `open_in (subtopology euclidean u) (v:real^N->bool)`)) THEN
      ASM SET_TAC[];
      REWRITE_TAC[IMAGE_ID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p':real^2->real^N`; `(:real^2)`; `affine hull (t:real^N->bool)`;
                 `IMAGE (p:real^N->real^2) v`] INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_UNIV; AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL; AFF_DIM_UNIV;
                    DIMINDEX_2] THEN
    REPEAT CONJ_TAC THENL
     [INT_ARITH_TAC;
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `t:real^N->bool`] HULL_SUBSET) THEN
      ASM SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN MAP_EVERY X_GEN_TAC [`x1:real^2`; `x2:real^2`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a1:real^N` STRIP_ASSUME_TAC)
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `a2:real^N` STRIP_ASSUME_TAC) MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a1:real^N) IN u /\ a2 IN u` STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET o
          check (fun th -> concl th = `open_in (subtopology euclidean u) (v:real^N->bool)`)) THEN
        ASM SET_TAC[];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN relative_interior t` ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:real^N->bool) SUBSET relative_interior t` MP_TAC THENL
     [MATCH_MP_TAC RELATIVE_INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) SUBSET e` MP_TAC THENL
   [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(y:real^N) IN relative_interior e` THEN SET_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC]);;

(* B5: no triangle on e allows neither plane nor half-plane charts at y.   *)

let MOI_S8TA_EDGE0_NO = prove
 (`!(L:(real^N->bool)->bool) e y.
     simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &2) /\
     e IN L /\ aff_dim e = &1 /\
     (!t. t IN L /\ aff_dim t = &2 ==> ~(e SUBSET t)) /\ y IN relative_interior e
     ==> ~(moi_s28_locally_r2 (UNIONS L) y \/ moi_s28_locally_half (UNIONS L) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`; `y:real^N`]
    MOI_S8TA_LOCAL_EDGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS L INTER ball(y:real^N,r) SUBSET e` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `e UNION UNIONS {t | t IN L /\ aff_dim t = &2 /\ (e:real^N->bool) SUBSET t}` THEN
    ASM_REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; IN_ELIM_THM; SUBSET_REFL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `y:real^N`; `UNIONS L INTER ball(y:real^N,r)`]
    MOI_S8TA_DISK_IN_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; IN_UNIONS] THEN
      EXISTS_TAC `e:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^2->real^N` (X_CHOOSE_THEN `z:real^2`
    (X_CHOOSE_THEN `rr:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`psi:real^2->real^N`; `ball(z:real^2,rr)`; `e:real^N->bool`]
    INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_BALL] THEN
    MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `e:real^N->bool`] HULL_SUBSET) THEN
    ASM SET_TAC[];
    ASM_REWRITE_TAC[AFF_DIM_BALL; DIMINDEX_2] THEN INT_ARITH_TAC]);;
(* The relative interior of a triangle is open in the polyhedron and        *)
(* homeomorphic to R^2 (dimension at most 2).                               *)

let MOI_S8TA_TRI_OPEN = prove
 (`!(L:(real^N->bool)->bool) t.
     simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &2) /\
     t IN L /\ aff_dim t = &2
     ==> open_in (subtopology euclidean (UNIONS L)) (relative_interior t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `relative_interior t =
                {x | x IN UNIONS L /\
                     !s. s IN L /\ x IN s ==> (t:real^N->bool) SUBSET s}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
        MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `x:real^N`] THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "all")) THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(f:real^N->bool) IN L` ASSUME_TAC THENL
       [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      SUBGOAL_THEN `(t:real^N->bool) SUBSET f` ASSUME_TAC THENL
       [USE_THEN "all" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
        ALL_TAC] THEN
      SUBGOAL_THEN `t:real^N->bool = f` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `aff_dim(f:real^N->bool) <= &2` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `f:real^N->bool`] AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC];
    MATCH_MP_TAC MOI_SCF_SC_OPEN_STAR THEN ASM_REWRITE_TAC[]]);;

let MOI_S8TA_TRI_R2 = prove
 (`!(L:(real^N->bool)->bool) t y.
     simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &2) /\
     t IN L /\ aff_dim t = &2 /\ y IN relative_interior t
     ==> moi_s28_locally_r2 (UNIONS L) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s28_locally_r2] THEN
  EXISTS_TAC `relative_interior t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S8TA_TRI_OPEN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S8TA_RELINT_R2 THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]]);;

(* 2D charts force dimension at most 2.                                     *)

let MOI_S8TA_EMB2_DIM = prove
 (`!(L:(real^N->bool)->bool) s y.
     simplicial_complex L /\ s IN L /\ y IN s /\ moi_s8ta_emb2 (UNIONS L) y
     ==> aff_dim s <= &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s8ta_emb2] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^N->bool`
      (X_CHOOSE_THEN `f:real^N->real^2` (X_CHOOSE_THEN `g:real^2->real^N`
        STRIP_ASSUME_TAC)))))) THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS L)) (u:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN oo` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `open(oo:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `convex(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s INTER ball(y:real^N,r)) = aff_dim s` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN
    ASM_REWRITE_TAC[OPEN_BALL; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `s INTER ball(y:real^N,r) SUBSET u` ASSUME_TAC THENL
   [SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS L` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real^2`; `s INTER ball(y:real^N,r)`; `(:real^2)`]
    INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN) THEN
  REWRITE_TAC[AFFINE_HULL_UNIV; SUBSET_UNIV; AFF_DIM_UNIV; DIMINDEX_2] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CONVEX_INTER; CONVEX_BALL] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (term_match []
      `homeomorphism (u:real^N->bool,IMAGE (f:real^N->real^2) u) (f,g)`) (concl th))) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]]);;

(* Every point of the polyhedron of a simplicial complex lies in the       *)
(* relative interior of a simplex of the complex.                          *)

let MOI_S8TA_CARRIER = prove
 (`!(L:(real^N->bool)->bool) y.
     simplicial_complex L /\ y IN UNIONS L
     ==> ?s. s IN L /\ y IN relative_interior s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `y:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN ASM_MESON_TAC[simplicial_complex]);;

(* ------------------------------------------------------------------------- *)
(* SURF_CHARTS.  Every point lies in the open star of a vertex, which       *)
(* is a plane chart (circle link) or a half-plane chart (arc link); so all  *)
(* points have 2D charts and the dimension is at most 2.  Points of         *)
(* boundary edges have no plane chart (B3, and openness of the plane-chart *)
(* points).  A point without plane chart has a half-plane chart; its        *)
(* carrier is not a triangle, is an edge on exactly one triangle (B2, B5),  *)
(* or is a vertex with an arc link, whose star contains points of such an   *)
(* edge.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S8TA_CMB_FACTS = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> simplicial_complex c /\ lf_simplicial_complex c /\
         (!v. {v} IN c ==> pl_sphere 1 (UNIONS (simplicial_link c v)) \/
                           pl_ball 1 (UNIONS (simplicial_link c v)))`,
  GEN_TAC THEN REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[MOI_SIMPLICIAL_COMPLEX_LF]);;

let MOI_S8TA_CM_CMB = prove
 (`!c:(real^N->bool)->bool.
     combinatorial_manifold 2 c ==> combinatorial_manifold_with_boundary 2 c`,
  SIMP_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary]);;

(* Points of an open star: the simplices containing them contain the       *)
(* vertex.                                                                  *)

let MOI_S8TA_OPEN_STAR_IN = prove
 (`!c (v:real^N) z s.
     z IN moi_sta_open_star c v /\ s IN c /\ z IN s ==> v IN s`,
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S8TA_VERTEX_IN_OPEN_STAR = prove
 (`!c (v:real^N). {v} IN c ==> v IN moi_sta_open_star c v`,
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM; IN_UNIONS] THEN
  MESON_TAC[IN_SING]);;

(* The star charts at a vertex.                                             *)

let MOI_S8TA_STAR_CHARTS = prove
 (`!c (v:real^N) y.
     lf_simplicial_complex c /\ {v} IN c /\
     (pl_sphere 1 (UNIONS (simplicial_link c v)) \/
      pl_ball 1 (UNIONS (simplicial_link c v))) /\
     y IN moi_sta_open_star c v
     ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC))) THENL
   [DISJ1_TAC THEN REWRITE_TAC[moi_s28_locally_r2] THEN
    EXISTS_TAC `moi_sta_open_star c (v:real^N)` THEN
    ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN; MOI_S8TA_CIRCLE_CHART];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_S8TA_ARC_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^2` (X_CHOOSE_THEN `k:real^2->real^N`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `moi_sta_open_star c (v:real^N)`;
                   `h:real^N->real^2`; `k:real^2->real^N`; `y:real^N`] MOI_S8TA_HCHART) THEN
    ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN] THEN
    SUBGOAL_THEN `&0 <= ((h:real^N->real^2) y)$2` MP_TAC THENL
     [SUBGOAL_THEN `(h:real^N->real^2) y IN {z:real^2 | &0 <= z$2}` MP_TAC THENL
       [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [homeomorphism]) THEN
        UNDISCH_TAC `(y:real^N) IN moi_sta_open_star c v` THEN SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM]];
      MESON_TAC[REAL_ARITH `!x. &0 <= x ==> &0 < x \/ x = &0`]]]);;

let MOI_S8TA_CMB_CHART2 = prove
 (`!c:(real^N->bool)->bool y.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ y IN UNIONS c
     ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_STA_OPEN_STAR_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_S8TA_STAR_CHARTS THEN EXISTS_TAC `v:real^N` THEN
  ASM_SIMP_TAC[]);;

let MOI_S8TA_CMB_DIM = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> !s. s IN c ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  MATCH_MP_TAC MOI_S8TA_EMB2_DIM THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN MATCH_MP_TAC MOI_S8TA_CMB_CHART2 THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* (i) Points of boundary edges have no plane chart.                       *)

let MOI_S8TA_BD_NO_R2 = prove
 (`!c:(real^N->bool)->bool y.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ y IN surface_boundary c
     ==> ~moi_s28_locally_r2 (UNIONS c) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_DIM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `(y:real^N) IN surface_boundary c` THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `?t:real^N->bool. {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = {t}`
  (X_CHOOSE_TAC `t:real^N->bool`) THENL
   [REWRITE_TAC[GSYM MOI_FSA_CARD_EQ_1] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) IN c /\ aff_dim t = &2 /\ e SUBSET t /\
                (!t'. t' IN c /\ aff_dim t' = &2 /\ e SUBSET t' ==> t' = t)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = {t:real^N->bool}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s28_locally_r2] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC(GEN_REWRITE_RULE I [OPEN_IN_OPEN] th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?z:real^N. z IN relative_interior e /\ z IN oo` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(oo INTER closure(relative_interior e:real^N->bool) = {})` MP_TAC THENL
     [SUBGOAL_THEN `closure(relative_interior e:real^N->bool) = e` SUBST1_TAC THENL
       [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `closure(e:real^N->bool)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CLOSURE_RELATIVE_INTERIOR THEN
          ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
          MATCH_MP_TAC CLOSURE_CLOSED THEN ASM_MESON_TAC[MOI_SCF_SC_CLOSED]];
        ASM SET_TAC[]];
      ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `t:real^N->bool`;
                 `z:real^N`] MOI_S8TA_EDGE1_NO_R2) THEN
  ASM_REWRITE_TAC[moi_s28_locally_r2] THEN EXISTS_TAC `u:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:real^N) IN UNIONS c` MP_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ASM SET_TAC[]]);;

(* (ii) A point of the relative interior of an edge without plane chart     *)
(* lies on a boundary edge: the edge is on exactly one triangle.           *)

let MOI_S8TA_NONR2_EDGE = prove
 (`!c:(real^N->bool)->bool e y.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     e IN c /\ aff_dim e = &1 /\ y IN relative_interior e /\
     ~moi_s28_locally_r2 (UNIONS c) y
     ==> e SUBSET surface_boundary c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_DIM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s28_locally_half (UNIONS c) (y:real^N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_S8TA_CMB_CHART2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {r | r IN c /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = 1`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `?t:real^N->bool. t IN c /\ aff_dim t = &2 /\ e SUBSET t` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `?t':real^N->bool. t' IN c /\ aff_dim t' = &2 /\ e SUBSET t' /\
                                       ~(t' = t)` THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `~(t:real^N->bool = t')` ASSUME_TAC THENL
         [UNDISCH_TAC `~(t':real^N->bool = t)` THEN MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `t:real^N->bool`;
                       `t':real^N->bool`; `y:real^N`] MOI_S8TA_EDGE2_R2) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `{r | r IN c /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = {t}`
        SUBST1_TAC THENL
         [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
          X_GEN_TAC `r:real^N->bool` THEN EQ_TAC THENL
           [STRIP_TAC THEN
            UNDISCH_TAC `~(?t':real^N->bool. t' IN c /\ aff_dim t' = &2 /\ e SUBSET t' /\
                                             ~(t' = t))` THEN
            REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `r:real^N->bool`) THEN
            ASM_REWRITE_TAC[];
            DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
          REWRITE_TAC[CARD_SING]]];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `y:real^N`]
        MOI_S8TA_EDGE0_NO) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(?t:real^N->bool. t IN c /\ aff_dim t = &2 /\ e SUBSET t)` THEN
        MESON_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[surface_boundary] THEN
  MATCH_MP_TAC(SET_RULE `!x:real^N->bool s. x IN s ==> x SUBSET UNIONS s`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM]);;

(* (ii) Every point without plane chart is on the boundary.               *)

let MOI_S8TA_NONR2_BD = prove
 (`!c:(real^N->bool)->bool y.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ y IN UNIONS c /\
     ~moi_s28_locally_r2 (UNIONS c) y
     ==> y IN surface_boundary c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_DIM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  (* the carrier of a point without plane chart, if not a vertex, is a     *)
  (* boundary edge                                                          *)
  SUBGOAL_THEN
   `!z s. z IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) z /\
          s IN c /\ z IN relative_interior s /\ ~(aff_dim s = &0)
          ==> s SUBSET surface_boundary (c:(real^N->bool)->bool)`
  (LABEL_TAC "nv") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(z:real^N) IN relative_interior s` THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) = &1 \/ aff_dim s = &2` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN
      UNDISCH_TAC `~(s:real^N->bool = {})` THEN REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN
      SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &2` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(aff_dim(s:real^N->bool) = &0)` THEN INT_ARITH_TAC;
      MATCH_MP_TAC MOI_S8TA_NONR2_EDGE THEN EXISTS_TAC `z:real^N` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `z:real^N`]
        MOI_S8TA_TRI_R2) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_S8TA_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THENL
   [ALL_TAC;
    USE_THEN "nv" (MP_TAC o SPECL [`y:real^N`; `s:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]] THEN
  (* the carrier is a vertex v = y *)
  UNDISCH_TAC `aff_dim(s:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `(y:real^N) IN relative_interior {v}` THEN
  REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP (ASSUME `{v:real^N} IN c`) o
    check (fun th -> can (term_match [] `!v:real^N. {v} IN c ==> p v \/ q v`) (concl th))) THENL
   [SUBGOAL_THEN `moi_s28_locally_r2 (UNIONS c) (v:real^N)` MP_TAC THENL
     [REWRITE_TAC[moi_s28_locally_r2] THEN EXISTS_TAC `moi_sta_open_star c (v:real^N)` THEN
      ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN; MOI_S8TA_CIRCLE_CHART;
                   MOI_S8TA_VERTEX_IN_OPEN_STAR];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_S8TA_ARC_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^2` (X_CHOOSE_THEN `k:real^2->real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (term_match []
      `homeomorphism (a:real^N->bool,{z:real^2 | &0 <= z$2}) (f,g)`) (concl th))) THEN
  ABBREV_TAC `z = (k:real^2->real^N) (basis 1)` THEN
  SUBGOAL_THEN `(basis 1:real^2) IN {z:real^2 | &0 <= z$2}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN moi_sta_open_star c v /\ (h:real^N->real^2) z = basis 1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s28_locally_half (UNIONS c) (z:real^N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `moi_sta_open_star c (v:real^N)`;
                   `h:real^N->real^2`; `k:real^2->real^N`; `z:real^N`] MOI_S8TA_HCHART) THEN
    ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^N = v)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(h:real^N->real^2) z = basis 1` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$1`) THEN
    SIMP_TAC[VEC_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN UNIONS c` ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^N) IN moi_sta_open_star c v` THEN
    REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `z:real^N`] MOI_S8TA_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN s'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TA_OPEN_STAR_IN THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `z:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(aff_dim(s':real^N->bool) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `(z:real^N) IN relative_interior {a}` THEN
    UNDISCH_TAC `(v:real^N) IN {a}` THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s':real^N->bool) SUBSET surface_boundary c` MP_TAC THENL
   [USE_THEN "nv" MATCH_MP_TAC THEN EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S8TA_HALF_NOT_R2 THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* Combinatorial 2-manifolds without boundary have plane charts everywhere. *)

let MOI_S8TA_CM_ALL_R2 = prove
 (`!c:(real^N->bool)->bool y.
     FINITE c /\ combinatorial_manifold 2 c /\ y IN UNIONS c
     ==> moi_s28_locally_r2 (UNIONS c) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `combinatorial_manifold 2 (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_STA_OPEN_STAR_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_s28_locally_r2] THEN EXISTS_TAC `moi_sta_open_star c (v:real^N)` THEN
  ASM_SIMP_TAC[MOI_STA_OPEN_STAR_OPEN; MOI_S8TA_CIRCLE_CHART]);;

(* ------------------------------------------------------------------------- *)
(* The theorem SURF_CHARTS.                                                  *)
(* ------------------------------------------------------------------------- *)

let SURF_CHARTS = prove
 (MOI_S28_SURF_CHARTS,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `surface_boundary c SUBSET UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[surface_boundary; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    ASM_MESON_TAC[MOI_S8TA_NONR2_BD];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~moi_s28_locally_r2 (UNIONS c) (y:real^N)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S8TA_BD_NO_R2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_S8TA_CMB_CHART2) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    DISCH_TAC THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_S8TA_BD_NO_R2) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S8TA_CM_ALL_R2 THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* POLYGON_COMPLEX.  A PL 1-sphere j is a polyhedron with line charts       *)
(* (j minus a point is homeomorphic to R^1), so MOI_S4L_LINE_CHART_COMPLEX  *)
(* triangulates it with every vertex on exactly two edges; the vertex links *)
(* are then two points, PL 0-spheres.                                       *)
(* ------------------------------------------------------------------------- *)

(* Two distinct points form a PL 0-sphere.  (As MOI_FCL_PL_SPHERE_0 of      *)
(* pc_moi_fnd_collar, restated here to keep the load closure small.)       *)

let MOI_S8TA_PL_SPHERE_0 = prove
 (`!p q:real^N. ~(p = q) ==> pl_sphere 0 {p,q}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY EXISTS_TAC [`segment[p:real^N,q]`; `\x:real^N. x`; `\x:real^N. x`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier(segment[p:real^N,q]) = {p,q}` SUBST1_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SIMP_TAC[RELATIVE_FRONTIER_OF_CONVEX_HULL; AFFINE_INDEPENDENT_2] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_2] THEN
    ASM_SIMP_TAC[SET_RULE `~(p:real^N = q) ==> {p,q} DELETE p = {q} /\ {p,q} DELETE q = {p}`;
                 CONVEX_HULL_SING] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{{p:real^N},{q}}` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
              POLYTOPE_SING; UNIONS_2] THEN
  SET_TAC[]);;

(* Faces of a segment missing one end lie in the other end.               *)

let MOI_S8TA_FACE_SEG = prove
 (`!(s:real^N->bool) v a. s face_of segment[v,a] /\ ~(v IN s) ==> s SUBSET {a}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{v:real^N,a}`; `s:real^N->bool`] FACE_OF_CONVEX_HULL_SUBSET) THEN
  ASM_SIMP_TAC[FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s' SUBSET {a:real^N}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `s':real^N->bool`] HULL_SUBSET) THEN
    UNDISCH_TAC `~((v:real^N) IN s)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `s' SUBSET {v:real^N,a}` THEN SET_TAC[];
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull {a:real^N}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CONVEX_HULL_SING; SUBSET_REFL]]]);;

(* The link of a vertex of a 1-complex on exactly two edges.               *)

let MOI_S8TA_K1_LINK = prove
 (`!(K:(real^N->bool)->bool) v.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\ {v} IN K /\
     CARD {e | e IN K /\ aff_dim e = &1 /\ v IN e} = 2
     ==> pl_sphere 0 (UNIONS (simplicial_link K v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?e1 e2:real^N->bool. ~(e1 = e2) /\
                  {e | e IN K /\ aff_dim e = &1 /\ v IN e} = {e1,e2}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_FC2_CARD_EQ_2] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_SCF_SC_FINITE]; SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^N->bool. e IN K /\ aff_dim e = &1 /\ v IN e <=> e = e1 \/ e = e2`
  (LABEL_TAC "E") THENL
   [GEN_TAC THEN
    UNDISCH_TAC `{e | e IN K /\ aff_dim e = &1 /\ v IN e} = {e1,e2:real^N->bool}` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e1:real^N->bool) IN K /\ aff_dim e1 = &1 /\ v IN e1 /\
                (e2:real^N->bool) IN K /\ aff_dim e2 = &1 /\ v IN e2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "E" (fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `e1:real^N->bool`]
    MOI_S4L_K1_EDGE_AT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `e2:real^N->bool`]
    MOI_S4L_K1_EDGE_AT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(a:real^N = b)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(e1:real^N->bool = e2)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (simplicial_link K (v:real^N)) = {a,b}` SUBST1_TAC THENL
   [ALL_TAC; MATCH_MP_TAC MOI_S8TA_PL_SPHERE_0 THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `s SUBSET (t:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(t:real^N->bool) = -- &1 \/ aff_dim t = &0 \/ aff_dim t = &1`
    MP_TAC THENL
     [MP_TAC(ISPEC `t:real^N->bool` AFF_DIM_GE) THEN
      SUBGOAL_THEN `aff_dim(t:real^N->bool) <= &1` MP_TAC THENL
       [ASM_MESON_TAC[]; INT_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 MP_TAC (DISJ_CASES_THEN2 MP_TAC ASSUME_TAC)) THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(v:real^N) IN {}` THEN REWRITE_TAC[NOT_IN_EMPTY];
      REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `c0:real^N` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `(v:real^N) IN {c0}` THEN UNDISCH_TAC `~((v:real^N) IN s)` THEN
      UNDISCH_TAC `(x:real^N) IN s` THEN UNDISCH_TAC `s SUBSET {c0:real^N}` THEN SET_TAC[];
      USE_THEN "E" (MP_TAC o SPEC `t:real^N->bool`) THEN
      REWRITE_TAC[ASSUME `(t:real^N->bool) IN K`; ASSUME `(v:real^N) IN t`;
                  ASSUME `aff_dim(t:real^N->bool) = &1`] THEN
      STRIP_TAC THENL
       [MP_TAC(ISPECL [`s:real^N->bool`; `v:real^N`; `a:real^N`] MOI_S8TA_FACE_SEG);
        MP_TAC(ISPECL [`s:real^N->bool`; `v:real^N`; `b:real^N`] MOI_S8TA_FACE_SEG)] THEN
      (ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
      UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[]];
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `{a:real^N}` THEN REWRITE_TAC[IN_SING] THEN
      SUBGOAL_THEN `~(v:real^N = a)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `e1:real^N->bool` THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      EXISTS_TAC `{b:real^N}` THEN REWRITE_TAC[IN_SING] THEN
      SUBGOAL_THEN `~(v:real^N = b)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `e2:real^N->bool` THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]]]);;

(* A PL 1-sphere has line charts: minus a point it is homeomorphic to R^1   *)
(* (the relative frontier of a 2-simplex punctured at one point).          *)

let MOI_S8TA_SPHERE1_LINE_CHARTS = prove
 (`!j:real^N->bool. pl_sphere 1 j ==> moi_s4l_line_charts j`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `convex(k:real^N->bool) /\ bounded k /\ aff_dim k = &2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                  AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^N. a IN relative_frontier k
                ==> (relative_frontier k DELETE a) homeomorphic (:real^1)`
  (LABEL_TAC "punct") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN THEN
    ASM_REWRITE_TAC[AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_1] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_s4l_line_charts] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  (* a point a' of the relative frontier other than g x *)
  SUBGOAL_THEN `?a':real^N. a' IN relative_frontier k /\ ~(a' = (g:real^N->real^N) x)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(g:real^N->real^N) x IN relative_frontier k` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(relative_frontier k DELETE (g:real^N->real^N) x) homeomorphic (:real^1)`
    ASSUME_TAC THENL [USE_THEN "punct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(relative_frontier k DELETE (g:real^N->real^N) x = {})` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC
       `(relative_frontier k DELETE (g:real^N->real^N) x) homeomorphic (:real^1)` THEN
      ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; UNIV_NOT_EMPTY];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real^N) a' IN j /\ ~(x = f a')` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(a':real^N = (g:real^N->real^N) x)` THEN
    FIRST_X_ASSUM SUBST1_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j DELETE (f:real^N->real^N) a') homeomorphic (:real^1)` MP_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:N`,`:M`; `:1`,`:P`] HOMEOMORPHIC_TRANS) THEN
    EXISTS_TAC `relative_frontier k DELETE (a':real^N)` THEN
    CONJ_TAC THENL [ALL_TAC; USE_THEN "punct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier k:real^N->bool`; `j:real^N->bool`] THEN
    ASM_REWRITE_TAC[DELETE_SUBSET] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^1` (X_CHOOSE_TAC `h':real^1->real^N`)) THEN
  MAP_EVERY EXISTS_TAC [`(:real^N) DELETE (f:real^N->real^N) a'`;
                        `h:real^N->real^1`; `h':real^1->real^N`] THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN ASM_REWRITE_TAC[IN_DELETE; IN_UNIV] THEN
  SUBGOAL_THEN `j INTER ((:real^N) DELETE (f:real^N->real^N) a') = j DELETE f a'`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism (j DELETE (f:real^N->real^N) a',(:real^1)) (h,h')` THEN
  DISCH_THEN(fun th -> MP_TAC th THEN
    SUBST1_TAC(CONJUNCT1(CONJUNCT2(GEN_REWRITE_RULE I [homeomorphism] th)))) THEN
  SIMP_TAC[OPEN_UNIV]);;

(* The theorem POLYGON_COMPLEX.                                              *)

let POLYGON_COMPLEX = prove
 (MOI_S28_POLYGON_COMPLEX,
  X_GEN_TAC `j:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`j:real^N->bool`; `{}:real^N->bool`] MOI_S4L_LINE_CHART_COMPLEX) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S8TA_SPHERE1_LINE_CHARTS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_SC_FINITE];
    REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TA_K1_LINK THEN ASM_SIMP_TAC[]];
    UNDISCH_TAC `pl_sphere 1 (j:real^N->bool)` THEN
    REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    SUBGOAL_THEN `j = IMAGE (f:real^N->real^N) (relative_frontier k)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN
    SUBGOAL_THEN `convex(k:real^N->bool) /\ bounded k /\ aff_dim k = &2` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                    AFF_DIM_SIMPLEX];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]]);;

