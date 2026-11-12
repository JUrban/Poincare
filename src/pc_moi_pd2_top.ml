(* ========================================================================= *)
(* pc_moi_pd2_top (step M7 of route M): the topological leaves of the 2D     *)
(* theorem MOI_SMO_PD2_STATEMENT.                                            *)
(*   D5  MOI_SMO_LOCAL_HOMEO_SPHERE: a local homeomorphism of a compact     *)
(*       connected locally path-connected set onto S^2 is a homeomorphism.  *)
(*   D4b MOI_SMO_VERTEX_DEGREE: the conical blow-up of an injective map     *)
(*       has winding number +1 or -1.                                       *)
(*   D4a MOI_SMO_CREASE_ORIENT: no folds along a crease.                    *)
(* ========================================================================= *)

needs "src/pc_moi_smo_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* D5.  A local homeomorphism is continuous; then the library's covering    *)
(* space argument (PROPER_LOCAL_HOMEOMORPHISM_GLOBAL) applies, since a map  *)
(* from a compact set is proper and S^2 is simply connected.                *)
(* ------------------------------------------------------------------------- *)

let MOI_PDT_LOCAL_HOMEOMORPHISM_CONTINUOUS = prove
 (`!f:real^M->real^N s t.
        (!x. x IN s
             ==> ?u v g. x IN u /\
                         open_in (subtopology euclidean s) u /\
                         open_in (subtopology euclidean t) v /\
                         homeomorphism (u,v) (f,g))
        ==> f continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `x:real^M`; `s:real^M->bool`;
                 `u:real^M->bool`] CONTINUOUS_WITHIN_OPEN_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]);;

let MOI_SMO_LOCAL_HOMEO_SPHERE = prove
 (`!u:N->bool. MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`X:real^N->bool`; `f:real^N->real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^3) continuous_on X` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDT_LOCAL_HOMEOMORPHISM_CONTINUOUS THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PROPER_LOCAL_HOMEOMORPHISM_GLOBAL THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[PATH_CONNECTED_EQ_CONNECTED_LPC];
    MATCH_MP_TAC SIMPLY_CONNECTED_SPHERE THEN
    REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC PROPER_MAP_FROM_COMPACT THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN
    ASM_SIMP_TAC[CLOSED_SUBSET; COMPACT_IMP_CLOSED];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* D4b.  Degree one at a conical vertex.  Plan: the image under G of a      *)
(* small circle is a simple closed curve with G(0) = 0 inside it            *)
(* (invariance of domain), so it winds +1 or -1 times around 0              *)
(* (SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE); it is a nearby loop of the   *)
(* image of the same circle under P, which is a positive multiple of the    *)
(* image of the unit circle under P.                                        *)
(* ------------------------------------------------------------------------- *)

(* The image of the centre of a closed ball under a continuous injective    *)
(* map lies inside the image of the boundary sphere: the image W of the     *)
(* open ball is open (invariance of domain), connected and bounded, misses  *)
(* the image S of the sphere, and is closed in the complement of S, so it   *)
(* is the whole component of f a in the complement of S.                    *)

let MOI_PDT_INSIDE_IMAGE_SPHERE = prove
 (`!f:real^N->real^N a r.
        &0 < r /\ f continuous_on cball(a,r) /\
        (!x y. x IN cball(a,r) /\ y IN cball(a,r) /\ f x = f y ==> x = y)
        ==> f a IN inside(IMAGE f (sphere(a,r)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (ball(a,r)) INTER
                IMAGE f (sphere(a,r)) = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `x:real^N = y` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL; SPHERE_SUBSET_CBALL];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN ball(a,r)` THEN
    UNDISCH_TAC `(y:real^N) IN sphere(a,r)` THEN
    ASM_REWRITE_TAC[IN_BALL; IN_SPHERE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (f:real^N->real^N) (ball(a,r)))` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_BALL] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; BALL_SUBSET_CBALL];
      ASM_MESON_TAC[SUBSET; BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(IMAGE (f:real^N->real^N) (ball(a,r)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[CONNECTED_BALL] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (f:real^N->real^N) (cball(a,r)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->real^N) a IN IMAGE f (ball(a,r))` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (cball(a,r)) =
                IMAGE f (ball(a,r)) UNION IMAGE f (sphere(a,r))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION; BALL_UNION_SPHERE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^N) (ball(a,r)) SUBSET
    connected_component ((:real^N) DIFF IMAGE f (sphere(a,r))) (f a)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) (ball(a,r)) INTER
                 IMAGE f (sphere(a,r)) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^N) DIFF IMAGE (f:real^N->real^N) (sphere(a,r))`;
                 `(f:real^N->real^N) a`] CONNECTED_COMPONENT_SUBSET) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `connected_component ((:real^N) DIFF IMAGE f (sphere(a,r)))
                        ((f:real^N->real^N) a) =
    IMAGE f (ball(a,r))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^N) DIFF IMAGE (f:real^N->real^N) (sphere(a,r))`;
                   `(f:real^N->real^N) a`] CONNECTED_CONNECTED_COMPONENT) THEN
    REWRITE_TAC[CONNECTED_CLOPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (f:real^N->real^N) (ball(a,r))`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[CLOSED_IN_CLOSED] THEN
        EXISTS_TAC `IMAGE (f:real^N->real^N) (cball(a,r))` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`IMAGE (f:real^N->real^N) (cball(a,r)) =
           IMAGE f (ball(a,r)) UNION IMAGE f (sphere(a,r))`;
          `IMAGE (f:real^N->real^N) (ball(a,r)) SUBSET
           connected_component ((:real^N) DIFF IMAGE f (sphere(a,r))) (f a)`;
          `connected_component ((:real^N) DIFF IMAGE f (sphere(a,r)))
                               ((f:real^N->real^N) a) SUBSET
           (:real^N) DIFF IMAGE f (sphere(a,r))`] THEN
        SET_TAC[]];
      UNDISCH_TAC `(f:real^N->real^N) a IN IMAGE f (ball(a,r))` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[inside; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(f:real^N->real^N) a IN IMAGE f (ball(a,r))`;
      `IMAGE (f:real^N->real^N) (ball(a,r)) INTER
       IMAGE f (sphere(a,r)) = {}`] THEN
    SET_TAC[];
    REWRITE_TAC[ASSUME
     `connected_component ((:real^N) DIFF IMAGE f (sphere(a,r)))
                          ((f:real^N->real^N) a) =
      IMAGE f (ball(a,r))`] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^N->real^N) (cball(a,r))` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[COMPACT_IMP_BOUNDED];
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL]]]);;

(* A continuous positively homogeneous map without zeros off 0 grows at    *)
(* least linearly.                                                          *)

let MOI_PDT_HOMOG_LOWER_BOUND = prove
 (`!P:complex->complex.
        P continuous_on (:complex) /\
        (!t x. &0 <= t ==> P(Cx t * x) = Cx t * P x) /\
        (!x. ~(x = Cx(&0)) ==> ~(P x = Cx(&0)))
        ==> ?m. &0 < m /\ !z. m * norm z <= norm(P z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:complex. norm((P:complex->complex) z)`;
                 `sphere(Cx(&0),&1)`] CONTINUOUS_ATTAINS_INF) THEN
  REWRITE_TAC[COMPACT_SPHERE; SPHERE_EQ_EMPTY; o_DEF] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SPHERE; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `norm((P:complex->complex) z0)` THEN CONJ_TAC THENL
   [REWRITE_TAC[NORM_POS_LT; COMPLEX_VEC_0] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `norm(z0:complex) = &1` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN
  ASM_CASES_TAC `z = Cx(&0)` THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_0; REAL_MUL_RZERO; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(z:complex)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; COMPLEX_VEC_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(P:complex->complex) z =
                Cx(norm z) * P(z / Cx(norm(z:complex)))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`norm(z:complex)`;
                                   `z / Cx(norm(z:complex))`]) THEN
    REWRITE_TAC[NORM_POS_LE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `~(Cx(norm(z:complex)) = Cx(&0))` MP_TAC THENL
     [REWRITE_TAC[CX_INJ] THEN UNDISCH_TAC `&0 < norm(z:complex)` THEN
      REAL_ARITH_TAC;
      CONV_TAC COMPLEX_FIELD];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NORM] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NORM] THEN
  MATCH_MP_TAC REAL_DIV_REFL THEN
  UNDISCH_TAC `&0 < norm(z:complex)` THEN REAL_ARITH_TAC);;

(* Rouche-type comparison on a circle about 0.                              *)

let MOI_PDT_WINDING_NEARBY = prove
 (`!G P:complex->complex rho.
        &0 < rho /\ P continuous_on sphere(Cx(&0),rho) /\
        G continuous_on sphere(Cx(&0),rho) /\
        (!z. z IN sphere(Cx(&0),rho) ==> norm(G z - P z) < norm(P z))
        ==> winding_number(G o circlepath(Cx(&0),rho),Cx(&0)) =
            winding_number(P o circlepath(Cx(&0),rho),Cx(&0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_NEARBY_LOOPS_EQ THEN
  ASM_SIMP_TAC[PATH_CONTINUOUS_IMAGE; PATH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH;
               REAL_LT_IMP_LE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
               PATHSTART_CIRCLEPATH; PATHFINISH_CIRCLEPATH] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; COMPLEX_SUB_RZERO] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `circlepath(Cx(&0),rho) t IN
                path_image(circlepath(Cx(&0),rho))` MP_TAC THENL
   [REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE]]);;

(* For P positively homogeneous without zeros off 0, the image under P of  *)
(* the circle of radius rho is a positive multiple of that of the unit      *)
(* circle, hence has the same winding number about 0.                       *)

let MOI_PDT_WINDING_HOMOG_SCALE = prove
 (`!P:complex->complex rho.
        &0 < rho /\ P continuous_on (:complex) /\
        (!t x. &0 <= t ==> P(Cx t * x) = Cx t * P x) /\
        (!x. ~(x = Cx(&0)) ==> ~(P x = Cx(&0)))
        ==> winding_number(P o circlepath(Cx(&0),rho),Cx(&0)) =
            winding_number(P o circlepath(Cx(&0),&1),Cx(&0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WINDING_NUMBER_LOOPS_LINEAR_EQ THEN
  REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATHSTART_CIRCLEPATH;
              PATHFINISH_CIRCLEPATH] THEN
  SUBGOAL_THEN `!c. path c ==> path((P:complex->complex) o c)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PATH_CIRCLEPATH] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; CIRCLEPATH; COMPLEX_ADD_LID; COMPLEX_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MP_TAC(SPEC `cexp(Cx(&2) * Cx pi * ii * Cx(drop t))`
   (ASSUME `!x. ~(x = Cx(&0)) ==> ~((P:complex->complex) x = Cx(&0))`)) THEN
  REWRITE_TAC[CEXP_NZ] THEN
  SPEC_TAC(`(P:complex->complex)(cexp(Cx(&2) * Cx pi * ii * Cx(drop t)))`,
           `w:complex`) THEN
  X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_SEGMENT; NOT_EXISTS_THM; COMPLEX_CMUL] THEN
  X_GEN_TAC `s:real` THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (&1 - s) + s * rho` MP_TAC THENL
   [ASM_CASES_TAC `s = &1` THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC;
      MP_TAC(SPECL [`s:real`; `rho:real`] REAL_LE_MUL) THEN
      MAP_EVERY UNDISCH_TAC [`&0 <= s`; `s <= &1`; `~(s = &1)`;
                             `&0 < rho`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx(&1 - s) * w + Cx s * Cx rho * w =
                Cx((&1 - s) + s * rho) * w` SUBST1_TAC THENL
   [REWRITE_TAC[CX_ADD; CX_MUL; CX_SUB] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < (&1 - s) + s * rho` THEN
  REAL_ARITH_TAC);;

(* The image under an injective continuous G with G 0 = 0 of a circle      *)
(* about 0 winds +1 or -1 times around 0.                                   *)

let MOI_PDT_WINDING_SIMPLE_IMAGE = prove
 (`!G:complex->complex rho.
        &0 < rho /\ G continuous_on cball(Cx(&0),rho) /\
        (!x y. x IN cball(Cx(&0),rho) /\ y IN cball(Cx(&0),rho) /\ G x = G y
               ==> x = y) /\
        G(Cx(&0)) = Cx(&0)
        ==> winding_number(G o circlepath(Cx(&0),rho),Cx(&0)) = Cx(&1) \/
            winding_number(G o circlepath(Cx(&0),rho),Cx(&0)) = --Cx(&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(G:complex->complex) o circlepath(Cx(&0),rho)`
    SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN
    SIMP_TAC[SIMPLE_PATH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE;
             REAL_LT_IMP_NZ; ASSUME `&0 < rho`] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SPHERE_SUBSET_CBALL; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(&0) IN inside(path_image((G:complex->complex) o
                                circlepath(Cx(&0),rho)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN
    SIMP_TAC[PATH_IMAGE_CIRCLEPATH; REAL_LT_IMP_LE; ASSUME `&0 < rho`] THEN
    SUBGOAL_THEN
     `(G:complex->complex)(Cx(&0)) IN inside(IMAGE G (sphere(Cx(&0),rho)))`
    MP_TAC THENL
     [MATCH_MP_TAC MOI_PDT_INSIDE_IMAGE_SPHERE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* The leaf D4b, MOI_SMO_VERTEX_DEGREE.                                     *)

let MOI_SMO_VERTEX_DEGREE = prove
 (`MOI_SMO_VERTEX_DEGREE_STATEMENT`,
  REWRITE_TAC[MOI_SMO_VERTEX_DEGREE_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`G:complex->complex`; `P:complex->complex`;
                       `u:complex->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\t. (P:complex->complex)(cexp(ii * Cx(&2 * pi * drop t)))) =
    P o circlepath(Cx(&0),&1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; CIRCLEPATH] THEN
    X_GEN_TAC `t:real^1` THEN AP_TERM_TAC THEN
    REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_MUL_LID; CX_MUL] THEN
    AP_TERM_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPEC `P:complex->complex` MOI_PDT_HOMOG_LOWER_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC
   `!e. &0 < e
        ==> ?r. &0 < r /\
                !x:complex. norm x < r
                            ==> norm((G:complex->complex) x -
                                     (P:complex->complex) x) <= e * norm x` THEN
  DISCH_THEN(MP_TAC o SPEC `m / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open(u:complex->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&0)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?rho. &0 < rho /\ rho < r /\ cball(Cx(&0),rho) SUBSET u`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min r r1 / &2` THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < r`; `&0 < r1`] THEN REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`&0 < r`; `&0 < r1`] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(Cx(&0),r1)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < r`; `&0 < r1`] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:complex->complex`; `rho:real`]
    MOI_PDT_WINDING_SIMPLE_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:complex->complex`; `P:complex->complex`; `rho:real`]
    MOI_PDT_WINDING_NEARBY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SPHERE_SUBSET_CBALL; SUBSET_TRANS];
      ALL_TAC] THEN
    X_GEN_TAC `z:complex` THEN
    REWRITE_TAC[IN_SPHERE; dist; COMPLEX_SUB_LZERO; NORM_NEG] THEN
    DISCH_TAC THEN
    MP_TAC(SPEC `z:complex`
     (ASSUME `!z:complex. m * norm z <= norm((P:complex->complex) z)`)) THEN
    MP_TAC(SPEC `z:complex`
     (ASSUME `!x:complex. norm x < r
                          ==> norm((G:complex->complex) x -
                                   (P:complex->complex) x) <= m / &2 * norm x`)) THEN
    REWRITE_TAC[ASSUME `norm(z:complex) = rho`; ASSUME `rho < r`] THEN
    SUBGOAL_THEN `&0 < m * rho` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:complex->complex`; `rho:real`]
    MOI_PDT_WINDING_HOMOG_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* D4a.  No folds along a crease.  Plan: invert Gp near 0 (inverse function *)
(* theorem, g), and put H = g o Gm.  H is the identity on the first axis    *)
(* near 0, so its derivative C at 0 fixes basis 1, and det C has the sign   *)
(* of det DGp(0) det DGm(0).  If that sign were negative, H would push      *)
(* points just below the axis to points just above it, so Gm(x) = Gp(y)     *)
(* with x below and y above the axis, contradicting injectivity of G.       *)
(* ------------------------------------------------------------------------- *)

let MOI_PDT_HAS_DERIVATIVE_IMP_LINEAR = prove
 (`!f:real^M->real^N f' net. (f has_derivative f') net ==> linear f'`,
  SIMP_TAC[has_derivative]);;

let MOI_PDT_CONTINUOUS_AT_NBHD = prove
 (`!f:real^M->real^N x s.
        f continuous (at x) /\ open s /\ f x IN s
        ==> ?d. &0 < d /\ !y. norm(y - x) < d ==> f y IN s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o
    GEN_REWRITE_RULE I [CONTINUOUS_AT_OPEN]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^M` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  ASM_REWRITE_TAC[]);;

(* The determinant of a linear map of the plane fixing basis 1.            *)

let MOI_PDT_DET2_FIX_BASIS1 = prove
 (`!C:real^2->real^2. C(basis 1) = basis 1 ==> det(matrix C) = (C(basis 2))$2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DET_2] THEN
  SIMP_TAC[MATRIX_COMPONENT; DIMINDEX_2; ARITH] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC);;

(* A map that is the identity on the first axis near 0 has a derivative    *)
(* at 0 fixing basis 1.                                                     *)

let MOI_PDT_AXIS_DERIVATIVE = prove
 (`!H:real^2->real^2 C d.
        (H has_derivative C) (at (vec 0)) /\ &0 < d /\
        (!s. abs s < d ==> H(s % basis 1) = s % basis 1)
        ==> C(basis 1) = basis 1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "der"))
             (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ax"))) THEN
  SUBGOAL_THEN `(H:real^2->real^2)(vec 0) = vec 0` ASSUME_TAC THENL
   [USE_THEN "ax" (MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[REAL_ABS_0; VECTOR_MUL_LZERO; ASSUME `&0 < d`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN DISCH_TAC THEN
  USE_THEN "der" (MP_TAC o SPEC
   `norm((C:real^2->real^2)(basis 1) - basis 1) / &2`) THEN
  REWRITE_TAC[REAL_HALF; ASSUME
   `&0 < norm((C:real^2->real^2)(basis 1) - basis 1)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "est"))) THEN
  SUBGOAL_THEN `?s. &0 < s /\ s < d /\ s < d1` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min d d1 / &2` THEN
    MAP_EVERY UNDISCH_TAC [`&0 < d`; `&0 < d1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs s = s` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(basis 1:real^2) = &1` ASSUME_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `(C:real^2->real^2)(s % basis 1) = s % C(basis 1)`
  ASSUME_TAC THENL [ASM_MESON_TAC[LINEAR_CMUL]; ALL_TAC] THEN
  USE_THEN "est" (MP_TAC o SPEC `s % basis 1:real^2`) THEN
  USE_THEN "ax" (MP_TAC o SPEC `s:real`) THEN
  REWRITE_TAC[ASSUME `abs s = s`; ASSUME `s < d`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; NORM_MUL; ASSUME `abs s = s`;
              ASSUME `norm(basis 1:real^2) = &1`; REAL_MUL_RID;
              ASSUME `s < d1`; ASSUME `(H:real^2->real^2)(vec 0) = vec 0`;
              ASSUME `(C:real^2->real^2)(s % basis 1) = s % C(basis 1)`] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL; ASSUME `abs s = s`] THEN
  REWRITE_TAC[ISPECL [`basis 1:real^2`; `(C:real^2->real^2)(basis 1)`]
                     NORM_SUB] THEN
  SUBGOAL_THEN `&0 < s * norm((C:real^2->real^2)(basis 1) - basis 1)`
  MP_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* If the derivative C of H at 0 (H 0 = 0) maps basis 2 below the axis,    *)
(* then H maps the points just below 0 on the second axis strictly above   *)
(* the first axis.                                                          *)

let MOI_PDT_NO_FOLD_CORE = prove
 (`!H:real^2->real^2 C.
        (H has_derivative C) (at (vec 0)) /\ H(vec 0) = vec 0 /\
        (C(basis 2))$2 < &0
        ==> ?d. &0 < d /\
                !s. &0 < s /\ s < d ==> &0 < (H(--(s % basis 2)))$2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_DERIVATIVE_AT_ALT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "der"))
             STRIP_ASSUME_TAC) THEN
  USE_THEN "der"
   (MP_TAC o SPEC `--(((C:real^2->real^2)(basis 2))$2) / &2`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `((C:real^2->real^2)(basis 2))$2 < &0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "est"))) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(basis 2:real^2) = &1` ASSUME_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `abs s = s` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(C:real^2->real^2)(--(s % basis 2)) = --(s % C(basis 2))`
  ASSUME_TAC THENL [ASM_MESON_TAC[LINEAR_CMUL; LINEAR_NEG]; ALL_TAC] THEN
  USE_THEN "est" (MP_TAC o SPEC `--(s % basis 2):real^2`) THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; NORM_NEG; NORM_MUL; ASSUME `abs s = s`;
              ASSUME `norm(basis 2:real^2) = &1`; REAL_MUL_RID;
              ASSUME `s < d`; ASSUME `(H:real^2->real^2)(vec 0) = vec 0`;
              ASSUME `(C:real^2->real^2)(--(s % basis 2)) =
                      --(s % C(basis 2))`] THEN
  MP_TAC(ISPECL
   [`(H:real^2->real^2)(--(s % basis 2)) -
     --(s % (C:real^2->real^2)(basis 2))`; `2`] COMPONENT_LE_NORM) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_NEG_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  SUBGOAL_THEN `&0 < s * --(((C:real^2->real^2)(basis 2))$2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((C:real^2->real^2)(basis 2))$2 < &0` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Signs: if k a = 1 and a b < 0 then k b < 0.                           *)

let MOI_PDT_SIGN_LEMMA = prove
 (`!a b k. k * a = &1 /\ a * b < &0 ==> k * b < &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(k * b) * (a * a) = a * b` ASSUME_TAC THENL
   [UNDISCH_TAC `k * a = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k * b:real`; `a * a:real`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[REAL_LE_SQUARE] THEN
  UNDISCH_TAC `a * b < &0` THEN REAL_ARITH_TAC);;

(* Two smooth maps agreeing on the first axis, with invertible derivatives *)
(* at 0 of opposite orientations, fold: some point strictly below the axis *)
(* and some point strictly above it have the same image.                   *)

let MOI_PDT_FOLD_POINT = prove
 (`!Gp Gm:real^2->real^2 u.
        open u /\ vec 0 IN u /\ smooth_map_on u Gp /\ smooth_map_on u Gm /\
        (!x. x IN u /\ x$2 = &0 ==> Gp x = Gm x) /\
        ~(det(matrix(frechet_derivative Gp (at (vec 0)))) = &0) /\
        det(matrix(frechet_derivative Gp (at (vec 0)))) *
        det(matrix(frechet_derivative Gm (at (vec 0)))) < &0
        ==> ?x y. x IN u /\ y IN u /\ x$2 < &0 /\ &0 < y$2 /\ Gm x = Gp y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "axis") STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `!x. x IN u
        ==> ((Gp:real^2->real^2) has_derivative
             frechet_derivative Gp (at x)) (at x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_HAS_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((Gm:real^2->real^2) has_derivative
     frechet_derivative Gm (at (vec 0))) (at (vec 0))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`u:real^2->bool`; `Gm:real^2->real^2`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h. (\x. frechet_derivative (Gp:real^2->real^2) (at x) h)
        continuous at (vec 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`u:real^2->bool`; `Gp:real^2->real^2`; `h:real^2`]
      SMOOTH_MAP_ON_FRECHET_DERIVATIVE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT;
             ASSUME `open(u:real^2->bool)`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Gp:real^2->real^2`;
                 `\x. frechet_derivative (Gp:real^2->real^2) (at x)`;
                 `u:real^2->bool`; `vec 0:real^2`]
    INVERSE_FUNCTION_THEOREM_C1_POINTWISE) THEN
  BETA_TAC THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (X_CHOOSE_THEN `v:real^2->bool`
   (X_CHOOSE_THEN `g:real^2->real^2`
   (X_CHOOSE_THEN `g':real^2->real^2->real^2` MP_TAC)))) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(Gm:real^2->real^2)(vec 0) = (Gp:real^2->real^2)(vec 0)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN USE_THEN "axis" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[VEC_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^2)((Gp:real^2->real^2)(vec 0)) = vec 0`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((g:real^2->real^2) has_derivative (g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)))
    (at (Gp(vec 0))) /\
    g'(Gp(vec 0)) o frechet_derivative Gp (at (vec 0)) = I`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `(Gp:real^2->real^2)(vec 0)` (ASSUME
     `!y:real^2. y IN v
          ==> ((g:real^2->real^2) has_derivative
               (g':real^2->real^2->real^2) y) (at y) /\
              frechet_derivative (Gp:real^2->real^2) (at (g y)) o g' y = I /\
              g' y o frechet_derivative Gp (at (g y)) = I`)) THEN
    REWRITE_TAC[ASSUME `(Gp:real^2->real^2)(vec 0) IN v`;
                ASSUME `(g:real^2->real^2)((Gp:real^2->real^2)(vec 0)) =
                        vec 0`] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((g:real^2->real^2) o (Gm:real^2->real^2)) has_derivative
     ((g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)) o frechet_derivative Gm (at (vec 0))))
    (at (vec 0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)) o
     frechet_derivative (Gm:real^2->real^2) (at (vec 0))) (basis 1) =
    basis 1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDT_AXIS_DERIVATIVE THEN
    EXISTS_TAC `(g:real^2->real^2) o (Gm:real^2->real^2)` THEN
    REWRITE_TAC[ETA_AX] THEN
    MP_TAC(SPEC `vec 0:real^2` (GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]
      (ASSUME `open(t:real^2->bool)`))) THEN
    REWRITE_TAC[ASSUME `vec 0:real^2 IN t`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s % basis 1:real^2 IN t` ASSUME_TAC THENL
     [MP_TAC(ASSUME `ball(vec 0:real^2,d) SUBSET t`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_BALL_0; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN
      ASM_REWRITE_TAC[REAL_MUL_RID];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(Gm:real^2->real^2)(s % basis 1) =
                  (Gp:real^2->real^2)(s % basis 1)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN USE_THEN "axis" MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [MP_TAC(ASSUME `t SUBSET (u:real^2->bool)`) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC(ASSUME `!x:real^2. x IN t
                           ==> (g:real^2->real^2)((Gp:real^2->real^2) x) = x`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linear((g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)):real^2->real^2) /\
    linear(frechet_derivative (Gp:real^2->real^2) (at (vec 0))) /\
    linear(frechet_derivative (Gm:real^2->real^2) (at (vec 0)))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_PDT_HAS_DERIVATIVE_IMP_LINEAR THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `det(matrix((g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)) o
               frechet_derivative (Gm:real^2->real^2) (at (vec 0)))) < &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`frechet_derivative (Gm:real^2->real^2) (at (vec 0))`;
                   `(g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)):real^2->real^2`]
      MATRIX_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DET_MUL] THEN MATCH_MP_TAC MOI_PDT_SIGN_LEMMA THEN
    EXISTS_TAC `det(matrix(frechet_derivative (Gp:real^2->real^2)
                                              (at (vec 0))))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM DET_MUL] THEN
    MP_TAC(ISPECL [`frechet_derivative (Gp:real^2->real^2) (at (vec 0))`;
                   `(g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)):real^2->real^2`]
      MATRIX_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[MATRIX_I; DET_I];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(((g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)) o
      frechet_derivative (Gm:real^2->real^2) (at (vec 0))) (basis 2))$2 < &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `(g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)) o
                  frechet_derivative (Gm:real^2->real^2) (at (vec 0))`
      MOI_PDT_DET2_FIX_BASIS1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^2->real^2) o (Gm:real^2->real^2))(vec 0) = vec 0`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[o_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(g:real^2->real^2) o (Gm:real^2->real^2)`;
                 `(g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)) o
                  frechet_derivative (Gm:real^2->real^2) (at (vec 0))`]
    MOI_PDT_NO_FOLD_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fold"))) THEN
  MP_TAC(SPEC `vec 0:real^2` (GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]
    (ASSUME `open(u:real^2->bool)`))) THEN
  REWRITE_TAC[ASSUME `vec 0:real^2 IN u`] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Gm:real^2->real^2`; `vec 0:real^2`; `v:real^2->bool`]
    MOI_PDT_CONTINUOUS_AT_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `frechet_derivative (Gm:real^2->real^2) (at (vec 0))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nv"))) THEN
  MP_TAC(ISPECL [`(g:real^2->real^2) o (Gm:real^2->real^2)`; `vec 0:real^2`;
                 `t:real^2->bool`] MOI_PDT_CONTINUOUS_AT_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
    REWRITE_TAC[differentiable] THEN
    EXISTS_TAC `(g':real^2->real^2->real^2)((Gp:real^2->real^2)(vec 0)) o
                frechet_derivative (Gm:real^2->real^2) (at (vec 0))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d4:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nt"))) THEN
  SUBGOAL_THEN `?s. &0 < s /\ s < d1 /\ s < d2 /\ s < d3 /\ s < d4`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (min d1 d2) (min d3 d4) / &2` THEN
    MAP_EVERY UNDISCH_TAC [`&0 < d1`; `&0 < d2`; `&0 < d3`; `&0 < d4`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(--(s % basis 2):real^2) = s` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN
    UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Gm:real^2->real^2)(--(s % basis 2)) IN v` ASSUME_TAC THENL
   [USE_THEN "nv" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_SUB_RZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^2)((Gm:real^2->real^2)(--(s % basis 2))) IN t`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `--(s % basis 2):real^2`
     (ASSUME `!y:real^2. norm(y - vec 0) < d4
                         ==> ((g:real^2->real^2) o (Gm:real^2->real^2)) y IN t`)) THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; o_THM; ASSUME `norm(--(s % basis 2):real^2) = s`;
                ASSUME `s < d4`];
    ALL_TAC] THEN
  EXISTS_TAC `--(s % basis 2):real^2` THEN
  EXISTS_TAC `(g:real^2->real^2)((Gm:real^2->real^2)(--(s % basis 2)))` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ASSUME `ball(vec 0:real^2,d2) SUBSET u`) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_BALL_0];
    MP_TAC(ASSUME `t SUBSET (u:real^2->bool)`) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[VECTOR_NEG_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    UNDISCH_TAC `&0 < s` THEN REAL_ARITH_TAC;
    MP_TAC(SPEC `s:real`
     (ASSUME `!s. &0 < s /\ s < d1
                  ==> &0 < (((g:real^2->real^2) o (Gm:real^2->real^2))
                            (--(s % basis 2)))$2`)) THEN
    REWRITE_TAC[o_THM; ASSUME `&0 < s`; ASSUME `s < d1`];
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ASSUME `!y:real^2. y IN v
                           ==> (Gp:real^2->real^2)((g:real^2->real^2) y) = y`) THEN
    ASM_REWRITE_TAC[]]);;

(* The leaf D4a, MOI_SMO_CREASE_ORIENT.                                     *)

let MOI_SMO_CREASE_ORIENT = prove
 (`MOI_SMO_CREASE_ORIENT_STATEMENT`,
  REWRITE_TAC[MOI_SMO_CREASE_ORIENT_STATEMENT; jacobian] THEN
  MAP_EVERY X_GEN_TAC [`G:real^2->real^2`; `Gp:real^2->real^2`;
                       `Gm:real^2->real^2`; `u:real^2->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`Gp:real^2->real^2`; `Gm:real^2->real^2`; `u:real^2->bool`]
    MOI_PDT_FOLD_POINT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
      MP_TAC(SPEC `x:real^2` (ASSUME
       `!x:real^2. x IN u /\ x$2 <= &0
                   ==> (G:real^2->real^2) x = (Gm:real^2->real^2) x`)) THEN
      MP_TAC(SPEC `x:real^2` (ASSUME
       `!x:real^2. x IN u /\ &0 <= x$2
                   ==> (G:real^2->real^2) x = (Gp:real^2->real^2) x`)) THEN
      REWRITE_TAC[ASSUME `(x:real^2) IN u`; ASSUME `(x:real^2)$2 = &0`;
                  REAL_LE_REFL] THEN
      MESON_TAC[];
      REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[REAL_ENTIRE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `y:real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `x:real^2 = y` MP_TAC THENL
   [MATCH_MP_TAC(ASSUME
     `!x y. x IN u /\ y IN u /\ (G:real^2->real^2) x = G y ==> x = y`) THEN
    REWRITE_TAC[ASSUME `(x:real^2) IN u`; ASSUME `(y:real^2) IN u`] THEN
    SUBGOAL_THEN `(x:real^2)$2 <= &0 /\ &0 <= (y:real^2)$2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `x:real^2` (ASSUME
     `!x:real^2. x IN u /\ x$2 <= &0
                 ==> (G:real^2->real^2) x = (Gm:real^2->real^2) x`)) THEN
    MP_TAC(SPEC `y:real^2` (ASSUME
     `!x:real^2. x IN u /\ &0 <= x$2
                 ==> (G:real^2->real^2) x = (Gp:real^2->real^2) x`)) THEN
    REWRITE_TAC[ASSUME `(x:real^2) IN u`; ASSUME `(y:real^2) IN u`;
                ASSUME `(x:real^2)$2 <= &0`; ASSUME `&0 <= (y:real^2)$2`] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN
    REWRITE_TAC[ASSUME `(Gm:real^2->real^2) x = (Gp:real^2->real^2) y`];
    DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY UNDISCH_TAC [`(y:real^2)$2 < &0`; `&0 < (y:real^2)$2`] THEN
    REAL_ARITH_TAC]);;

