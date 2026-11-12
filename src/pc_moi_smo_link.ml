(* ========================================================================= *)
(* pc_moi_smo_link (route M): the gnomonic projections of the star charts   *)
(* at a vertex v form a smooth atlas on the link of v (C6,                  *)
(* MOI_SMO_LINK_ATLAS_STATEMENT), given the edge charts (C4).  Route: a     *)
(* general projectivization lemma MOI_SLK_GNOM_ATLAS (homogeneous injective *)
(* 3D charts with smooth transitions give a smooth atlas of gnomonic charts *)
(* on a set L homeomorphic to S^2 that meets every ray from v at most       *)
(* once), then its instance for the star atlas (C3 from pc_moi_smo_base, C4 *)
(* as hypothesis).                                                          *)
(* The first part gives basic facts on the gnomonic projection, locality of *)
(* smoothness and invariance of domain on a 2-sphere.                       *)
(* ========================================================================= *)

needs "src/pc_moi_smo_cf.ml";;
needs "src/pc_moi_smo_base.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Locality of smoothness on open sets.  Copied (renamed) from              *)
(* SMOOTH_MAP_ON_LOCAL in pc_mfd_maps.ml, which is not in the load closure  *)
(* of this file.                                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_SLK_SMOOTH_LOCAL = prove
 (`!s (f:real^M->real^N).
        open s /\
        (!x. x IN s ==> ?t. open t /\ x IN t /\ smooth_map_on t f)
        ==> smooth_map_on s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_map_on] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`n:num`; `s:real^M->bool`; `f:real^M->real^N`]
    CONTINUOUSLY_DIFFERENTIABLE_LOCAL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s INTER t:real^M->bool` THEN
  ASM_SIMP_TAC[OPEN_INTER; IN_INTER; INTER_SUBSET] THEN
  MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
  EXISTS_TAC `t:real^M->bool` THEN REWRITE_TAC[INTER_SUBSET] THEN
  ASM_MESON_TAC[smooth_map_on]);;

(* ------------------------------------------------------------------------- *)
(* The gnomonic projection.                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_SLK_GNOM_COMPONENTS = prove
 (`!y:real^3. (moi_smo_gnom y)$1 = y$1 / y$3 /\ (moi_smo_gnom y)$2 = y$2 / y$3`,
  REWRITE_TAC[moi_smo_gnom; VECTOR_2]);;

let MOI_SLK_GNOM_CMUL = prove
 (`!t (y:real^3). &0 < t ==> moi_smo_gnom(t % y) = moi_smo_gnom y`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; MOI_SLK_GNOM_COMPONENTS;
              VECTOR_MUL_COMPONENT] THEN
  ASM_CASES_TAC `(y:real^3)$3 = &0` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_INV_0; REAL_MUL_RZERO] THEN
  UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `~((y:real^3)$3 = &0)` THEN
  CONV_TAC REAL_FIELD);;

let MOI_SLK_GNOM_LIFT = prove
 (`!y:real^3. &0 < y$3
        ==> y = y$3 % vector[(moi_smo_gnom y)$1; (moi_smo_gnom y)$2; &1]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_SLK_GNOM_COMPONENTS;
              VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  UNDISCH_TAC `&0 < (y:real^3)$3` THEN CONV_TAC REAL_FIELD);;

let MOI_SLK_GNOM_EQ = prove
 (`!y z:real^3. &0 < y$3 /\ &0 < z$3 /\ moi_smo_gnom y = moi_smo_gnom z
        ==> y = (y$3 / z$3) % z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3;
              MOI_SLK_GNOM_COMPONENTS; VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_FIELD);;

let MOI_SLK_GNOM_SMOOTH = prove
 (`!s. open s /\ (!y:real^3. y IN s ==> ~(y$3 = &0))
       ==> smooth_map_on s moi_smo_gnom`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `moi_smo_gnom`]
    SMOOTH_MAP_ON_COMPONENTWISE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= k /\ k <= 2 <=> k = 1 \/ k = 2`] THEN
  SUBGOAL_THEN
   `!i. smooth_map_on s (\y:real^3. lift(y$i))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^3->bool`; `\y:real^3. y`; `i:num`]
      SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[MOI_SLK_GNOM_COMPONENTS] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `\y:real^3. lift(y$k)`; `\y:real^3. lift(y$3)`]
    SMOOTH_MAP_ON_LIFT_DIV) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ASM_MESON_TAC[]);;

let MOI_SLK_GNOM_CONTINUOUS = prove
 (`!s. (!y:real^3. y IN s ==> &0 < y$3) ==> moi_smo_gnom continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `{y:real^3 | y$3 > &0}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    MATCH_MP_TAC MOI_SLK_GNOM_SMOOTH THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Invariance of domain for maps from an open subset of a space             *)
(* homeomorphic to the 2-sphere into the plane.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_SLK_IOD = prove
 (`!X:real^N->bool W (f:real^N->real^2).
        X homeomorphic sphere(vec 0:real^3,&1) /\
        open_in (subtopology euclidean X) W /\
        f continuous_on W /\
        (!x y. x IN W /\ y IN W /\ f x = f y ==> x = y)
        ==> open (IMAGE f W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_TAC `k:real^3->real^N`)) THEN
  SUBGOAL_THEN `(W:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (sphere(vec 0:real^3,&1)))
            (IMAGE (h:real^N->real^3) W)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->real^N`; `X:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!x:real^N. x IN W ==> (k:real^3->real^N)(h x) = x`
  ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (k:real^3->real^N) (IMAGE (h:real^N->real^3) W) = W`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x:real^N. x IN W ==> (k:real^3->real^N)((h:real^N->real^3) x) = x)
      ==> IMAGE k (IMAGE h W) = W`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((f:real^N->real^2) o (k:real^3->real^N)) (IMAGE h W) = IMAGE f W`
  (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^3) W SUBSET sphere(vec 0,&1)`
  ASSUME_TAC THENL [ASM_MESON_TAC[IMAGE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:real^N->real^2) o (k:real^3->real^N)`;
                 `cball(vec 0:real^3,&1)`; `IMAGE (h:real^N->real^3) W`;
                 `(:real^2)`] INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET_GEN) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; SUBSET_UNIV] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[BOUNDED_CBALL; CONVEX_CBALL; AFFINE_UNIV; AFF_DIM_UNIV;
              AFF_DIM_CBALL; RELATIVE_FRONTIER_CBALL; DIMINDEX_2; DIMINDEX_3] THEN
  REWRITE_TAC[REAL_LT_01; REAL_OF_NUM_EQ; ARITH_EQ; INT_ARITH `&2:int < &3`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `sphere(vec 0:real^3,&1)` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(k:real^3->real^N)(h(x:real^N)) = x /\ k(h(y:real^N)) = y`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[];
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_SLK_IOD_HOMEO = prove
 (`!X:real^N->bool W (f:real^N->real^2).
        X homeomorphic sphere(vec 0:real^3,&1) /\
        open_in (subtopology euclidean X) W /\
        f continuous_on W /\
        (!x y. x IN W /\ y IN W /\ f x = f y ==> x = y)
        ==> open (IMAGE f W) /\ ?g. homeomorphism (W,IMAGE f W) (f,g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLK_IOD THEN EXISTS_TAC `X:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_OPEN_MAP THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC OPEN_SUBSET THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SLK_IOD THEN EXISTS_TAC `X:real^N->bool` THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET W` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[OPEN_IN_TRANS];
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Charts given as homeomorphic maps between Euclidean subspaces.           *)
(* ------------------------------------------------------------------------- *)

let MOI_SLK_HMAP = prove
 (`!U (kappa:real^N->real^M).
        homeomorphic_map (subtopology euclidean U,
                          subtopology euclidean (IMAGE kappa U)) kappa
        ==> (?g. homeomorphism (U,IMAGE kappa U) (kappa,g)) /\
            kappa continuous_on U /\
            (!x y. x IN U /\ y IN U /\ kappa x = kappa y ==> x = y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^M->real^N`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_SLK_HMAP_OF_HOMEO = prove
 (`!U (kappa:real^N->real^M) g.
        homeomorphism (U,IMAGE kappa U) (kappa,g)
        ==> homeomorphic_map (subtopology euclidean U,
                              subtopology euclidean (IMAGE kappa U)) kappa`,
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY] THEN
  MESON_TAC[]);;

(* The image of an open part of a chart domain is open.                      *)

let MOI_SLK_OPEN_IMAGE_SUB = prove
 (`!Y U V (kappa:real^N->real^3).
        open_in (subtopology euclidean Y) U /\
        open_in (subtopology euclidean Y) V /\ V SUBSET U /\
        open (IMAGE kappa U) /\
        homeomorphic_map (subtopology euclidean U,
                          subtopology euclidean (IMAGE kappa U)) kappa
        ==> open (IMAGE kappa V)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SLK_HMAP) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `g:real^3->real^N`) STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
  EXISTS_TAC `IMAGE (kappa:real^N->real^3) U` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
  MAP_EVERY EXISTS_TAC [`g:real^3->real^N`; `U:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `Y:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* One gnomonic chart.  K is a 3D chart on U (open in Y), continuous,       *)
(* injective and homogeneous of degree 1 about v; the link chart is l |->   *)
(* gnom(K(v + (l - v) / 2)) on the points l of L whose midpoint with v lies *)
(* in U and whose image has positive third coordinate.                      *)
(* ------------------------------------------------------------------------- *)

let MOI_SLK_RATIO = prove
 (`!a b. &0 < a /\ &0 < b /\ a <= b ==> &0 < a / b /\ a / b <= &1`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID]);;

let MOI_SLK_MID_CONTINUOUS = prove
 (`!(v:real^N) s. (\l. v + inv(&2) % (l - v)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB;
           CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST]);;

let MOI_SLK_W_OPEN = prove
 (`!(L:real^N->bool) Y v U (K:real^N->real^3).
     (!l. l IN L ==> v + inv(&2) % (l - v) IN Y) /\
     open_in (subtopology euclidean Y) U /\ K continuous_on U
     ==> open_in (subtopology euclidean L)
           {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                &0 < (K(v + inv(&2) % (l - v)))$3}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean L)
      {l:real^N | l IN L /\ v + inv(&2) % (l - v) IN U}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\l:real^N. v + inv(&2) % (l - v)`; `L:real^N->bool`;
                   `Y:real^N->bool`; `U:real^N->bool`]
      CONTINUOUS_OPEN_IN_PREIMAGE_GEN) THEN
    ASM_REWRITE_TAC[MOI_SLK_MID_CONTINUOUS; SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN
  EXISTS_TAC `{l:real^N | l IN L /\ v + inv(&2) % (l - v) IN U}` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(K:real^N->real^3) o (\l:real^N. v + inv(&2) % (l - v))`;
                 `{l:real^N | l IN L /\ v + inv(&2) % (l - v) IN U}`;
                 `{y:real^3 | y$3 > &0}`] CONTINUOUS_OPEN_IN_PREIMAGE) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[MOI_SLK_MID_CONTINUOUS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `(s:real^N->bool) = t ==> open_in top s ==> open_in top t`) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM; real_gt] THEN MESON_TAC[]);;

let MOI_SLK_PHI_CONT = prove
 (`!(L:real^N->bool) v U (K:real^N->real^3).
     K continuous_on U
     ==> (\l. moi_smo_gnom(K(v + inv(&2) % (l - v)))) continuous_on
         {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
              &0 < (K(v + inv(&2) % (l - v)))$3}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\l:real^N. moi_smo_gnom((K:real^N->real^3)(v + inv(&2) % (l - v)))) =
    moi_smo_gnom o (K o (\l. v + inv(&2) % (l - v)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[MOI_SLK_MID_CONTINUOUS] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC MOI_SLK_GNOM_CONTINUOUS THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN MESON_TAC[]]);;

(* Two points of U with the same gnomonic image lie on one ray from v.       *)

let MOI_SLK_HOMOG_RAY = prove
 (`!U (K:real^N->real^3) v x1 x2.
     (!x y. x IN U /\ y IN U /\ K x = K y ==> x = y) /\
     (!x t. x IN U /\ &0 < t /\ t <= &1
            ==> v + t % (x - v) IN U /\ K(v + t % (x - v)) = t % K x) /\
     x1 IN U /\ x2 IN U /\ &0 < (K x1)$3 /\ &0 < (K x2)$3 /\
     moi_smo_gnom(K x1) = moi_smo_gnom(K x2)
     ==> ?r. &0 < r /\ x1 - v = r % (x2 - v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 (LABEL_TAC "hom") STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!z1 z2:real^N.
       z1 IN U /\ z2 IN U /\ &0 < ((K:real^N->real^3) z1)$3 /\ &0 < (K z2)$3 /\
       moi_smo_gnom(K z1) = moi_smo_gnom(K z2) /\ (K z1)$3 <= (K z2)$3
       ==> z1 = v + ((K z1)$3 / (K z2)$3) % (z2 - v)`
  (LABEL_TAC "wlog") THENL
   [MAP_EVERY X_GEN_TAC [`z1:real^N`; `z2:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`((K:real^N->real^3) z1)$3`; `((K:real^N->real^3) z2)$3`]
      MOI_SLK_RATIO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "hom" (MP_TAC o SPECL
     [`z2:real^N`; `((K:real^N->real^3) z1)$3 / (K z2)$3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SLK_GNOM_EQ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH
   `((K:real^N->real^3) x1)$3 <= (K x2)$3 \/ (K x2)$3 <= (K x1)$3`) THENL
   [EXISTS_TAC `((K:real^N->real^3) x1)$3 / (K x2)$3` THEN
    USE_THEN "wlog" (MP_TAC o SPECL [`x1:real^N`; `x2:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th] THEN VECTOR_ARITH_TAC]);
    SUBGOAL_THEN `&0 < ((K:real^N->real^3) x2)$3 / (K x1)$3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `inv(((K:real^N->real^3) x2)$3 / (K x1)$3)` THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    USE_THEN "wlog" (MP_TAC o SPECL [`x2:real^N`; `x1:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&0 < ((K:real^N->real^3) x2)$3 / (K x1)$3` THEN
    SPEC_TAC(`((K:real^N->real^3) x2)$3 / (K x1)$3`,`t:real`) THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(v + t % (x1 - v)) - v:real^N = t % (x1 - v)`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `inv t * t = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LID]]);;

(* Injectivity of a gnomonic chart.                                          *)

let MOI_SLK_PHI_INJ = prove
 (`!(L:real^N->bool) v U (K:real^N->real^3).
     (!l1 l2 r1 r2. l1 IN L /\ l2 IN L /\ &0 < r1 /\ &0 < r2 /\
                    v + r1 % (l1 - v) = v + r2 % (l2 - v) ==> l1 = l2) /\
     (!x y. x IN U /\ y IN U /\ K x = K y ==> x = y) /\
     (!x t. x IN U /\ &0 < t /\ t <= &1
            ==> v + t % (x - v) IN U /\ K(v + t % (x - v)) = t % K x)
     ==> !l1 l2. l1 IN {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                            &0 < (K(v + inv(&2) % (l - v)))$3} /\
                 l2 IN {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                            &0 < (K(v + inv(&2) % (l - v)))$3} /\
                 moi_smo_gnom(K(v + inv(&2) % (l1 - v))) =
                 moi_smo_gnom(K(v + inv(&2) % (l2 - v)))
                 ==> l1 = l2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ray")
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "hom"))) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `K:real^N->real^3`; `v:real^N`;
                 `v + inv(&2) % (l1 - v):real^N`; `v + inv(&2) % (l2 - v):real^N`]
    MOI_SLK_HOMOG_RAY) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "ray" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`&1`; `r:real`] THEN
  ASM_REWRITE_TAC[REAL_LT_01] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[VECTOR_ARITH `(v + inv(&2) % (l - v)) - v:real^N = inv(&2) % (l - v)`] THEN
  REWRITE_TAC[VECTOR_ARITH
   `inv(&2) % (l1 - v) = r % inv(&2) % (l2 - v) <=>
    v + &1 % (l1 - v):real^N = v + r % (l2 - v)`]);;

(* A homogeneous injective chart does not vanish off v.                      *)

let MOI_SLK_NONZERO = prove
 (`!U (K:real^N->real^3) v x.
     (!x y. x IN U /\ y IN U /\ K x = K y ==> x = y) /\
     (!x t. x IN U /\ &0 < t /\ t <= &1
            ==> v + t % (x - v) IN U /\ K(v + t % (x - v)) = t % K x) /\
     x IN U /\ ~(x = v)
     ==> ~(K x = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 (LABEL_TAC "hom") STRIP_ASSUME_TAC)) THEN
  DISCH_TAC THEN
  USE_THEN "hom" (MP_TAC o SPECL [`x:real^N`; `inv(&2)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN STRIP_TAC THEN
  SUBGOAL_THEN `v + inv(&2) % (x - v):real^N = x` MP_TAC THENL
   [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[VECTOR_ARITH
     `v + inv(&2) % (x - v):real^N = x <=> x = v`] THEN
    ASM_REWRITE_TAC[]]);;

(* The chart conditions for one gnomonic chart.                               *)

let MOI_SLK_CHART = prove
 (`!(L:real^N->bool) Y v U (K:real^N->real^3).
     L homeomorphic sphere(vec 0:real^3,&1) /\
     (!l. l IN L ==> v + inv(&2) % (l - v) IN Y) /\
     (!l1 l2 r1 r2. l1 IN L /\ l2 IN L /\ &0 < r1 /\ &0 < r2 /\
                    v + r1 % (l1 - v) = v + r2 % (l2 - v) ==> l1 = l2) /\
     open_in (subtopology euclidean Y) U /\ K continuous_on U /\
     (!x y. x IN U /\ y IN U /\ K x = K y ==> x = y) /\
     (!x t. x IN U /\ &0 < t /\ t <= &1
            ==> v + t % (x - v) IN U /\ K(v + t % (x - v)) = t % K x)
     ==> open_in (subtopology euclidean L)
           {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                &0 < (K(v + inv(&2) % (l - v)))$3} /\
         (\l. moi_smo_gnom(K(v + inv(&2) % (l - v)))) continuous_on
           {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                &0 < (K(v + inv(&2) % (l - v)))$3} /\
         open (IMAGE (\l. moi_smo_gnom(K(v + inv(&2) % (l - v))))
                     {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                          &0 < (K(v + inv(&2) % (l - v)))$3}) /\
         ?g. homeomorphism
               ({l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                     &0 < (K(v + inv(&2) % (l - v)))$3},
                IMAGE (\l. moi_smo_gnom(K(v + inv(&2) % (l - v))))
                      {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                           &0 < (K(v + inv(&2) % (l - v)))$3})
               ((\l. moi_smo_gnom(K(v + inv(&2) % (l - v)))),g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean L)
      {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
           &0 < ((K:real^N->real^3)(v + inv(&2) % (l - v)))$3}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLK_W_OPEN THEN EXISTS_TAC `Y:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\l. moi_smo_gnom((K:real^N->real^3)(v + inv(&2) % (l - v)))) continuous_on
    {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
         &0 < (K(v + inv(&2) % (l - v)))$3}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLK_PHI_CONT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SLK_IOD_HOMEO THEN EXISTS_TAC `L:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SLK_PHI_INJ THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transition maps between two gnomonic charts.  The 3D transition G of two *)
(* homogeneous charts is homogeneous on the image, so near a point p0 the   *)
(* link transition is the smooth map p |-> gnom(G(mu % (p,1))) for a fixed  *)
(* mu below the height of p0.                                               *)
(* ------------------------------------------------------------------------- *)

(* The pointwise identity behind the local formula.                          *)

let MOI_SLK_TRANS_POINT = prove
 (`!(v:real^N) U1 U2 (K1:real^N->real^3) (K2:real^N->real^3) G x mu.
     (!x t. x IN U1 /\ &0 < t /\ t <= &1
            ==> v + t % (x - v) IN U1 /\ K1(v + t % (x - v)) = t % K1 x) /\
     (!x t. x IN U2 /\ &0 < t /\ t <= &1
            ==> v + t % (x - v) IN U2 /\ K2(v + t % (x - v)) = t % K2 x) /\
     (!x. x IN U1 INTER U2 ==> G(K1 x) = K2 x) /\
     x IN U1 /\ x IN U2 /\ &0 < mu /\ mu < (K1 x)$3 /\ &0 < (K2 x)$3
     ==> mu % vector[(moi_smo_gnom(K1 x))$1; (moi_smo_gnom(K1 x))$2; &1]
           IN IMAGE K1 (U1 INTER U2) /\
         &0 < (G(mu % vector[(moi_smo_gnom(K1 x))$1;
                             (moi_smo_gnom(K1 x))$2; &1]))$3 /\
         moi_smo_gnom(G(mu % vector[(moi_smo_gnom(K1 x))$1;
                                    (moi_smo_gnom(K1 x))$2; &1])) =
         moi_smo_gnom(K2 x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h1")
    (CONJUNCTS_THEN2 (LABEL_TAC "h2")
    (CONJUNCTS_THEN2 (LABEL_TAC "g") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `&0 < ((K1:real^N->real^3) x)$3` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`mu:real`; `((K1:real^N->real^3) x)$3`] MOI_SLK_RATIO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
  USE_THEN "h1" (MP_TAC o SPECL [`x:real^N`; `mu / ((K1:real^N->real^3) x)$3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "h2" (MP_TAC o SPECL [`x:real^N`; `mu / ((K1:real^N->real^3) x)$3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `mu % vector[(moi_smo_gnom((K1:real^N->real^3) x))$1;
                (moi_smo_gnom(K1 x))$2; &1] =
    K1(v + (mu / (K1 x)$3) % (x - v))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `(K1:real^N->real^3) x` MOI_SLK_GNOM_LIFT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
    ASM_MESON_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(G:real^3->real^3)((K1:real^N->real^3)(v + (mu / (K1 x)$3) % (x - v))) =
    (mu / (K1 x)$3) % (K2:real^N->real^3) x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(K2:real^N->real^3)(v + (mu / ((K1:real^N->real^3) x)$3) % (x - v))` THEN
    CONJ_TAC THENL
     [USE_THEN "g" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `v + (mu / ((K1:real^N->real^3) x)$3) % (x - v)` THEN
    ASM_REWRITE_TAC[IN_INTER];
    REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SLK_GNOM_CMUL THEN ASM_REWRITE_TAC[]]);;

(* The affine map p |-> mu % (p,1) is smooth.                                 *)

let MOI_SLK_LIFT_SMOOTH = prove
 (`!mu s. smooth_map_on s (\p:real^2. mu % vector[p$1; p$2; &1]:real^3)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MOI_SBA_AFFINE_SMOOTH THEN
  EXISTS_TAC `\p:real^2. mu % vector[p$1; p$2; &0]:real^3` THEN
  EXISTS_TAC `mu % vector[&0; &0; &1]:real^3` THEN
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

(* Abstract transition lemma: chart 1 is a homeomorphism with inverse g1,  *)
(* the two link charts are gnomonic projections of K1, K2 on W1, W2, and    *)
(* G is a smooth 3D transition on the open set K1(U1 INTER U2).              *)

let MOI_SLK_TRANS_ABS = prove
 (`!(W1:real^N->bool) W2 (phi1:real^N->real^2) phi2 g1 v U1 U2
    (K1:real^N->real^3) (K2:real^N->real^3) G.
     homeomorphism (W1,IMAGE phi1 W1) (phi1,g1) /\
     open (IMAGE phi1 (W1 INTER W2)) /\
     (!l. l IN W1
          ==> v + inv(&2) % (l - v) IN U1 /\
              &0 < (K1(v + inv(&2) % (l - v)))$3 /\
              phi1 l = moi_smo_gnom(K1(v + inv(&2) % (l - v)))) /\
     (!l. l IN W2
          ==> v + inv(&2) % (l - v) IN U2 /\
              &0 < (K2(v + inv(&2) % (l - v)))$3 /\
              phi2 l = moi_smo_gnom(K2(v + inv(&2) % (l - v)))) /\
     K1 continuous_on U1 /\
     (!x t. x IN U1 /\ &0 < t /\ t <= &1
            ==> v + t % (x - v) IN U1 /\ K1(v + t % (x - v)) = t % K1 x) /\
     (!x t. x IN U2 /\ &0 < t /\ t <= &1
            ==> v + t % (x - v) IN U2 /\ K2(v + t % (x - v)) = t % K2 x) /\
     open (IMAGE K1 (U1 INTER U2)) /\
     smooth_map_on (IMAGE K1 (U1 INTER U2)) G /\
     (!x. x IN U1 INTER U2 ==> G(K1 x) = K2 x)
     ==> ?g. smooth_map_on (IMAGE phi1 (W1 INTER W2)) g /\
             !l. l IN W1 INTER W2 ==> g(phi1 l) = phi2 l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hm")
    (CONJUNCTS_THEN2 (LABEL_TAC "op")
    (CONJUNCTS_THEN2 (LABEL_TAC "w1")
    (CONJUNCTS_THEN2 (LABEL_TAC "w2")
    (CONJUNCTS_THEN2 (LABEL_TAC "k1c")
    (CONJUNCTS_THEN2 (LABEL_TAC "h1")
    (CONJUNCTS_THEN2 (LABEL_TAC "h2")
    (CONJUNCTS_THEN2 (LABEL_TAC "gop")
    (CONJUNCTS_THEN2 (LABEL_TAC "gsm") (LABEL_TAC "g")))))))))) THEN
  USE_THEN "hm" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  EXISTS_TAC `\p:real^2. (phi2:real^N->real^2)((g1:real^2->real^N) p)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC MOI_SLK_SMOOTH_LOCAL THEN
  CONJ_TAC THENL [USE_THEN "op" ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
  X_GEN_TAC `l0:real^N` THEN STRIP_TAC THEN
  USE_THEN "w1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(l0:real^N) IN W1`))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `?mu. &0 < mu /\ mu < ((K1:real^N->real^3)(v + inv(&2) % (l0 - v)))$3`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `((K1:real^N->real^3)(v + inv(&2) % (l0 - v)))$3 / &2` THEN
    UNDISCH_TAC `&0 < ((K1:real^N->real^3)(v + inv(&2) % (l0 - v)))$3` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the continuous height function on the image of the overlap *)
  SUBGOAL_THEN
   `(\p:real^2. (K1:real^N->real^3)(v + inv(&2) % ((g1:real^2->real^N) p - v)))
    continuous_on IMAGE (phi1:real^N->real^2) (W1 INTER W2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\p:real^2. (K1:real^N->real^3)(v + inv(&2) % ((g1:real^2->real^N) p - v))) =
      K1 o ((\l. v + inv(&2) % (l - v)) o g1)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[MOI_SLK_MID_CONTINUOUS] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (phi1:real^N->real^2) W1` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U1:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; o_THM] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* the neighbourhood t of phi1 l0 *)
  SUBGOAL_THEN
   `?t. open t /\ (phi1:real^N->real^2) l0 IN t /\
        !p. p IN t
            ==> p IN IMAGE phi1 (W1 INTER W2) /\
                mu < ((K1:real^N->real^3)
                        (v + inv(&2) % ((g1:real^2->real^N) p - v)))$3`
  MP_TAC THENL
   [EXISTS_TAC
     `{p:real^2 | p IN IMAGE (phi1:real^N->real^2) (W1 INTER W2) /\
                  (\p. (K1:real^N->real^3)(v + inv(&2) % ((g1:real^2->real^N) p - v)))
                  p IN {y:real^3 | y$3 > mu}}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT];
      REWRITE_TAC[IN_ELIM_THM; real_gt] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `l0:real^N` THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(g1:real^2->real^N)((phi1:real^N->real^2) l0) = l0`
        SUBST1_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]];
      REWRITE_TAC[IN_ELIM_THM; real_gt] THEN MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tprop"))))] THEN
  EXISTS_TAC `t:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  (* the local formula *)
  SUBGOAL_THEN
   `!p. p IN t
        ==> mu % vector[(p:real^2)$1; p$2; &1] IN
              IMAGE (K1:real^N->real^3) (U1 INTER U2) /\
            &0 < ((G:real^3->real^3)(mu % vector[p$1; p$2; &1]))$3 /\
            moi_smo_gnom(G(mu % vector[p$1; p$2; &1])) =
            (phi2:real^N->real^2)((g1:real^2->real^N) p)`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN
    USE_THEN "tprop" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(p:real^2) IN t`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(g1:real^2->real^N) p IN W1 /\ g1 p IN W2 /\
      (phi1:real^N->real^2)(g1 p) = p`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `p IN IMAGE (phi1:real^N->real^2) (W1 INTER W2)` THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `l:real^N` STRIP_ASSUME_TAC) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "w1" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(g1:real^2->real^N) p IN W1`))) THEN
    USE_THEN "w2" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(g1:real^2->real^N) p IN W2`))) THEN
    REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`v:real^N`; `U1:real^N->bool`; `U2:real^N->bool`;
                   `K1:real^N->real^3`; `K2:real^N->real^3`; `G:real^3->real^3`;
                   `v + inv(&2) % ((g1:real^2->real^N) p - v)`; `mu:real`]
      MOI_SLK_TRANS_POINT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `moi_smo_gnom((K1:real^N->real^3)
         (v + inv(&2) % ((g1:real^2->real^N) p - v))) = p`
    SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `moi_smo_gnom((K2:real^N->real^3)
         (v + inv(&2) % ((g1:real^2->real^N) p - v))) =
      (phi2:real^N->real^2)(g1 p)`
    SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `moi_smo_gnom o ((G:real^3->real^3) o
              (\p:real^2. mu % vector[p$1; p$2; &1]:real^3))` THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{y:real^3 | y$3 > &0}` THEN
  ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM; real_gt] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (K1:real^N->real^3) (U1 INTER U2)` THEN
    ASM_REWRITE_TAC[MOI_SLK_LIFT_SMOOTH] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_SLK_GNOM_SMOOTH THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; IN_ELIM_THM; real_gt] THEN
    REAL_ARITH_TAC]);;

(* Orthogonal transformations are open maps.                                *)

let MOI_SLK_OPEN_ORTH = prove
 (`!(R:real^N->real^N) s. orthogonal_transformation R /\ open s
                          ==> open (IMAGE R s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:real^N->real^N`; `s:real^N->bool`]
    OPEN_BIJECTIVE_LINEAR_IMAGE_EQ) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR;
                  ORTHOGONAL_TRANSFORMATION_INJECTIVE;
                  ORTHOGONAL_TRANSFORMATION_SURJECTIVE];
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* The 3D transition between rotated charts.                                 *)

let MOI_SLK_ROT_TRANS = prove
 (`!Y U1 U2 (kappa1:real^N->real^3) (kappa2:real^N->real^3) G0
    (R1:real^3->real^3) (R2:real^3->real^3).
     open_in (subtopology euclidean Y) U1 /\
     open_in (subtopology euclidean Y) U2 /\
     open (IMAGE kappa1 U1) /\
     homeomorphic_map (subtopology euclidean U1,
                       subtopology euclidean (IMAGE kappa1 U1)) kappa1 /\
     smooth_map_on (IMAGE kappa1 (U1 INTER U2)) G0 /\
     (!x. x IN U1 INTER U2 ==> G0(kappa1 x) = kappa2 x) /\
     orthogonal_transformation R1 /\ orthogonal_transformation R2
     ==> ?G. open (IMAGE (\x. R1(kappa1 x)) (U1 INTER U2)) /\
             smooth_map_on (IMAGE (\x. R1(kappa1 x)) (U1 INTER U2)) G /\
             (!x. x IN U1 INTER U2 ==> G(R1(kappa1 x)) = R2(kappa2 x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `R1:real^3->real^3` ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1':real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open (IMAGE (kappa1:real^N->real^3) (U1 INTER U2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLK_OPEN_IMAGE_SUB THEN
    MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `U1:real^N->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x. (R1:real^3->real^3)((kappa1:real^N->real^3) x)) (U1 INTER U2) =
    IMAGE R1 (IMAGE kappa1 (U1 INTER U2))`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  EXISTS_TAC `\y:real^3. (R2:real^3->real^3)((G0:real^3->real^3)((R1':real^3->real^3) y))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLK_OPEN_ORTH THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `(\y:real^3. (R2:real^3->real^3)((G0:real^3->real^3)((R1':real^3->real^3) y))) =
      R2 o (G0 o R1')`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN
     `open (IMAGE (R1:real^3->real^3) (IMAGE (kappa1:real^N->real^3) (U1 INTER U2)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SLK_OPEN_ORTH THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `IMAGE (kappa1:real^N->real^3) (U1 INTER U2)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[IN_IMAGE];
      MATCH_MP_TAC MOI_SBA_AFFINE_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`R1':real^3->real^3`; `vec 0:real^3`] THEN
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; VECTOR_ADD_RID]];
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The general projectivization lemma.  A family S of 3D charts, open in Y, *)
(* homogeneous of degree 1 about v, with smooth transitions, whose domains  *)
(* contain the midpoints of v with the points of L, gives a smooth atlas on *)
(* L (homeomorphic to S^2, meeting each ray from v at most once) formed by  *)
(* the gnomonic projections of the rotated charts R o kappa.                *)
(* ------------------------------------------------------------------------- *)

let MOI_SLK_INTER_RESTRICT = prove
 (`!(L:real^N->bool) P. L INTER {l | l IN L /\ P l} = {l | l IN L /\ P l}`,
  SET_TAC[]);;

let MOI_SLK_IMAGE_INTER_OPEN = prove
 (`!(L:real^N->bool) W1 W2 (phi1:real^N->real^2) g1.
     L homeomorphic sphere(vec 0:real^3,&1) /\
     open_in (subtopology euclidean L) W1 /\
     open_in (subtopology euclidean L) W2 /\
     homeomorphism (W1,IMAGE phi1 W1) (phi1,g1)
     ==> open (IMAGE phi1 (W1 INTER W2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLK_IOD THEN
  EXISTS_TAC `L:real^N->bool` THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `W1:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]]);;

(* A rotated homogeneous chart is again a continuous injective homogeneous *)
(* chart.                                                                    *)

let MOI_SLK_ROT_CHART = prove
 (`!Y U (kappa:real^N->real^3) (R:real^3->real^3) v.
     open_in (subtopology euclidean Y) U /\ open (IMAGE kappa U) /\
     homeomorphic_map (subtopology euclidean U,
                       subtopology euclidean (IMAGE kappa U)) kappa /\
     (!x t. x IN U /\ &0 < t /\ t <= &1
            ==> v + t % (x - v) IN U /\ kappa(v + t % (x - v)) = t % kappa x) /\
     orthogonal_transformation R
     ==> (\x. R(kappa x)) continuous_on U /\
         (!x y. x IN U /\ y IN U /\ R(kappa x) = R(kappa y) ==> x = y) /\
         (!x t. x IN U /\ &0 < t /\ t <= &1
                ==> v + t % (x - v) IN U /\
                    R(kappa(v + t % (x - v))) = t % R(kappa x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MOI_SLK_HMAP)
    (CONJUNCTS_THEN2 (LABEL_TAC "hom") ASSUME_TAC)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj"))) THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\x. (R:real^3->real^3)((kappa:real^N->real^3) x)) = R o kappa`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_INJECTIVE];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "hom" (MP_TAC o SPECL [`x:real^N`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR; LINEAR_CMUL]]);;

(* The general lemma.                                                        *)

let MOI_SLK_GNOM_ATLAS = prove
 (`!(S:((real^N->bool)#(real^N->real^3))->bool) Y L (v:real^N).
     L homeomorphic sphere(vec 0:real^3,&1) /\
     ~(v IN L) /\
     (!l. l IN L ==> v + inv(&2) % (l - v) IN Y) /\
     (!l1 l2 r1 r2. l1 IN L /\ l2 IN L /\ &0 < r1 /\ &0 < r2 /\
                    v + r1 % (l1 - v) = v + r2 % (l2 - v) ==> l1 = l2) /\
     (!U kappa. (U,kappa) IN S
                ==> open_in (subtopology euclidean Y) U /\ open (IMAGE kappa U) /\
                    homeomorphic_map (subtopology euclidean U,
                                      subtopology euclidean (IMAGE kappa U))
                                     kappa) /\
     (!U kappa x t. (U,kappa) IN S /\ x IN U /\ &0 < t /\ t <= &1
                    ==> v + t % (x - v) IN U /\
                        kappa(v + t % (x - v)) = t % kappa x) /\
     (!U kappa V psi. (U,kappa) IN S /\ (V,psi) IN S
                      ==> ?g. smooth_map_on (IMAGE kappa (U INTER V)) g /\
                              !x. x IN U INTER V ==> g(kappa x) = psi x) /\
     (!l. l IN L ==> ?U kappa. (U,kappa) IN S /\ v + inv(&2) % (l - v) IN U)
     ==> smooth_manifold_atlas (subtopology euclidean L)
           {({l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                  &0 < ((R:real^3->real^3)(kappa(v + inv(&2) % (l - v))))$3},
             (\l. moi_smo_gnom(R(kappa(v + inv(&2) % (l - v)))))) |
            U,kappa,R | (U,kappa) IN S /\ orthogonal_transformation R}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sph")
    (CONJUNCTS_THEN2 (LABEL_TAC "vnot")
    (CONJUNCTS_THEN2 (LABEL_TAC "midY")
    (CONJUNCTS_THEN2 (LABEL_TAC "ray")
    (CONJUNCTS_THEN2 (LABEL_TAC "chart")
    (CONJUNCTS_THEN2 (LABEL_TAC "hom")
    (CONJUNCTS_THEN2 (LABEL_TAC "trans") (LABEL_TAC "cover")))))))) THEN
  (* the 3D facts of a rotated chart *)
  SUBGOAL_THEN
   `!U (kappa:real^N->real^3) (R:real^3->real^3).
       (U,kappa) IN S /\ orthogonal_transformation R
       ==> open_in (subtopology euclidean Y) U /\ open (IMAGE kappa U) /\
           homeomorphic_map (subtopology euclidean U,
                             subtopology euclidean (IMAGE kappa U)) kappa /\
           (\x. R(kappa x)) continuous_on U /\
           (!x y. x IN U /\ y IN U /\ R(kappa x) = R(kappa y) ==> x = y) /\
           (!x t. x IN U /\ &0 < t /\ t <= &1
                  ==> v + t % (x - v) IN U /\
                      R(kappa(v + t % (x - v))) = t % R(kappa x))`
  (LABEL_TAC "rot") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "chart" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `((U:real^N->bool),(kappa:real^N->real^3)) IN S`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SLK_ROT_CHART THEN EXISTS_TAC `Y:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "hom" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the link chart facts of a rotated chart *)
  SUBGOAL_THEN
   `!U (kappa:real^N->real^3) (R:real^3->real^3).
       (U,kappa) IN S /\ orthogonal_transformation R
       ==> open_in (subtopology euclidean L)
             {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                  &0 < (R(kappa(v + inv(&2) % (l - v))))$3} /\
           (\l. moi_smo_gnom(R(kappa(v + inv(&2) % (l - v))))) continuous_on
             {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                  &0 < (R(kappa(v + inv(&2) % (l - v))))$3} /\
           open (IMAGE (\l. moi_smo_gnom(R(kappa(v + inv(&2) % (l - v)))))
                       {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                            &0 < (R(kappa(v + inv(&2) % (l - v))))$3}) /\
           ?g. homeomorphism
                 ({l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                       &0 < (R(kappa(v + inv(&2) % (l - v))))$3},
                  IMAGE (\l. moi_smo_gnom(R(kappa(v + inv(&2) % (l - v)))))
                        {l | l IN L /\ v + inv(&2) % (l - v) IN U /\
                             &0 < (R(kappa(v + inv(&2) % (l - v))))$3})
                 ((\l. moi_smo_gnom(R(kappa(v + inv(&2) % (l - v))))),g)`
  (LABEL_TAC "rchart") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "rot" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `((U:real^N->bool),(kappa:real^N->real^3)) IN S /\
       orthogonal_transformation (R:real^3->real^3)`))) THEN
    STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL
     [`L:real^N->bool`; `Y:real^N->bool`; `v:real^N`; `U:real^N->bool`;
      `\x:real^N. (R:real^3->real^3)((kappa:real^N->real^3) x)`]
      MOI_SLK_CHART)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[smooth_manifold_atlas; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [(* chart conditions *)
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`W:real^N->bool`; `phi:real^N->real^2`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool`
      (X_CHOOSE_THEN `kappa:real^N->real^3`
      (X_CHOOSE_THEN `R:real^3->real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))) THEN
    USE_THEN "rchart" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `((U:real^N->bool),(kappa:real^N->real^3)) IN S /\
       orthogonal_transformation (R:real^3->real^3)`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `g:real^2->real^N`)))) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; MOI_SLK_INTER_RESTRICT] THEN
    MATCH_MP_TAC MOI_SLK_HMAP_OF_HOMEO THEN
    EXISTS_TAC `g:real^2->real^N` THEN FIRST_ASSUM ACCEPT_TAC;
    (* covering *)
    X_GEN_TAC `l:real^N` THEN DISCH_TAC THEN
    USE_THEN "cover" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(l:real^N) IN L`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool`
      (X_CHOOSE_THEN `kappa:real^N->real^3` STRIP_ASSUME_TAC)) THEN
    USE_THEN "rot" (MP_TAC o SPECL
      [`U:real^N->bool`; `kappa:real^N->real^3`; `I:real^3->real^3`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_I];
      REWRITE_TAC[I_THM] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `~((kappa:real^N->real^3)(v + inv(&2) % (l - v)) = vec 0)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_SLK_NONZERO THEN
      MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `v:real^N`] THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      REWRITE_TAC[VECTOR_ARITH `v + inv(&2) % (l - v):real^N = v <=> l = v`] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(kappa:real^N->real^3)(v + inv(&2) % (l - v))`;
                   `norm((kappa:real^N->real^3)(v + inv(&2) % (l - v))) %
                    basis 3:real^3`]
      ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_NORM] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `{x:real^N | x IN L /\ v + inv(&2) % (x - v) IN U /\
                  &0 < ((R:real^3->real^3)
                         ((kappa:real^N->real^3)(v + inv(&2) % (x - v))))$3}` THEN
    EXISTS_TAC
     `\x:real^N. moi_smo_gnom((R:real^3->real^3)
                   ((kappa:real^N->real^3)(v + inv(&2) % (x - v))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
      MAP_EVERY EXISTS_TAC
       [`U:real^N->bool`; `kappa:real^N->real^3`; `R:real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH;
               REAL_MUL_RID] THEN
      ASM_REWRITE_TAC[NORM_POS_LT]];
    (* transition maps *)
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`W1:real^N->bool`; `phi1:real^N->real^2`;
                         `W2:real^N->bool`; `phi2:real^N->real^2`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `U1:real^N->bool` (X_CHOOSE_THEN `kappa1:real^N->real^3`
        (X_CHOOSE_THEN `R1:real^3->real^3`
          (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))))
      (X_CHOOSE_THEN `U2:real^N->bool` (X_CHOOSE_THEN `kappa2:real^N->real^3`
        (X_CHOOSE_THEN `R2:real^3->real^3`
          (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))))) THEN
    USE_THEN "rchart" (MP_TAC o SPECL
      [`U1:real^N->bool`; `kappa1:real^N->real^3`; `R1:real^3->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `g1:real^2->real^N`)))) THEN
    USE_THEN "rchart" (MP_TAC o SPECL
      [`U2:real^N->bool`; `kappa2:real^N->real^3`; `R2:real^3->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
    USE_THEN "rot" (MP_TAC o SPECL
      [`U1:real^N->bool`; `kappa1:real^N->real^3`; `R1:real^3->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "rot" (MP_TAC o SPECL
      [`U2:real^N->bool`; `kappa2:real^N->real^3`; `R2:real^3->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "trans" (MP_TAC o SPECL
      [`U1:real^N->bool`; `kappa1:real^N->real^3`;
       `U2:real^N->bool`; `kappa2:real^N->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `G0:real^3->real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`Y:real^N->bool`; `U1:real^N->bool`; `U2:real^N->bool`;
                   `kappa1:real^N->real^3`; `kappa2:real^N->real^3`;
                   `G0:real^3->real^3`; `R1:real^3->real^3`; `R2:real^3->real^3`]
      MOI_SLK_ROT_TRANS) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^3->real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_SLK_TRANS_ABS THEN
    MAP_EVERY EXISTS_TAC
     [`g1:real^2->real^N`; `v:real^N`; `U1:real^N->bool`; `U2:real^N->bool`;
      `\x:real^N. (R1:real^3->real^3)((kappa1:real^N->real^3) x)`;
      `\x:real^N. (R2:real^3->real^3)((kappa2:real^N->real^3) x)`;
      `G:real^3->real^3`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(SIMP_TAC[IN_ELIM_THM] THEN NO_TAC) THEN
    MATCH_MP_TAC MOI_SLK_IMAGE_INTER_OPEN THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `g1:real^2->real^N`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The instance for the star atlas at a vertex v of a finite combinatorial  *)
(* 3-manifold (C3 from pc_moi_smo_base, C4 as the hypothesis                *)
(* MOI_SMO_EDGE_STATEMENT), and the theorem C6 from C4.                     *)
(* ------------------------------------------------------------------------- *)

(* The link: homeomorphic to S^2, avoids v, midpoints lie in the polyhedron *)
(* and every ray from v meets it at most once.                              *)

let MOI_SLK_LINK_BASICS = prove
 (`!c (v:real^N).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
     ==> UNIONS(simplicial_link c v) homeomorphic sphere(vec 0:real^3,&1) /\
         ~(v IN UNIONS(simplicial_link c v)) /\
         (!l. l IN UNIONS(simplicial_link c v)
              ==> v + inv(&2) % (l - v) IN UNIONS c) /\
         (!l1 l2 r1 r2. l1 IN UNIONS(simplicial_link c v) /\
                        l2 IN UNIONS(simplicial_link c v) /\
                        &0 < r1 /\ &0 < r2 /\
                        v + r1 % (l1 - v) = v + r2 % (l2 - v) ==> l1 = l2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_CM_FACTS];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `v:real^N`]
      MOI_CMB_LINK_IN_STAR) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    X_GEN_TAC `l:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `l:real^N`]
      MOI_CMB_LINK_IN_STAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_MESON_TAC[MOI_SBA_LF_CONVEX];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `l1:real^N`;
                   `l2:real^N`; `r1:real`; `r2:real`] MOI_CMB_CONE_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* The polyhedron minus its 1-skeleton is open in the polyhedron.           *)

let MOI_SLK_X1_OPEN = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c
     ==> open_in (subtopology euclidean (UNIONS c))
                 (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed (UNIONS {e:real^N->bool | e IN c /\ aff_dim e <= &1})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[MOI_SBA_LF_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1} =
    UNIONS c INTER
    ((:real^N) DIFF UNIONS {e:real^N->bool | e IN c /\ aff_dim e <= &1})`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed]);;

(* Chart conditions for the members of the star atlas.                      *)

let MOI_SLK_STAR_CHART_OK = prove
 (`!u c (v:real^N) U (kappa:real^N->real^3).
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\
     (U,kappa) IN moi_smo_star_atlas c v
     ==> open_in (subtopology euclidean (UNIONS c)) U /\ open (IMAGE kappa U) /\
         homeomorphic_map (subtopology euclidean U,
                           subtopology euclidean (IMAGE kappa U)) kappa`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((U:real^N->bool),(kappa:real^N->real^3)) IN
      moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c \/
    (U,kappa) IN moi_smo_edge_atlas c`
  MP_TAC THENL
   [UNDISCH_TAC
     `((U:real^N->bool),(kappa:real^N->real^3)) IN moi_smo_star_atlas c v` THEN
    REWRITE_TAC[MOI_SBA_STAR_ATLAS_IN; IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_SBA_ATLAS) THEN
    ASM_REWRITE_TAC[smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `kappa:real^N->real^3`] o
               CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(U:real^N->bool) SUBSET
      UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}`
    ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS THEN
      EXISTS_TAC `UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}:real^N->bool` THEN
      ASM_SIMP_TAC[MOI_SLK_X1_OPEN];
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC
       `homeomorphic_map
         (subtopology (subtopology euclidean
            (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})) U,
          subtopology euclidean (IMAGE (kappa:real^N->real^3) U)) kappa` THEN
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      SUBGOAL_THEN
       `(UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}) INTER U =
        (U:real^N->bool)`
      SUBST1_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]]];
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^N->bool)->bool` o
                  GEN_REWRITE_RULE I [MOI_SMO_EDGE_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* Transitions between members of the star atlas.                           *)

let MOI_SLK_STAR_TRANS = prove
 (`!u c (v:real^N) U (kappa:real^N->real^3) V psi.
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\
     (U,kappa) IN moi_smo_star_atlas c v /\ (V,psi) IN moi_smo_star_atlas c v
     ==> ?g. smooth_map_on (IMAGE kappa (U INTER V)) g /\
             !x. x IN U INTER V ==> g(kappa x) = psi x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^N->bool)->bool` o
                GEN_REWRITE_RULE I [MOI_SMO_EDGE_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "et"))) THEN
  SUBGOAL_THEN
   `((U:real^N->bool),(kappa:real^N->real^3)) IN
      moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
      moi_smo_edge_atlas c /\
    ((V:real^N->bool),(psi:real^N->real^3)) IN
      moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
      moi_smo_edge_atlas c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_STAR_ATLAS_IN]; ALL_TAC] THEN
  ASM_CASES_TAC
   `((U:real^N->bool),(kappa:real^N->real^3)) IN moi_smo_edge_atlas c` THENL
   [USE_THEN "et" (MP_TAC o SPECL [`U:real^N->bool`; `kappa:real^N->real^3`;
                                   `V:real^N->bool`; `psi:real^N->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `((V:real^N->bool),(psi:real^N->real^3)) IN moi_smo_edge_atlas c` THENL
   [USE_THEN "et" (MP_TAC o SPECL [`V:real^N->bool`; `psi:real^N->real^3`;
                                   `U:real^N->bool`; `kappa:real^N->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBST1_TAC(ISPECL [`V:real^N->bool`; `U:real^N->bool`] INTER_COMM) THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_SBA_ATLAS) THEN
  ASM_REWRITE_TAC[smooth_manifold_atlas] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_UNION]) THEN
  REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[]);;

(* The star atlas covers the midpoints of v with the points of the link.    *)

let MOI_SLK_STAR_COVER = prove
 (`!u c (v:real^N).
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\ {v} IN c
     ==> !l. l IN UNIONS(simplicial_link c v)
             ==> ?U kappa. (U,kappa) IN moi_smo_star_atlas c v /\
                           v + inv(&2) % (l - v) IN U`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `l:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_CM_FACTS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `l:real^N`]
    MOI_CMB_LINK_IN_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(v:real^N = l)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `v + inv(&2) % (l - v) IN (t:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_MESON_TAC[MOI_SBA_LF_CONVEX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v + inv(&2) % (l - v):real^N`]
    MOI_SBA_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`; `t:real^N->bool`]
    MOI_SBA_RELINT_MEETS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN r /\ l IN r` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(r:real^N->bool) face_of t` THEN REWRITE_TAC[face_of] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `v + inv(&2) % (l - v):real^N` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      SUBGOAL_THEN `v + inv(&2) % (l - v):real^N = midpoint(v,l)` SUBST1_TAC THENL
       [REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
        ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of r` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_VERTEX_EXTREME THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `aff_dim(r:real^N->bool) = &1 \/ aff_dim r = &2 \/ aff_dim r = &3`
  MP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`] MOI_SBA_DIM_LE3) THEN
    MP_TAC(ISPECL [`{v:real^N,l}`; `r:real^N->bool`] AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[AFF_DIM_2] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^N->bool)->bool` o
                  GEN_REWRITE_RULE I [MOI_SMO_EDGE_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`r:real^N->bool`; `v:real^N`] o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `kappa:real^N->real^3` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`moi_smo_open_star c (r:real^N->bool)`;
                          `kappa:real^N->real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_SBA_RELINT_IN_STAR; SUBSET];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`; `v:real^N`]
      MOI_SBA_TRI_STAR_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->real^3` ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`moi_smo_open_star c (r:real^N->bool)`;
                          `w:real^N->real^3`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_SBA_RELINT_IN_STAR; SUBSET];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`; `v:real^N`]
      MOI_SBA_TET_STAR_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`relative_interior(r:real^N->bool)`;
                          `A:real^N->real^3`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem: C4 implies C6.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_SMO_LINK_ATLAS_FROM_EDGE = prove
 (`!u:N->bool. MOI_SMO_EDGE_STATEMENT u ==> MOI_SMO_LINK_ATLAS_STATEMENT u`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MOI_SMO_LINK_ATLAS_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SLK_LINK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_smo_link_atlas] THEN
  MATCH_MP_TAC MOI_SLK_GNOM_ATLAS THEN
  EXISTS_TAC `UNIONS c:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `kappa:real^N->real^3`] THEN
    DISCH_TAC THEN MATCH_MP_TAC MOI_SLK_STAR_CHART_OK THEN
    MAP_EVERY EXISTS_TAC [`u:N->bool`; `v:real^N`] THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN REWRITE_TAC[MOI_SBA_STAR_ATLAS_IN] THEN MESON_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_SLK_STAR_TRANS THEN
    MAP_EVERY EXISTS_TAC [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SLK_STAR_COVER THEN EXISTS_TAC `u:N->bool` THEN
    ASM_REWRITE_TAC[]]);;

