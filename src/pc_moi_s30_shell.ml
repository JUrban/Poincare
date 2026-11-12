(* ========================================================================= *)
(* pc_moi_s30_shell: spherical and toroidal shells (Moise GTM 47, background *)
(* of 30.4-30.8, printed pp.215-218).  Main theorems SPHERICAL_SHELL_FACTS,  *)
(* TOROIDAL_SHELL_FACTS, SHELL_NO_SPHERE, SHELL_CORE_ESSENTIAL (statements   *)
(* of pc_moi_s3032_stmt).                                                    *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_p305.ml";;     (* MOI_P35_HOMEO_INTERIOR *)
needs "src/pc_moi_s308.ml";;     (* solid torus loops, MOI_S38_CORE *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* 1. Interiors under homeomorphisms of subsets of euclidean                *)
(* spaces of the same dimension (invariance of domain both ways), and the   *)
(* interior of the closed annulus of real^3 (the ends are not interior by   *)
(* MOI_P35_SHELL_ENDS).                                                      *)
(* ========================================================================= *)

let MOI_S3SH_HOMEO_INTERIOR_GEN = prove
 (`!(K:real^M->bool) (X:real^N->bool) (h:real^M->real^N) k.
     dimindex(:M) = dimindex(:N) /\ homeomorphism (K,X) (h,k)
     ==> interior X = IMAGE h (interior K)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC o
                GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    SUBGOAL_THEN `(q:real^N) IN X` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(q:real^N,e) SUBSET X` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    EXISTS_TAC `(k:real^N->real^M) q` THEN CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `open (IMAGE (k:real^N->real^M) (ball(q,e)))` ASSUME_TAC THENL
     [MATCH_MP_TAC INVARIANCE_OF_DOMAIN_GEN THEN REWRITE_TAC[OPEN_BALL] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `dimindex(:M) = dimindex(:N)` THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `X:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
        SUBGOAL_THEN `(a:real^N) IN X /\ (b:real^N) IN X` STRIP_ASSUME_TAC THENL
         [ASM SET_TAC[]; ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (k:real^N->real^M) (ball(q,e)) SUBSET interior K` MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `q:real^N`) THEN ASM_SIMP_TAC[CENTRE_IN_BALL];
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `K:real^M->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      MATCH_MP_TAC INVARIANCE_OF_DOMAIN_GEN THEN REWRITE_TAC[OPEN_INTERIOR] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `dimindex(:M) = dimindex(:N)` THEN ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `K:real^M->bool` THEN
        ASM_REWRITE_TAC[INTERIOR_SUBSET];
        MP_TAC(ISPEC `K:real^M->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]]]]);;

let MOI_S3SH_HOMEO_INTERIOR = prove
 (`!(K:real^N->bool) (X:real^N->bool) (h:real^N->real^N) k.
     homeomorphism (K,X) (h,k) ==> interior X = IMAGE h (interior K)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3SH_HOMEO_INTERIOR_GEN THEN
  EXISTS_TAC `k:real^N->real^N` THEN ASM_REWRITE_TAC[]);;

(* The interior of the closed annulus. *)

let MOI_S3SH_ANNULUS_INTERIOR = prove
 (`interior {y:real^3 | &1 <= norm y /\ norm y <= &2} =
   {y:real^3 | &1 < norm y /\ norm y < &2}`,
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPEC `y:real^3` MOI_P35_SHELL_ENDS) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `{y:real^3 | &1 <= norm y /\ norm y <= &2}` INTERIOR_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `{y:real^3 | &1 < norm y /\ norm y < &2} = ball(vec 0,&2) DIFF cball(vec 0,&1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_DIFF; IN_BALL_0; IN_CBALL_0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      SIMP_TAC[OPEN_DIFF; OPEN_BALL; CLOSED_CBALL]]]);;

(* ========================================================================= *)
(* 2. Spherical shells (the theorem SPHERICAL_SHELL_FACTS).  The model is    *)
(* the closed annulus 1 <= |y| <= 2 of real^3; its interior is the open      *)
(* annulus (section 1), homeomorphic to sphere(0,1) PCROSS (1,2), simply     *)
(* connected.                                                                *)
(* ========================================================================= *)

(* The open annulus is homeomorphic to a sphere times an open interval. *)

let MOI_S3SH_ANNULUS_PCROSS = prove
 (`homeomorphism (sphere(vec 0:real^3,&1) PCROSS {t:real^1 | &1 < drop t /\ drop t < &2},
                  {y:real^3 | &1 < norm y /\ norm y < &2})
                 ((\z:real^(3,1)finite_sum. drop(sndcart z) % fstcart z),
                  (\y:real^3. pastecart (inv(norm y) % y) (lift(norm y))))`,
  REWRITE_TAC[homeomorphism; FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART;
              PASTECART_IN_PCROSS; IN_ELIM_THM; IN_SPHERE_0] THEN
  REPEAT CONJ_TAC THENL
   [(* left inverse *)
    MAP_EVERY X_GEN_TAC [`u:real^3`; `t:real^1`] THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_MUL; PASTECART_INJ; VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN
    SUBGOAL_THEN `abs(drop t) = drop t` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~(drop t = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID; LIFT_DROP];
    (* the image of the forward map *)
    REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART;
                PASTECART_IN_PCROSS; IN_ELIM_THM; IN_SPHERE_0] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`inv(norm y) % y:real^3`; `lift(norm(y:real^3))`] THEN
      REWRITE_TAC[LIFT_DROP; VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      SUBGOAL_THEN `~(norm(y:real^3) = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LINV; VECTOR_MUL_LID]];
    (* continuity of the forward map *)
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART; ETA_AX];
    (* right inverse *)
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `~(norm(y:real^3) = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID];
    (* the image of the backward map *)
    REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_ELIM_THM; IN_SPHERE_0;
                PASTECART_INJ] THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `t:real^1`] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM; LIFT_DROP] THEN
      SUBGOAL_THEN `~(norm(y:real^3) = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN EXISTS_TAC `drop t % u:real^3` THEN
      ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
      SUBGOAL_THEN `abs(drop t) = drop t` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(drop t = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID; LIFT_DROP] THEN
      ASM_REAL_ARITH_TAC];
    (* continuity of the backward map *)
    MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      SUBGOAL_THEN `(\y:real^3. inv(norm y)) = inv o norm` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_INV THEN REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_NORM]]]);;

let MOI_S3SH_OPEN_ANNULUS_SC = prove
 (`simply_connected {y:real^3 | &1 < norm y /\ norm y < &2}`,
  MATCH_MP_TAC(ISPECL [`sphere(vec 0:real^3,&1) PCROSS {t:real^1 | &1 < drop t /\ drop t < &2}`;
                       `{y:real^3 | &1 < norm y /\ norm y < &2}`]
                      HOMEOMORPHIC_SIMPLY_CONNECTED) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`\z:real^(3,1)finite_sum. drop(sndcart z) % fstcart z`;
                          `\y:real^3. pastecart (inv(norm y) % y) (lift(norm y))`] THEN
    REWRITE_TAC[MOI_S3SH_ANNULUS_PCROSS];
    MATCH_MP_TAC SIMPLY_CONNECTED_PCROSS THEN CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLY_CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
      MATCH_MP_TAC CONVEX_IMP_SIMPLY_CONNECTED THEN
      SUBGOAL_THEN `{t:real^1 | &1 < drop t /\ drop t < &2} = interval(lift(&1),lift(&2))`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP];
        REWRITE_TAC[CONVEX_INTERVAL]]]]);;

(* The basic facts. *)

let SPHERICAL_SHELL_FACTS = prove
 (MOI_S30_SPHERICAL_SHELL_FACTS,
  REWRITE_TAC[spherical_shell] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `k:real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ABBREV_TAC `K = {y:real^3 | &1 <= norm y /\ norm y <= &2}` THEN
  SUBGOAL_THEN `compact (K:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[MOI_P35_SHELL_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET K /\ sphere(vec 0:real^3,&2) SUBSET K`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. &0 <= r /\ sphere(vec 0:real^3,r) SUBSET K
                    ==> compact(IMAGE (h:real^3->real^3) (sphere(vec 0,r))) /\
                        connected(IMAGE h (sphere(vec 0,r))) /\
                        ~(IMAGE h (sphere(vec 0,r)) = {})`
  (LABEL_TAC "sph") THENL
   [GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_SPHERE] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_3; ARITH] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "sph" (MP_TAC o SPEC `&1`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POS]; STRIP_TAC] THEN
  USE_THEN "sph" (MP_TAC o SPEC `&2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POS]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) K = x` (SUBST_ALL_TAC o SYM) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interior (IMAGE (h:real^3->real^3) K) = IMAGE h (interior K)` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S3SH_HOMEO_INTERIOR THEN EXISTS_TAC `k:real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior K = {y:real^3 | &1 < norm y /\ norm y < &2}` SUBST1_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[MOI_S3SH_ANNULUS_INTERIOR]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a IN K /\ b IN K /\ (h:real^3->real^3) a = h b ==> a = b`
  (LABEL_TAC "inj") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | &1 < norm y /\ norm y < &2} SUBSET K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `K = {x:real^3 | &1 <= norm x /\ norm x < &2} UNION
                      {x:real^3 | &1 < norm x /\ norm x <= &2}` SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `&2`] (el 2 (CONJUNCTS CONNECTED_ANNULUS))) THEN
      REWRITE_TAC[VECTOR_SUB_RZERO; DIMINDEX_3; ARITH];
      MP_TAC(ISPECL [`vec 0:real^3`; `&1`; `&2`] (el 1 (CONJUNCTS CONNECTED_ANNULUS))) THEN
      REWRITE_TAC[VECTOR_SUB_RZERO; DIMINDEX_3; ARITH];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      EXISTS_TAC `(&3 / &2) % basis 1:real^3` THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC];
    (* disjoint ends *)
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `w:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:real^3) = b` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM SET_TAC[];
      UNDISCH_TAC `(a:real^3) IN sphere(vec 0,&1)` THEN
      UNDISCH_TAC `(b:real^3) IN sphere(vec 0,&2)` THEN
      REWRITE_TAC[IN_SPHERE_0] THEN MESON_TAC[REAL_ARITH `~(&1 = &2)`]];
    (* the ends lie in the shell *)
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[];
    (* the interior *)
    SUBGOAL_THEN `{y:real^3 | &1 < norm y /\ norm y < &2} =
                  K DIFF (sphere(vec 0,&1) UNION sphere(vec 0,&2))` SUBST1_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_SPHERE_0; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x y. x IN K /\ y IN K /\ (h:real^3->real^3) x = h y ==> x = y) /\
      A SUBSET K /\ B SUBSET K
      ==> IMAGE h (K DIFF (A UNION B)) = IMAGE h K DIFF (IMAGE h A UNION IMAGE h B)`) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    (* simply connected *)
    MATCH_MP_TAC(ISPECL [`{y:real^3 | &1 < norm y /\ norm y < &2}`;
                         `IMAGE (h:real^3->real^3) {y:real^3 | &1 < norm y /\ norm y < &2}`]
                        HOMEOMORPHIC_SIMPLY_CONNECTED) THEN
    REWRITE_TAC[MOI_S3SH_OPEN_ANNULUS_SC] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`h:real^3->real^3`; `k:real^3->real^3`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`K:real^3->bool`; `IMAGE (h:real^3->real^3) K`] THEN
    ASM_SIMP_TAC[SUBSET_REFL; IMAGE_SUBSET]]);;

(* ========================================================================= *)
(* 3. The toroidal model.  It lives in real^(2,1)finite_sum (a copy of       *)
(* real^3 in cylindrical form, matched with real^3 by the dimension form of  *)
(* section 1): moi_s3sh_tor u v s puts the point (u,v) of the torus at       *)
(* distance 1 + s from the core circle of radius 4, and moi_s3sh_rho is the  *)
(* distance to that circle.  For unit u, v and 0 < 1 + s < 4 the map is      *)
(* injective with rho = 1 + s and onto the set 0 < rho < 4; so the model (S1 *)
(* x S1) x [0,1] is homeomorphic to {1 <= rho <= 2}, whose interior is {1 <  *)
(* rho < 2} (moving s slightly outside [0,1] leaves the set).                *)
(* ========================================================================= *)

let moi_s3sh_tor = new_definition
 `moi_s3sh_tor (u:real^2) (v:real^2) (s:real) =
    pastecart ((&4 + (&1 + s) * v$1) % u) (lift((&1 + s) * v$2)):real^(2,1)finite_sum`;;

let moi_s3sh_phi = new_definition
 `moi_s3sh_phi (x:real^((2,2)finite_sum,1)finite_sum) =
    moi_s3sh_tor (fstcart(fstcart x)) (sndcart(fstcart x)) (drop(sndcart x))`;;

let moi_s3sh_rho = new_definition
 `moi_s3sh_rho (w:real^(2,1)finite_sum) =
    norm(vector[norm(fstcart w) - &4; drop(sndcart w)]:real^2)`;;

let MOI_S3SH_UNIT_COMPONENTS = prove
 (`!v:real^2. norm v = &1 ==> abs(v$1) <= &1 /\ abs(v$2) <= &1`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`v:real^2`; `1`] COMPONENT_LE_NORM) THEN
  MP_TAC(ISPECL [`v:real^2`; `2`] COMPONENT_LE_NORM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_S3SH_TOR_C = prove
 (`!(v:real^2) s.
     norm v = &1 /\ &0 < &1 + s /\ &1 + s < &4
     ==> abs((&1 + s) * v$1) <= &1 + s /\ &0 < &4 + (&1 + s) * v$1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3SH_UNIT_COMPONENTS) THEN
  SUBGOAL_THEN `abs((&1 + s) * (v:real^2)$1) <= &1 + s` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(&1 + s) = &1 + s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S3SH_TOR_RHO = prove
 (`!(u:real^2) (v:real^2) s.
     norm u = &1 /\ norm v = &1 /\ &0 < &1 + s /\ &1 + s < &4
     ==> moi_s3sh_rho (moi_s3sh_tor u v s) = &1 + s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`v:real^2`; `s:real`] MOI_S3SH_TOR_C) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[moi_s3sh_rho; moi_s3sh_tor; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
              NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_MUL_RID; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `norm((&1 + s) % v:real^2)` THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S3SH_TOR_INJ = prove
 (`!(u:real^2) (v:real^2) s (u':real^2) (v':real^2) s'.
     norm u = &1 /\ norm v = &1 /\ &0 < &1 + s /\ &1 + s < &4 /\
     norm u' = &1 /\ norm v' = &1 /\ &0 < &1 + s' /\ &1 + s' < &4 /\
     moi_s3sh_tor u v s = moi_s3sh_tor u' v' s'
     ==> u = u' /\ v = v' /\ s = s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `s:real = s'` SUBST_ALL_TAC THENL
   [MP_TAC(SPECL [`u:real^2`; `v:real^2`; `s:real`] MOI_S3SH_TOR_RHO) THEN
    MP_TAC(SPECL [`u':real^2`; `v':real^2`; `s':real`] MOI_S3SH_TOR_RHO) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_s3sh_tor u v s' = moi_s3sh_tor u' v' s'` THEN
  REWRITE_TAC[moi_s3sh_tor; PASTECART_INJ; LIFT_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^2)$2 = (v':real^2)$2` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + s') * (v:real^2)$2 = (&1 + s') * (v':real^2)$2` THEN
    REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`v:real^2`; `s':real`] MOI_S3SH_TOR_C) THEN
  MP_TAC(SPECL [`v':real^2`; `s':real`] MOI_S3SH_TOR_C) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^2)$1 = (v':real^2)$1` ASSUME_TAC THENL
   [UNDISCH_TAC `(&4 + (&1 + s') * (v:real^2)$1) % (u:real^2) =
                 (&4 + (&1 + s') * (v':real^2)$1) % (u':real^2)` THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:real^2->real`) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&4 + (&1 + s') * (v:real^2)$1 = &4 + (&1 + s') * (v':real^2)$1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_EQ_ADD_LCANCEL; REAL_EQ_MUL_LCANCEL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(&4 + (&1 + s') * (v:real^2)$1) % (u:real^2) =
               (&4 + (&1 + s') * (v':real^2)$1) % (u':real^2)` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2]);;

let MOI_S3SH_TOR_SURJ = prove
 (`!w. &0 < moi_s3sh_rho w /\ moi_s3sh_rho w < &4
       ==> ?u v. norm(u:real^2) = &1 /\ norm(v:real^2) = &1 /\
                 moi_s3sh_tor u v (moi_s3sh_rho w - &1) = w`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `r = norm(fstcart(w:real^(2,1)finite_sum))` THEN
  ABBREV_TAC `m = vector[r - &4; drop(sndcart(w:real^(2,1)finite_sum))]:real^2` THEN
  SUBGOAL_THEN `norm(m:real^2) = moi_s3sh_rho w` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "r"] THEN REWRITE_TAC[moi_s3sh_rho]; ALL_TAC] THEN
  ABBREV_TAC `rh = moi_s3sh_rho w` THEN
  SUBGOAL_THEN `(m:real^2)$1 = r - &4 /\ m$2 = drop(sndcart(w:real^(2,1)finite_sum))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "m" THEN REWRITE_TAC[VECTOR_2]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(r - &4) <= rh` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:real^2`; `1`] COMPONENT_LE_NORM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`inv r % fstcart(w:real^(2,1)finite_sum)`; `inv rh % (m:real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3sh_tor; VECTOR_MUL_COMPONENT] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&4 + (&1 + (rh - &1)) * inv rh * (r - &4) = r /\
                (&1 + (rh - &1)) * inv rh * drop(sndcart(w:real^(2,1)finite_sum)) =
                drop(sndcart w)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < rh` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID; LIFT_DROP;
               PASTECART_FST_SND]);;

let MOI_S3SH_TOR_DIST = prove
 (`!(u:real^2) (v:real^2) s t.
     norm u = &1 /\ norm v = &1
     ==> norm(moi_s3sh_tor u v s - moi_s3sh_tor u v t) <= &2 * abs(s - t)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3SH_UNIT_COMPONENTS o
    check (fun th -> concl th = `norm(v:real^2) = &1`)) THEN
  REWRITE_TAC[moi_s3sh_tor; PASTECART_SUB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((&4 + (&1 + s) * (v:real^2)$1) % (u:real^2) -
                   (&4 + (&1 + t) * v$1) % u) +
              norm(lift((&1 + s) * (v:real^2)$2) - lift((&1 + t) * v$2))` THEN
  REWRITE_TAC[NORM_PASTECART_LE] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; GSYM LIFT_SUB; NORM_MUL; NORM_LIFT] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN
  SUBGOAL_THEN `(&4 + (&1 + s) * (v:real^2)$1) - (&4 + (&1 + t) * v$1) = (s - t) * v$1 /\
                (&1 + s) * (v:real^2)$2 - (&1 + t) * v$2 = (s - t) * v$2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH `a * x <= a * &1 /\ a * y <= a * &1 ==> a * x + a * y <= &2 * a`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

(* Continuity of rho and of the parametrization. *)

let MOI_S3SH_RHO_CONTINUOUS = prove
 (`!s. (lift o moi_s3sh_rho) continuous_on s`,
  GEN_TAC THEN REWRITE_TAC[o_DEF; moi_s3sh_rho] THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
  GEN_REWRITE_TAC I [CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`] THEN
  X_GEN_TAC `i:num` THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[VECTOR_2] THENL
   [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; ETA_AX];
    REWRITE_TAC[LIFT_DROP; ETA_AX] THEN SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART]]);;

let MOI_S3SH_PHI_CONTINUOUS = prove
 (`!s. moi_s3sh_phi continuous_on s`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `moi_s3sh_phi =
    (\x:real^((2,2)finite_sum,1)finite_sum.
       pastecart ((&4 + (&1 + drop(sndcart x)) * (sndcart(fstcart x))$1) %
                  fstcart(fstcart x))
                 (lift((&1 + drop(sndcart x)) * (sndcart(fstcart x))$2)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_s3sh_phi; moi_s3sh_tor]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (\x:real^((2,2)finite_sum,1)finite_sum. lift((sndcart(fstcart x))$i))
        continuous_on s`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    SUBGOAL_THEN `(\x:real^((2,2)finite_sum,1)finite_sum. sndcart(fstcart x)) =
                  sndcart o fstcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN MATCH_MP_TAC LINEAR_COMPOSE THEN
    REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lift o (\x:real^((2,2)finite_sum,1)finite_sum. &1 + drop(sndcart x))) continuous_on s`
  ASSUME_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_DROP] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(\x:real^((2,2)finite_sum,1)finite_sum. fstcart(fstcart x)) =
                    fstcart o fstcart` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN MATCH_MP_TAC LINEAR_COMPOSE THEN
      REWRITE_TAC[LINEAR_FSTCART]];
    REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    ASM_REWRITE_TAC[]]);;

(* The image of a product of the torus with a set of levels. *)

let MOI_S3SH_MODEL_IMAGE = prove
 (`!P. (!t. P t ==> -- &1 < t /\ t < &3)
       ==> IMAGE moi_s3sh_phi
                 ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                  {s:real^1 | P(drop s)}) =
           {w | P(moi_s3sh_rho w - &1)}`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS; IN_SPHERE_0;
              IN_ELIM_THM; moi_s3sh_phi; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  X_GEN_TAC `w:real^(2,1)finite_sum` THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`; `s:real^1`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop s`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`u:real^2`; `v:real^2`; `drop s`] MOI_S3SH_TOR_RHO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[REAL_ARITH `(&1 + x) - &1 = x`];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `moi_s3sh_rho w - &1`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(SPEC `w:real^(2,1)finite_sum` MOI_S3SH_TOR_SURJ) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^2` (X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`u:real^2`; `v:real^2`; `lift(moi_s3sh_rho w - &1)`] THEN
    ASM_REWRITE_TAC[LIFT_DROP]]);;

let MOI_S3SH_MODEL_IMAGES = prove
 (`IMAGE moi_s3sh_phi
     ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
      interval[vec 0:real^1,vec 1]) =
   {w | &1 <= moi_s3sh_rho w /\ moi_s3sh_rho w <= &2} /\
   IMAGE moi_s3sh_phi
     ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
      interval(vec 0:real^1,vec 1)) =
   {w | &1 < moi_s3sh_rho w /\ moi_s3sh_rho w < &2}`,
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `interval[vec 0:real^1,vec 1] = {s | &0 <= drop s /\ drop s <= &1} /\
      {w | &1 <= moi_s3sh_rho w /\ moi_s3sh_rho w <= &2} =
      {w | &0 <= moi_s3sh_rho w - &1 /\ moi_s3sh_rho w - &1 <= &1}`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_ELIM_THM; DROP_VEC] THEN
      REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `\t. &0 <= t /\ t <= &1` MOI_S3SH_MODEL_IMAGE);
    SUBGOAL_THEN
     `interval(vec 0:real^1,vec 1) = {s | &0 < drop s /\ drop s < &1} /\
      {w | &1 < moi_s3sh_rho w /\ moi_s3sh_rho w < &2} =
      {w | &0 < moi_s3sh_rho w - &1 /\ moi_s3sh_rho w - &1 < &1}`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_ELIM_THM; DROP_VEC] THEN
      REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `\t. &0 < t /\ t < &1` MOI_S3SH_MODEL_IMAGE)] THEN
  REWRITE_TAC[] THEN (ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN ACCEPT_TAC]));;

(* The interior of the model. *)

let MOI_S3SH_MODEL_INTERIOR = prove
 (`interior {w | &1 <= moi_s3sh_rho w /\ moi_s3sh_rho w <= &2} =
   {w | &1 < moi_s3sh_rho w /\ moi_s3sh_rho w < &2}`,
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w:real^(2,1)finite_sum` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= moi_s3sh_rho w /\ moi_s3sh_rho w <= &2` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `{w:real^(2,1)finite_sum | &1 <= moi_s3sh_rho w /\ moi_s3sh_rho w <= &2}`
                   INTERIOR_SUBSET) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `w:real^(2,1)finite_sum`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ball"))) THEN
    MP_TAC(SPEC `w:real^(2,1)finite_sum` MOI_S3SH_TOR_SURJ) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^2` (X_CHOOSE_THEN `v:real^2` STRIP_ASSUME_TAC)) THEN
    ABBREV_TAC `d = min (e / &4) (&1 / &2)` THEN
    SUBGOAL_THEN `&0 < d /\ &2 * d < e /\ d <= &1 / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `!t. abs(t - (moi_s3sh_rho w - &1)) <= d ==> &1 <= &1 + t /\ &1 + t <= &2`
    (LABEL_TAC "near") THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < &1 + t /\ &1 + t < &4` STRIP_ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`u:real^2`; `v:real^2`; `t:real`] MOI_S3SH_TOR_RHO) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN
       `moi_s3sh_tor u v t IN
        {w:real^(2,1)finite_sum | &1 <= moi_s3sh_rho w /\ moi_s3sh_rho w <= &2}`
      MP_TAC THENL [ALL_TAC; REWRITE_TAC[IN_ELIM_THM]] THEN
      USE_THEN "ball" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL; dist] THEN
      MP_TAC(SPECL [`u:real^2`; `v:real^2`; `moi_s3sh_rho w - &1`; `t:real`]
                   MOI_S3SH_TOR_DIST) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b /\ ~(a = b) ==> a < b`) THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN USE_THEN "near" (MP_TAC o SPEC `moi_s3sh_rho w - &1 - d`) THEN
      ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN USE_THEN "near" (MP_TAC o SPEC `moi_s3sh_rho w - &1 + d`) THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`lift o moi_s3sh_rho`; `(:real^(2,1)finite_sum)`;
                   `interval(lift(&1),lift(&2))`] CONTINUOUS_OPEN_PREIMAGE) THEN
    REWRITE_TAC[MOI_S3SH_RHO_CONTINUOUS; OPEN_UNIV; OPEN_INTERVAL; IN_UNIV;
                IN_INTERVAL_1; o_THM; LIFT_DROP]]);;

(* The model homeomorphism. *)

let MOI_S3SH_MODEL = prove
 (`?psi. homeomorphism
           ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
            interval[vec 0:real^1,vec 1],
            {w | &1 <= moi_s3sh_rho w /\ moi_s3sh_rho w <= &2})
           (moi_s3sh_phi,psi)`,
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  REWRITE_TAC[MOI_S3SH_PHI_CONTINUOUS; MOI_S3SH_MODEL_IMAGES] THEN CONJ_TAC THENL
   [SIMP_TAC[COMPACT_PCROSS; COMPACT_SPHERE; COMPACT_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SPHERE_0; IN_INTERVAL_1; DROP_VEC;
              moi_s3sh_phi; FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_INJ] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`; `s:real^1`;
                       `u':real^2`; `v':real^2`; `s':real^1`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`u:real^2`; `v:real^2`; `drop s`; `u':real^2`; `v':real^2`; `drop s'`]
               MOI_S3SH_TOR_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; MESON_TAC[DROP_EQ]]);;

(* ========================================================================= *)
(* 4. Toroidal shells (the theorem TOROIDAL_SHELL_FACTS).  By the model of   *)
(* section 3 a toroidal shell is homeomorphic to {1 <= rho <= 2}, so its     *)
(* interior is the image of (S1 x S1) x (0,1) (section 1 in dimension form). *)
(* The shell coordinate is the torus factor of the inverse map; a loop in    *)
(* (S1 x S1) x (0,1) is null-homotopic iff its torus factor is (the interval *)
(* factor is convex).                                                        *)
(* ========================================================================= *)

let MOI_S3SH_PCROSS_CONVEX_LOOPS = prove
 (`!(s:real^M->bool) (t:real^N->bool) q.
     convex t /\ path q /\ pathfinish q = pathstart q /\ path_image q SUBSET s PCROSS t
     ==> (homotopic_loops (s PCROSS t) q (linepath(pathstart q,pathstart q)) <=>
          homotopic_loops s (fstcart o q)
            (linepath(fstcart(pathstart q),fstcart(pathstart q))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real^1->real^(M,N)finite_sum`; `s:real^M->bool`; `t:real^N->bool`]
                MOI_FH1_LOOP_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o CONJUNCT1 o MATCH_MP MOI_FH1_HOMOTOPIC_LOOPS_PROJ) THEN
    REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`sndcart o (q:real^1->real^(M,N)finite_sum)`; `t:real^N->bool`]
                MOI_FH1_CONVEX_NULLHOMOTOPIC) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `t:real^N->bool`;
                 `fstcart o (q:real^1->real^(M,N)finite_sum)`;
                 `sndcart o (q:real^1->real^(M,N)finite_sum)`;
                 `linepath(fstcart(pathstart q):real^M,
                           fstcart(pathstart(q:real^1->real^(M,N)finite_sum)))`;
                 `linepath(sndcart(pathstart q):real^N,
                           sndcart(pathstart(q:real^1->real^(M,N)finite_sum)))`]
                MOI_FH1_HOMOTOPIC_LOOPS_PASTECART) THEN
  ASM_REWRITE_TAC[o_THM; PASTECART_FST_SND; ETA_AX; LINEPATH_REFL]);;

(* Levels of a product with the unit interval. *)

let MOI_S3SH_LEVELS = prove
 (`!s:real^M->bool.
     s PCROSS {vec 0:real^1} SUBSET s PCROSS interval[vec 0,vec 1] /\
     s PCROSS {vec 1:real^1} SUBSET s PCROSS interval[vec 0,vec 1] /\
     DISJOINT (s PCROSS {vec 0:real^1}) (s PCROSS {vec 1}) /\
     s PCROSS interval(vec 0:real^1,vec 1) =
     s PCROSS interval[vec 0,vec 1] DIFF (s PCROSS {vec 0} UNION s PCROSS {vec 1})`,
  GEN_TAC THEN
  REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_DIFF;
              IN_UNION; IN_INTER; NOT_IN_EMPTY; IN_SING; IN_INTERVAL_1; DROP_VEC;
              GSYM DROP_EQ] THEN
  REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^M`; `t:real^1`] THEN
  ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_S3SH_TT_LEVEL = prove
 (`!c:real^1.
     compact ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {c}) /\
     connected ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {c}) /\
     ~((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {c} = {})`,
  GEN_TAC THEN
  SIMP_TAC[COMPACT_PCROSS; COMPACT_SPHERE; COMPACT_SING; CONNECTED_PCROSS;
           CONNECTED_SPHERE; CONNECTED_SING; DIMINDEX_2; LE_REFL; PCROSS_EQ_EMPTY;
           SPHERE_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
  REAL_ARITH_TAC);;

(* The interior of a toroidal shell. *)

let MOI_S3SH_TSHELL_INTERIOR = prove
 (`!(y:real^3->bool) f k.
     homeomorphism ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                    interval[vec 0:real^1,vec 1],y) (f,k)
     ==> interior y =
         IMAGE f ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                  interval(vec 0:real^1,vec 1))`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `psi:real^(2,1)finite_sum->real^((2,2)finite_sum,1)finite_sum`
    (LABEL_TAC "mod") MOI_S3SH_MODEL THEN
  SUBGOAL_THEN
   `homeomorphism ({w | &1 <= moi_s3sh_rho w /\ moi_s3sh_rho w <= &2},y)
                  ((f:real^((2,2)finite_sum,1)finite_sum->real^3) o psi,
                   moi_s3sh_phi o (k:real^3->real^((2,2)finite_sum,1)finite_sum))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                interval[vec 0:real^1,vec 1]` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{w | &1 <= moi_s3sh_rho w /\ moi_s3sh_rho w <= &2}`; `y:real^3->bool`;
                 `(f:real^((2,2)finite_sum,1)finite_sum->real^3) o
                  (psi:real^(2,1)finite_sum->real^((2,2)finite_sum,1)finite_sum)`;
                 `moi_s3sh_phi o (k:real^3->real^((2,2)finite_sum,1)finite_sum)`]
                MOI_S3SH_HOMEO_INTERIOR_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; DIMINDEX_2; DIMINDEX_3] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MOI_S3SH_MODEL_INTERIOR; GSYM(CONJUNCT2 MOI_S3SH_MODEL_IMAGES); IMAGE_o] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
    interval(vec 0:real^1,vec 1) SUBSET
    (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
    interval[vec 0:real^1,vec 1]`
  MP_TAC THENL
   [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; INTERVAL_OPEN_SUBSET_CLOSED];
    ALL_TAC] THEN
  USE_THEN "mod" (MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SET_TAC[]);;

(* The shell coordinate. *)

let MOI_S3SH_TSHELL_COORD = prove
 (`!(y:real^N->bool) f k.
     homeomorphism ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                    interval[vec 0:real^1,vec 1],y) (f,k)
     ==> (fstcart o k) continuous_on y /\
         IMAGE (fstcart o k) y SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
         !p. path p /\ pathfinish p = pathstart p /\
             path_image p SUBSET
             IMAGE f ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                      interval(vec 0:real^1,vec 1))
             ==> (homotopic_loops
                    (IMAGE f ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                              interval(vec 0:real^1,vec 1)))
                    p (linepath(pathstart p,pathstart p)) <=>
                  homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                    ((fstcart o k) o p)
                    (linepath((fstcart o k) (pathstart p),(fstcart o k) (pathstart p))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FH1_IN_PCROSS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `homeomorphism ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                   interval(vec 0:real^1,vec 1),
                   IMAGE (f:real^((2,2)finite_sum,1)finite_sum->real^N)
                     ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                      interval(vec 0:real^1,vec 1))) (f,k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC
     [`(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
       interval[vec 0:real^1,vec 1]`; `y:real^N->bool`] THEN
    SUBGOAL_THEN
     `(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
      interval(vec 0:real^1,vec 1) SUBSET
      (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
      interval[vec 0:real^1,vec 1]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN REWRITE_TAC[SUBSET_REFL; INTERVAL_OPEN_SUBSET_CLOSED];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "y" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
     interval(vec 0:real^1,vec 1)`;
    `IMAGE (f:real^((2,2)finite_sum,1)finite_sum->real^N)
       ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
        interval(vec 0:real^1,vec 1))`;
    `f:real^((2,2)finite_sum,1)finite_sum->real^N`;
    `k:real^N->real^((2,2)finite_sum,1)finite_sum`; `p:real^1->real^N`;
    `linepath(pathstart p:real^N,pathstart p)`] MOI_S38_HOMEO_HOMOTOPIC_LOOPS_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; SUBSET];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL] THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                 `interval(vec 0:real^1,vec 1)`;
                 `(k:real^N->real^((2,2)finite_sum,1)finite_sum) o (p:real^1->real^N)`]
                MOI_S3SH_PCROSS_CONVEX_LOOPS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[CONVEX_INTERVAL] THEN ASM_MESON_TAC[MOI_S38_HOMEO_LOOP]; ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_COMPOSE; o_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[o_THM]);;

(* The theorem TOROIDAL_SHELL_FACTS. *)

let TOROIDAL_SHELL_FACTS = prove
 (MOI_S30_TOROIDAL_SHELL_FACTS,
  REWRITE_TAC[toroidal_shell; moi_s30_tt] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^((2,2)finite_sum,1)finite_sum->real^3`
    (X_CHOOSE_THEN `k:real^3->real^((2,2)finite_sum,1)finite_sum`
      (CONJUNCTS_THEN2 (LABEL_TAC "hom") (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)))) THEN
  USE_THEN "hom" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  MP_TAC(ISPEC `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` MOI_S3SH_LEVELS) THEN
  STRIP_TAC THEN
  (* the levels *)
  SUBGOAL_THEN
   `!c. c IN interval[vec 0:real^1,vec 1]
        ==> compact (IMAGE (f:real^((2,2)finite_sum,1)finite_sum->real^3)
                       ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {c})) /\
            connected (IMAGE f ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                                {c})) /\
            ~(IMAGE f ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {c}) =
              {}) /\
            IMAGE f ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {c})
            SUBSET y`
  (LABEL_TAC "lev") THENL
   [X_GEN_TAC `c:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {c:real^1} SUBSET
      (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
      interval[vec 0:real^1,vec 1]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL; SING_SUBSET]; ALL_TAC] THEN
    MP_TAC(SPEC `c:real^1` MOI_S3SH_TT_LEVEL) THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                  interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                  interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
      EXPAND_TAC "y" THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "lev" (MP_TAC o SPEC `vec 0:real^1`) THEN
  USE_THEN "lev" (MP_TAC o SPEC `vec 1:real^1`) THEN
  REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `interior y =
    IMAGE (f:real^((2,2)finite_sum,1)finite_sum->real^3)
      ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
       interval(vec 0:real^1,vec 1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3SH_TSHELL_INTERIOR THEN
    EXISTS_TAC `k:real^3->real^((2,2)finite_sum,1)finite_sum` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a IN (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
               interval[vec 0:real^1,vec 1] /\
          b IN (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
               interval[vec 0:real^1,vec 1] /\
          (f:real^((2,2)finite_sum,1)finite_sum->real^3) a = f b ==> a = b`
  (LABEL_TAC "inj") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_SPHERE; COMPACT_INTERVAL];
    EXPAND_TAC "y" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CONNECTED_PCROSS; CONNECTED_SPHERE; CONNECTED_INTERVAL; DIMINDEX_2; LE_REFL];
    (* disjoint ends *)
    MATCH_MP_TAC(SET_RULE
     `!(f:real^((2,2)finite_sum,1)finite_sum->real^3) d a b.
        (!x y. x IN d /\ y IN d /\ f x = f y ==> x = y) /\
        a SUBSET d /\ b SUBSET d /\ DISJOINT a b
        ==> DISJOINT (IMAGE f a) (IMAGE f b)`) THEN
    EXISTS_TAC `(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                interval[vec 0:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[];
    (* the interior *)
    EXPAND_TAC "y" THEN
    MATCH_MP_TAC(SET_RULE
     `!(f:real^((2,2)finite_sum,1)finite_sum->real^3) d a b.
        (!x y. x IN d /\ y IN d /\ f x = f y ==> x = y) /\
        a SUBSET d /\ b SUBSET d
        ==> IMAGE f (d DIFF (a UNION b)) = IMAGE f d DIFF (IMAGE f a UNION IMAGE f b)`) THEN
    ASM_REWRITE_TAC[];
    (* the shell coordinate *)
    EXISTS_TAC `fstcart o (k:real^3->real^((2,2)finite_sum,1)finite_sum)` THEN
    MP_TAC(ISPECL [`y:real^3->bool`; `f:real^((2,2)finite_sum,1)finite_sum->real^3`;
                   `k:real^3->real^((2,2)finite_sum,1)finite_sum`] MOI_S3SH_TSHELL_COORD) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* 5. A PL 2-sphere in the interior of a toroidal shell does not separate    *)
(* its ends (the theorem SHELL_NO_SPHERE; case (1) of Moise 30.6, p.217, by  *)
(* lifting instead of van Kampen).  Let theta be the first circle coordinate *)
(* of the shell.  The sphere s is simply connected and locally path          *)
(* connected, so theta has a continuous logarithm on s; extend it to real^3  *)
(* (Tietze).  If open u, v split the complement of s with t0 in u and t1 in  *)
(* v, the map psi equal to cexp of the logarithm off v and to theta off u is *)
(* continuous on the shell (closed pieces, equal on s).  The first circle    *)
(* loops of the levels 0 and 1 are homotopic in the shell, but psi sends the *)
(* first to a loop with a logarithm (winding number 0) and the second to the *)
(* standard circle (winding number 1).                                       *)
(* ========================================================================= *)

let MOI_S3SH_PL_SPHERE_FACTS = prove
 (`!s:real^3->bool.
     pl_sphere 2 s ==> compact s /\ simply_connected s /\ locally path_connected s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_P35_PL_SPHERE_HOMEO) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_COMPACTNESS) THEN
    REWRITE_TAC[COMPACT_SPHERE];
    MATCH_MP_TAC(ISPECL [`sphere(vec 0:real^3,&1)`; `s:real^3->bool`]
                        HOMEOMORPHIC_SIMPLY_CONNECTED) THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SIMPLY_CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_3; LE_REFL];
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP HOMEOMORPHIC_LOCAL_PATH_CONNECTEDNESS) THEN
    REWRITE_TAC[LOCALLY_PATH_CONNECTED_SPHERE]]);;

(* The first circle loop at a level c of the model. *)

let MOI_S3SH_LEVEL_LOOP = prove
 (`!c:real^1.
     c IN interval[vec 0,vec 1]
     ==> path (\t. pastecart (pastecart (circlepath(vec 0,&1) t) (Cx(&1))) c) /\
         pathfinish (\t. pastecart (pastecart (circlepath(vec 0,&1) t) (Cx(&1))) c) =
         pathstart (\t. pastecart (pastecart (circlepath(vec 0,&1) t) (Cx(&1))) c) /\
         path_image (\t. pastecart (pastecart (circlepath(vec 0,&1) t) (Cx(&1))) c) SUBSET
         (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {c} /\
         (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {c} SUBSET
         (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
         interval[vec 0,vec 1]`,
  GEN_TAC THEN DISCH_TAC THEN STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX; GSYM path] THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish];
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS; IN_SING] THEN
    UNDISCH_TAC `path_image (circlepath(vec 0,&1)) = sphere(vec 0:real^2,&1)` THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[];
    MATCH_MP_TAC PCROSS_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL; SING_SUBSET]]);;

let MOI_S3SH_LEVELS_HOMOTOPIC = prove
 (`homotopic_loops ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                    interval[vec 0:real^1,vec 1])
     (\t. pastecart (pastecart (circlepath(vec 0,&1) t) (Cx(&1))) (vec 0:real^1))
     (\t. pastecart (pastecart (circlepath(vec 0,&1) t) (Cx(&1))) (vec 1:real^1))`,
  MP_TAC(ISPECL [`sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                 `interval[vec 0:real^1,vec 1]`;
                 `\t:real^1. pastecart (circlepath(vec 0,&1) t) (Cx(&1))`;
                 `linepath(vec 0:real^1,vec 0)`;
                 `\t:real^1. pastecart (circlepath(vec 0,&1) t) (Cx(&1))`;
                 `linepath(vec 1:real^1,vec 1)`] MOI_FH1_HOMOTOPIC_LOOPS_PASTECART) THEN
  REWRITE_TAC[LINEPATH_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[HOMOTOPIC_LOOPS_REFL] THEN STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX; GSYM path] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
      UNDISCH_TAC `path_image (circlepath(vec 0,&1)) = sphere(vec 0:real^2,&1)` THEN
      REWRITE_TAC[path_image] THEN ASM SET_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
      ASM_REWRITE_TAC[pathstart; pathfinish]];
    MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
    REWRITE_TAC[path; pathstart; pathfinish; CONTINUOUS_ON_CONST; SEGMENT_1; DROP_VEC;
                REAL_POS; SUBSET_REFL]]);;

(* A loop with a continuous logarithm has winding number zero. *)

let MOI_S3SH_CEXP_LOOP_WINDING = prove
 (`!l:real^1->complex.
     path l /\ pathfinish l = pathstart l
     ==> winding_number(cexp o l,vec 0) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:real^1->complex`; `(:complex)`] MOI_FH1_CONVEX_NULLHOMOTOPIC) THEN
  ASM_REWRITE_TAC[CONVEX_UNIV; SUBSET_UNIV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `homotopic_loops ((:complex) DELETE vec 0) (cexp o l)
                  (cexp o linepath(pathstart l,pathstart l))` MP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN EXISTS_TAC `(:complex)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_CEXP; SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV] THEN
    REWRITE_TAC[COMPLEX_VEC_0; CEXP_NZ];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP WINDING_NUMBER_HOMOTOPIC_LOOPS) THEN
  REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL] THEN
  MATCH_MP_TAC WINDING_NUMBER_TRIVIAL THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
  MESON_TAC[CEXP_NZ]);;

(* The theorem SHELL_NO_SPHERE. *)

let SHELL_NO_SPHERE = prove
 (MOI_S30_SHELL_NO_SPHERE,
  REWRITE_TAC[toroidal_shell; euclidean_separates] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:real^((2,2)finite_sum,1)finite_sum->real^3`
      (X_CHOOSE_THEN `k:real^3->real^((2,2)finite_sum,1)finite_sum`
        (CONJUNCTS_THEN2 (LABEL_TAC "hom") (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC))))
    (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP MOI_S3SH_PL_SPHERE_FACTS) ASSUME_TAC)) THEN
  STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool`
    (X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC)) THEN
  USE_THEN "hom" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(s:real^3->bool) SUBSET y` ASSUME_TAC THENL
   [MP_TAC(ISPEC `y:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET interior y` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the level loops and their homotopy, before the abbreviations *)
  MP_TAC(SPEC `vec 0:real^1` MOI_S3SH_LEVEL_LOOP) THEN
  MP_TAC(SPEC `vec 1:real^1` MOI_S3SH_LEVEL_LOOP) THEN
  REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC MOI_S3SH_LEVELS_HOMOTOPIC THEN DISCH_TAC THEN
  ABBREV_TAC `c0 = \t. pastecart (pastecart (circlepath(vec 0,&1) t) (Cx(&1)))
                                 (vec 0:real^1)` THEN
  ABBREV_TAC `c1 = \t. pastecart (pastecart (circlepath(vec 0,&1) t) (Cx(&1)))
                                 (vec 1:real^1)` THEN
  (* the circle coordinate *)
  ABBREV_TAC `theta = \x:real^3. fstcart(fstcart
                        ((k:real^3->real^((2,2)finite_sum,1)finite_sum) x))` THEN
  SUBGOAL_THEN
   `(theta:real^3->complex) continuous_on y /\
    (!x. x IN y ==> theta x IN sphere(vec 0:real^2,&1))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "theta" THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(\x:real^3. fstcart(fstcart((k:real^3->real^((2,2)finite_sum,1)finite_sum) x))) =
        (fstcart o fstcart) o k` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN MATCH_MP_TAC LINEAR_COMPOSE THEN
      REWRITE_TAC[LINEAR_FSTCART];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(k:real^3->real^((2,2)finite_sum,1)finite_sum) x IN
        (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
        interval[vec 0:real^1,vec 1]`
      MP_TAC THENL
       [UNDISCH_TAC
         `IMAGE (k:real^3->real^((2,2)finite_sum,1)finite_sum) y =
          (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
          interval[vec 0:real^1,vec 1]` THEN
        UNDISCH_TAC `(x:real^3) IN y` THEN SET_TAC[];
        ALL_TAC] THEN
      SIMP_TAC[MOI_FH1_IN_PCROSS]];
    ALL_TAC] THEN
  (* the logarithm on the sphere and its extension *)
  MP_TAC(ISPECL [`theta:real^3->complex`; `s:real^3->bool`]
                CONTINUOUS_LOGARITHM_ON_SIMPLY_CONNECTED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `y:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(theta:real^3->complex) x IN sphere(vec 0:real^2,&1)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(s:real^3->bool) SUBSET y` THEN UNDISCH_TAC `(x:real^3) IN s` THEN
        SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_SPHERE_0; GSYM COMPLEX_VEC_0] THEN
      MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`]];
    DISCH_THEN(X_CHOOSE_THEN `l:real^3->complex` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`l:real^3->complex`; `(:real^3)`; `s:real^3->bool`] TIETZE_UNBOUNDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    DISCH_THEN(X_CHOOSE_THEN `lt:real^3->complex` STRIP_ASSUME_TAC)] THEN
  (* the pasted map *)
  ABBREV_TAC `psi = \x:real^3. if ~(x IN v) then cexp((lt:real^3->complex) x)
                               else (theta:real^3->complex) x` THEN
  SUBGOAL_THEN `(psi:real^3->complex) continuous_on y` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN
    SUBGOAL_THEN `(y INTER ((:real^3) DIFF v)) UNION (y INTER ((:real^3) DIFF u)) = y`
    ASSUME_TAC THENL [UNDISCH_TAC `DISJOINT (u:real^3->bool) v` THEN SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[SYM th]) THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[GSYM OPEN_CLOSED] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[GSYM OPEN_CLOSED] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(\x:real^3. cexp((lt:real^3->complex) x)) = cexp o lt` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `y:real^3->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN X_GEN_TAC `x:real^3` THEN
      STRIP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `(x:real^3) IN v`)) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^3) IN s` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~((x:real^3) IN u)`; `~((x:real^3) IN v)`;
                               `(u:real^3->bool) UNION v = (:real^3) DIFF s`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->complex) y SUBSET (:complex) DELETE vec 0` ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC[COMPLEX_VEC_0; CEXP_NZ];
      SUBGOAL_THEN `(theta:real^3->complex) x IN sphere(vec 0:real^2,&1)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_SPHERE_0] THEN MESON_TAC[NORM_0; REAL_ARITH `~(&0 = &1)`]];
    ALL_TAC] THEN
  (* the images of the level loops *)
  SUBGOAL_THEN
   `homotopic_loops y ((f:real^((2,2)finite_sum,1)finite_sum->real^3) o c0) (f o c1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                interval[vec 0:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops ((:complex) DELETE vec 0)
      ((psi:real^3->complex) o (f:real^((2,2)finite_sum,1)finite_sum->real^3) o c0)
      (psi o f o c1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN EXISTS_TAC `y:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH o
    check (fun th -> rator(rator(concl th)) = `homotopic_loops (y:real^3->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP o
    check (fun th -> rator(rator(concl th)) = `homotopic_loops (y:real^3->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_PATH o
    check (fun th -> rator(rator(concl th)) =
                     `homotopic_loops ((:complex) DELETE vec 0)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_LOOP o
    check (fun th -> rator(rator(concl th)) =
                     `homotopic_loops ((:complex) DELETE vec 0)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_LOOPS_IMP_SUBSET o
    check (fun th -> rator(rator(concl th)) =
                     `homotopic_loops ((:complex) DELETE vec 0)`)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP WINDING_NUMBER_HOMOTOPIC_LOOPS o
    check (fun th -> rator(rator(concl th)) =
                     `homotopic_loops ((:complex) DELETE vec 0)`)) THEN
  (* the winding number at level 1 *)
  SUBGOAL_THEN
   `winding_number((psi:real^3->complex) o
                   (f:real^((2,2)finite_sum,1)finite_sum->real^3) o c1,vec 0) = Cx(&1)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `winding_number(circlepath(vec 0,&1),vec 0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[MOI_FH1_CIRCLEPATH_FACTS]] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN STRIP_ASSUME_TAC MOI_FH1_CIRCLEPATH_FACTS THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC MOI_FH1_ORIGIN_NOT_IN_CIRCLE THEN SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(c1:real^1->real^((2,2)finite_sum,1)finite_sum) t IN
      (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {vec 1:real^1}`
    ASSUME_TAC THENL
     [UNDISCH_TAC
       `path_image (c1:real^1->real^((2,2)finite_sum,1)finite_sum) SUBSET
        (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {vec 1:real^1}` THEN
      REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(f:real^((2,2)finite_sum,1)finite_sum->real^3)
        ((c1:real^1->real^((2,2)finite_sum,1)finite_sum) t) IN v`
    ASSUME_TAC THENL
     [UNDISCH_TAC
       `IMAGE (f:real^((2,2)finite_sum,1)finite_sum->real^3)
          ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {vec 1:real^1})
        SUBSET v` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(k:real^3->real^((2,2)finite_sum,1)finite_sum)
        ((f:real^((2,2)finite_sum,1)finite_sum->real^3)
          ((c1:real^1->real^((2,2)finite_sum,1)finite_sum) t)) = c1 t`
    ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(SET_RULE
       `!a b x:real^((2,2)finite_sum,1)finite_sum. x IN a /\ a SUBSET b ==> x IN b`) THEN
      EXISTS_TAC `(sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS
                  {vec 1:real^1}` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "theta" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "c1" THEN REWRITE_TAC[FSTCART_PASTECART];
    ALL_TAC] THEN
  (* the winding number at level 0 *)
  SUBGOAL_THEN
   `winding_number((psi:real^3->complex) o
                   (f:real^((2,2)finite_sum,1)finite_sum->real^3) o c0,vec 0) = Cx(&0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `winding_number(cexp o ((lt:real^3->complex) o
                  (f:real^((2,2)finite_sum,1)finite_sum->real^3) o c0),vec 0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(c0:real^1->real^((2,2)finite_sum,1)finite_sum) t IN
        (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {vec 0:real^1}`
      ASSUME_TAC THENL
       [UNDISCH_TAC
         `path_image (c0:real^1->real^((2,2)finite_sum,1)finite_sum) SUBSET
          (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {vec 0:real^1}` THEN
        REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(f:real^((2,2)finite_sum,1)finite_sum->real^3)
          ((c0:real^1->real^((2,2)finite_sum,1)finite_sum) t) IN u`
      ASSUME_TAC THENL
       [UNDISCH_TAC
         `IMAGE (f:real^((2,2)finite_sum,1)finite_sum->real^3)
            ((sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)) PCROSS {vec 0:real^1})
          SUBSET u` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `~((f:real^((2,2)finite_sum,1)finite_sum->real^3)
           ((c0:real^1->real^((2,2)finite_sum,1)finite_sum) t) IN v)`
      ASSUME_TAC THENL
       [UNDISCH_TAC `DISJOINT (u:real^3->bool) v` THEN
        UNDISCH_TAC
         `(f:real^((2,2)finite_sum,1)finite_sum->real^3)
            ((c0:real^1->real^((2,2)finite_sum,1)finite_sum) t) IN u` THEN
        SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[o_THM] THEN EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3SH_CEXP_LOOP_WINDING THEN
      ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
      MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    ALL_TAC] THEN
  REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* 6. The spine of the inner solid torus is essential in the outer one       *)
(* (the theorem SHELL_CORE_ESSENTIAL; Moise p.218).  The toroidal            *)
(* shell collapses s2 onto s1 (MOI_S38_SHELL_LOOPS), so the spine j of s1   *)
(* carries the loops of s2 (MOI_S38_CORE with s := s2).  A contraction of j *)
(* in s2 to a point z would make the spine loop of s2 null-homotopic in s2, *)
(* but its circle coordinate has winding number 1.                          *)
(* ========================================================================= *)

let SHELL_CORE_ESSENTIAL = prove
 (MOI_S30_SHELL_CORE_ESSENTIAL,
  MAP_EVERY X_GEN_TAC [`s1:real^3->bool`; `s2:real^3->bool`; `j:real^3->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(s1:real^3->bool) SUBSET s2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s2:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `loops_carried (j:real^3->bool) s2` MP_TAC THENL
   [MATCH_MP_TAC MOI_S38_CORE THEN
    MAP_EVERY EXISTS_TAC [`s1:real^3->bool`; `s2:real^3->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC MOI_S38_SHELL_LOOPS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[loops_carried] THEN DISCH_THEN(LABEL_TAC "lc") THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` (LABEL_TAC "con")) THEN
  (* the spine loop of s2 *)
  MP_TAC(ISPEC `s2:real^3->bool` MOI_S38_SOLID_TORUS_HOMEO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_TAC `g2:real^3->real^(2,2)finite_sum`)) THEN
  MP_TAC(ISPECL [`s2:real^3->bool`; `f2:real^(2,2)finite_sum->real^3`;
                 `g2:real^3->real^(2,2)finite_sum`; `vec 0:real^2`] MOI_S38_SPINE_LOOP) THEN
  ASM_REWRITE_TAC[CENTRE_IN_CBALL; REAL_POS] THEN STRIP_TAC THEN
  ABBREV_TAC `c2 = (f2:real^(2,2)finite_sum->real^3) o
                   (\t. pastecart (vec 0:real^2) (circlepath(vec 0,&1) t))` THEN
  USE_THEN "lc" (MP_TAC o SPEC `c2:real^1->real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->real^3` STRIP_ASSUME_TAC) THEN
  (* the loop q of j contracts in s2 *)
  SUBGOAL_THEN `homotopic_loops s2 (q:real^1->real^3) (linepath(z,z))` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `homotopic_loops s2 ((\x:real^3. x) o (q:real^1->real^3)) ((\x:real^3. z) o q)`
    MP_TAC THENL
     [REWRITE_TAC[homotopic_loops] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
      EXISTS_TAC `j:real^3->bool` THEN CONJ_TAC THENL
       [MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN EXISTS_TAC `\f:real^3->real^3. T` THEN
        ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE];
        ASM_REWRITE_TAC[GSYM path; GSYM path_image]];
      REWRITE_TAC[o_DEF; ETA_AX; LINEPATH_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN s2` ASSUME_TAC THENL
   [USE_THEN "con" (MP_TAC o CONJUNCT2 o MATCH_MP HOMOTOPIC_WITH_IMP_SUBSET) THEN
    SUBGOAL_THEN `pathstart(q:real^1->real^3) IN j` MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!a b x:real^3. x IN a /\ a SUBSET b ==> x IN b`) THEN
      EXISTS_TAC `path_image (q:real^1->real^3)` THEN
      ASM_REWRITE_TAC[PATHSTART_IN_PATH_IMAGE];
      ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* so the spine loop of s2 is null-homotopic in s2 *)
  SUBGOAL_THEN `homotopic_loops s2 (c2:real^1->real^3) (linepath(z,z))` MP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN EXISTS_TAC `q:real^1->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s2:real^3->bool`; `f2:real^(2,2)finite_sum->real^3`;
                 `g2:real^3->real^(2,2)finite_sum`; `c2:real^1->real^3`;
                 `linepath(z:real^3,z)`] MOI_S38_SOLID_TORUS_HOMOTOPIC_LOOPS_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[MOI_FH1_COMPOSE_LINEPATH_REFL] THEN
  SUBGOAL_THEN `~(vec 0 = sndcart((g2:real^3->real^(2,2)finite_sum) z))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s2:real^3->bool`; `f2:real^(2,2)finite_sum->real^3`;
                   `g2:real^3->real^(2,2)finite_sum`] MOI_S38_SOLID_TORUS_COORD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[IN_IMAGE; o_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[WINDING_NUMBER_TRIVIAL] THEN REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC);;

