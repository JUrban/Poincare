(* ========================================================================= *)
(* pc_moi_s35_deg: the Sec 35 unit s35_deg, main theorems LOCAL_SIGN =       *)
(* MOI_S35_LOCAL_SIGN and CLOSE_SIGN = MOI_S35_CLOSE_SIGN                    *)
(* (pc_moi_s35_stmt.ml, section 7.3): an injective continuous map of a       *)
(* connected open set of real^3 has the same orientation at all points      *)
(* where it is locally affine, and two such maps close to each other, the   *)
(* first covering a ball three times their distance, have the same          *)
(* orientation.  Method: local sphere maps u -> f(z + rho u/|u|) - f(z) in  *)
(* real^3 minus 0; their homotopy class does not depend on rho (straight    *)
(* line in the punctured domain), is locally constant in z (closeness on    *)
(* the sphere, uniform continuity), and at a locally affine point is the    *)
(* class of the linear part (positive multiples), so HOMOTOPIC_LINEAR_MAPS_ *)
(* ALT of degree.ml compares determinants; for two close maps g o f^-1 is    *)
(* close to the identity on a ball (INVARIANCE_OF_DOMAIN_HOMEOMORPHISM).     *)
(* The orientation input missing from Moise GTM 47, p.251.                  *)
(* ========================================================================= *)

needs "src/pc_moi_s35_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Straight-line homotopies into real^N minus 0, and the local sphere    *)
(* maps of a map of real^3.                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S5G_SEG_CLOSE = prove
 (`!x y:real^N. norm(x - y) < norm x ==> ~(vec 0 IN segment[x,y])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IN_SEGMENT; NOT_EXISTS_THM] THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `x:real^N = u % (x - y)` ASSUME_TAC THENL
   [UNDISCH_TAC `vec 0:real^N = (&1 - u) % x + u % y` THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(x:real^N) = u * norm(x - y:real^N)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 <= u ==> abs u = u`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`u:real`; `&1`; `norm(x - y:real^N)`] REAL_LE_RMUL) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC);;

let MOI_S5G_SEG_POS = prove
 (`!(x:real^N) c. ~(x = vec 0) /\ &0 < c ==> ~(vec 0 IN segment[x,c % x])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT; NOT_EXISTS_THM] THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `((&1 - u) + u * c) % (x:real^N) = vec 0` MP_TAC THENL
   [UNDISCH_TAC `vec 0:real^N = (&1 - u) % x + u % c % x` THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_CASES_TAC `u = &1` THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`u:real`; `c:real`] REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC]);;

let MOI_S5G_HOMOTOPIC_CLOSE = prove
 (`!(f:real^M->real^N) g s.
     f continuous_on s /\ g continuous_on s /\
     (!x. x IN s ==> norm(f x - g x) < norm(f x))
     ==> homotopic_with (\z. T)
           (subtopology euclidean s,subtopology euclidean ((:real^N) DELETE vec 0))
           f g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
  ASM_REWRITE_TAC[SET_RULE `t SUBSET (:real^N) DELETE a <=> ~(a IN t)`] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S5G_SEG_CLOSE THEN
  ASM_SIMP_TAC[]);;

let MOI_S5G_HOMOTOPIC_POSMUL = prove
 (`!(f:real^M->real^N) g s.
     f continuous_on s /\ g continuous_on s /\
     (!x. x IN s ==> ~(f x = vec 0) /\ ?c. &0 < c /\ g x = c % f x)
     ==> homotopic_with (\z. T)
           (subtopology euclidean s,subtopology euclidean ((:real^N) DELETE vec 0))
           f g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN
  ASM_REWRITE_TAC[SET_RULE `t SUBSET (:real^N) DELETE a <=> ~(a IN t)`] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5G_SEG_POS THEN ASM_REWRITE_TAC[]);;

(* The local sphere map of f at z of radius rho, on real^3 minus 0.        *)

let moi_s5g_sph = new_definition
 `moi_s5g_sph (f:real^3->real^3) (z:real^3) (rho:real) (u:real^3) =
    f(z + (rho / norm u) % u) - f z`;;

let MOI_S5G_NORM_RADIAL = prove
 (`!rho (u:real^N). &0 <= rho /\ ~(u = vec 0) ==> norm((rho / norm u) % u) = rho`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL; NORM_EQ_0;
               REAL_ARITH `&0 <= rho ==> abs rho = rho`]);;

let MOI_S5G_RADIAL_CONTINUOUS = prove
 (`!(z:real^N) rho.
     (\u. z + (rho / norm u) % u) continuous_on ((:real^N) DELETE vec 0)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
  SUBGOAL_THEN `(lift o (\u:real^N. rho / norm u)) = (\u. rho % (lift o inv o norm) u)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; real_div; LIFT_CMUL]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUS_ON_INV THEN
  REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM; IN_DELETE; IN_UNIV; NORM_EQ_0]);;

let MOI_S5G_RADIAL_IN_CBALL = prove
 (`!(z:real^N) rho u.
     &0 <= rho /\ ~(u = vec 0) ==> z + (rho / norm u) % u IN cball(z,rho)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_CBALL; NORM_ARITH `dist(z:real^N,z + v) = norm v`] THEN
  ASM_SIMP_TAC[MOI_S5G_NORM_RADIAL; REAL_LE_REFL]);;

let MOI_S5G_SPH_CONTINUOUS = prove
 (`!(f:real^3->real^3) s z rho.
     f continuous_on s /\ &0 < rho /\ cball(z,rho) SUBSET s
     ==> (moi_s5g_sph f z rho) continuous_on ((:real^3) DELETE vec 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_s5g_sph (f:real^3->real^3) z rho =
                (\v. f v - f z) o (\u. z + (rho / norm u) % u)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; moi_s5g_sph]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  REWRITE_TAC[MOI_S5G_RADIAL_CONTINUOUS] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^3->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV] THEN
  X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  MATCH_MP_TAC MOI_S5G_RADIAL_IN_CBALL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let MOI_S5G_SPH_NONZERO = prove
 (`!(f:real^3->real^3) s z rho.
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     &0 < rho /\ cball(z,rho) SUBSET s
     ==> IMAGE (moi_s5g_sph f z rho) ((:real^3) DELETE vec 0) SUBSET
         ((:real^3) DELETE vec 0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV; moi_s5g_sph] THEN
  X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[VECTOR_SUB_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `z + (rho / norm u) % u = z:real^3` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[MOI_S5G_RADIAL_IN_CBALL; REAL_LT_IMP_LE; CENTRE_IN_CBALL];
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `z + v:real^3 = z <=> v = vec 0`; VECTOR_MUL_EQ_0] THEN
  ASM_SIMP_TAC[REAL_DIV_EQ_0; NORM_EQ_0; REAL_LT_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* 2. The class of the local sphere maps: independent of the radius, locally *)
(* constant in the centre, hence constant on a connected open set; at a     *)
(* locally affine point it is the class of the linear part.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S5G_SPH_ALT = prove
 (`!(f:real^3->real^3) z rho.
     moi_s5g_sph f z rho = \u. f(z + (rho / norm u) % u) - f z`,
  REWRITE_TAC[FUN_EQ_THM; moi_s5g_sph]);;

let MOI_S5G_COMPOSE = prove
 (`!(k:real^3->real^3) W p (a:real^M->real^3) b X.
     k continuous_on W /\ p IN W /\ (!x. x IN W /\ k x = k p ==> x = p) /\
     homotopic_with (\h. T)
       (subtopology euclidean X,subtopology euclidean (W DELETE p)) a b
     ==> homotopic_with (\h. T)
           (subtopology euclidean X,subtopology euclidean ((:real^3) DELETE vec 0))
           (\u. k(a u) - k p) (\u. k(b u) - k p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^M->real^3`; `b:real^M->real^3`;
                 `\x:real^3. (k:real^3->real^3) x - k p`; `X:real^M->bool`;
                 `(W:real^3->bool) DELETE p`; `(:real^3) DELETE vec 0`]
    HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT) THEN
  REWRITE_TAC[o_DEF] THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `W:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV; VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[]]);;

let MOI_S5G_SEG_RADIAL = prove
 (`!(z:real^N) r1 r2 u.
     &0 < r1 /\ &0 < r2 /\ ~(u = vec 0)
     ==> segment[z + (r1 / norm u) % u,z + (r2 / norm u) % u] SUBSET
         cball(z,max r1 r2) DELETE z`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `(s:real^N->bool) SUBSET t DELETE a <=> s SUBSET t /\ ~(a IN s)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_CBALL] THEN
    REWRITE_TAC[CBALL_MAX_UNION; IN_UNION] THEN
    ASM_SIMP_TAC[MOI_S5G_RADIAL_IN_CBALL; REAL_LT_IMP_LE];
    REWRITE_TAC[IN_SEGMENT; NOT_EXISTS_THM] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(((&1 - t) * r1 + t * r2) / norm(u:real^N)) % u = vec 0` MP_TAC THENL
     [UNDISCH_TAC `z:real^N = (&1 - t) % (z + (r1 / norm u) % u) +
                              t % (z + (r2 / norm u) % u)` THEN
      REWRITE_TAC[real_div] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_DIV_EQ_0; NORM_EQ_0] THEN
    ASM_CASES_TAC `t = &0` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`&1 - t`; `r1:real`] REAL_LE_MUL) THEN
      MP_TAC(SPECL [`t:real`; `r2:real`] REAL_LT_MUL) THEN ASM_REAL_ARITH_TAC]]);;

let MOI_S5G_SPH_RADIUS = prove
 (`!(f:real^3->real^3) s z rho1 rho2.
     f continuous_on s /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     &0 < rho1 /\ &0 < rho2 /\ cball(z,rho1) SUBSET s /\ cball(z,rho2) SUBSET s
     ==> homotopic_with (\h. T)
           (subtopology euclidean ((:real^3) DELETE vec 0),
            subtopology euclidean ((:real^3) DELETE vec 0))
           (moi_s5g_sph f z rho1) (moi_s5g_sph f z rho2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `cball(z:real^3,rho1) SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_S5G_SPH_ALT] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`; `z:real^3`;
                 `\u:real^3. z + (rho1 / norm u) % u`;
                 `\u:real^3. z + (rho2 / norm u) % u`; `(:real^3) DELETE vec 0`]
    MOI_S5G_COMPOSE) THEN
  BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN REWRITE_TAC[MOI_S5G_RADIAL_CONTINUOUS] THEN
  X_GEN_TAC `u:real^3` THEN REWRITE_TAC[IN_DELETE; IN_UNIV] THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z:real^3,max rho1 rho2) DELETE z` THEN
  ASM_SIMP_TAC[MOI_S5G_SEG_RADIAL] THEN REWRITE_TAC[CBALL_MAX_UNION] THEN
  UNDISCH_TAC `cball(z:real^3,rho1) SUBSET s` THEN
  UNDISCH_TAC `cball(z:real^3,rho2) SUBSET s` THEN SET_TAC[]);;

(* Local constancy in the centre: on the sphere of radius R about z the     *)
(* values stay at least d away from 0, and moving the centre by less than   *)
(* the uniform-continuity modulus for d/2 moves the values by less than d.  *)

let MOI_S5G_SPH_NEAR = prove
 (`!(f:real^3->real^3) s z.
     open s /\ f continuous_on s /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\ z IN s
     ==> ?R e. &0 < R /\ cball(z,R) SUBSET s /\ &0 < e /\
               !z'. dist(z,z') < e
                    ==> cball(z',R) SUBSET s /\
                        homotopic_with (\h. T)
                          (subtopology euclidean ((:real^3) DELETE vec 0),
                           subtopology euclidean ((:real^3) DELETE vec 0))
                          (moi_s5g_sph f z R) (moi_s5g_sph f z' R)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `z:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `R = e0 / &2` THEN
  SUBGOAL_THEN `&0 < R /\ cball(z:real^3,&2 * R) SUBSET s /\ cball(z,R) SUBSET s`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[REAL_ARITH `&2 * e0 / &2 = e0`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z:real^3,e0)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^3. norm((f:real^3->real^3) x - f z)`; `sphere(z:real^3,R)`]
    CONTINUOUS_ATTAINS_INF) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_SPHERE; SPHERE_EQ_EMPTY] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(z:real^3,R)` THEN ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d = norm((f:real^3->real^3) x1 - f z)` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `x1:real^3 = z` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `(f:real^3->real^3) x = f y`))
                                   (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `cball(z:real^3,R) SUBSET s` THEN
      UNDISCH_TAC `(x1:real^3) IN sphere(z,R)` THEN
      MP_TAC(ISPECL [`z:real^3`; `R:real`] SPHERE_SUBSET_CBALL) THEN SET_TAC[];
      UNDISCH_TAC `(x1:real^3) IN sphere(z,R)` THEN
      REWRITE_TAC[IN_SPHERE] THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `dist(z:real^3,z) = R` THEN REWRITE_TAC[DIST_REFL] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `cball(z:real^3,&2 * R)`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_CBALL] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `d / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`R:real`; `min eta R`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  X_GEN_TAC `z':real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `cball(z':real^3,R) SUBSET cball(z,&2 * R)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL] THEN X_GEN_TAC `y:real^3` THEN
    UNDISCH_TAC `dist(z:real^3,z') < min eta R` THEN
    REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(z':real^3,R) SUBSET s` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(z:real^3,&2 * R)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S5G_HOMOTOPIC_CLOSE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5G_SPH_CONTINUOUS THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S5G_SPH_CONTINUOUS THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:real^3` THEN REWRITE_TAC[IN_DELETE; IN_UNIV] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s5g_sph] THEN
  SUBGOAL_THEN `norm((R / norm u) % (u:real^3)) = R` MP_TAC THENL
   [MATCH_MP_TAC MOI_S5G_NORM_RADIAL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `w = (R / norm u) % (u:real^3)` THEN DISCH_TAC THEN
  ABBREV_TAC `p = z + w:real^3` THEN ABBREV_TAC `p' = z' + w:real^3` THEN
  SUBGOAL_THEN `(p:real^3) IN sphere(z,R) /\ p IN cball(z,&2 * R) /\
                (p':real^3) IN cball(z,&2 * R) /\ dist(p',p) = dist(z',z) /\
                z IN cball(z,&2 * R) /\ z' IN cball(z,&2 * R)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "p'"] THEN
    REWRITE_TAC[IN_SPHERE; IN_CBALL] THEN
    UNDISCH_TAC `dist(z:real^3,z') < min eta R` THEN
    REWRITE_TAC[REAL_LT_MIN] THEN UNDISCH_TAC `&0 < R` THEN
    UNDISCH_TAC `norm(w:real^3) = R` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `d <= norm((f:real^3->real^3) p - f z)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `sphere(z:real^3,R)`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist((f:real^3->real^3) p',f p) < d / &2 /\ dist(f z',f z) < d / &2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(z:real^3,z') < min eta R` THEN
    REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  UNDISCH_TAC `dist((f:real^3->real^3) p',f p) < d / &2` THEN
  UNDISCH_TAC `dist((f:real^3->real^3) z',f z) < d / &2` THEN
  UNDISCH_TAC `d <= norm((f:real^3->real^3) p - f z)` THEN
  REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH);;

(* The class is the same at all points of a connected open set, for all     *)
(* admissible radii (CONNECTED_EQUIVALENCE_RELATION).                        *)

let MOI_S5G_SPH_CONNECTED = prove
 (`!(f:real^3->real^3) s.
     open s /\ connected s /\ f continuous_on s /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
     ==> !x y rho rho'.
           x IN s /\ y IN s /\ &0 < rho /\ cball(x,rho) SUBSET s /\
           &0 < rho' /\ cball(y,rho') SUBSET s
           ==> homotopic_with (\h. T)
                 (subtopology euclidean ((:real^3) DELETE vec 0),
                  subtopology euclidean ((:real^3) DELETE vec 0))
                 (moi_s5g_sph f x rho) (moi_s5g_sph f y rho')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x y:real^3. x IN s /\ y IN s /\
                  !rho rho'. &0 < rho /\ cball(x,rho) SUBSET s /\
                             &0 < rho' /\ cball(y,rho') SUBSET s
                             ==> homotopic_with (\h. T)
                                   (subtopology euclidean ((:real^3) DELETE vec 0),
                                    subtopology euclidean ((:real^3) DELETE vec 0))
                                   (moi_s5g_sph (f:real^3->real^3) x rho)
                                   (moi_s5g_sph f y rho')`;
    `s:real^3->bool`] CONNECTED_EQUIVALENCE_RELATION) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "r"))) THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`rho:real`; `rho':real`] THEN
      STRIP_TAC THEN ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN
      USE_THEN "r" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `w:real^3`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r1")))
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2")))) THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`rho:real`; `rho'':real`] THEN
      STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
      EXISTS_TAC `moi_s5g_sph (f:real^3->real^3) y e` THEN CONJ_TAC THENL
       [USE_THEN "r1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "r2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      X_GEN_TAC `a:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`; `a:real^3`]
        MOI_S5G_SPH_NEAR) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `R:real` (X_CHOOSE_THEN `e:real`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near")))))) THEN
      EXISTS_TAC `s INTER ball(a:real^3,e)` THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
        ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
        ALL_TAC] THEN
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`rho:real`; `rho':real`] THEN
      STRIP_TAC THEN
      USE_THEN "near" (MP_TAC o C MATCH_MP (ASSUME `dist(a:real^3,x) < e`)) THEN
      STRIP_TAC THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
      EXISTS_TAC `moi_s5g_sph (f:real^3->real^3) a R` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5G_SPH_RADIUS THEN EXISTS_TAC `s:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
      EXISTS_TAC `moi_s5g_sph (f:real^3->real^3) x R` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_S5G_SPH_RADIUS THEN EXISTS_TAC `s:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `y:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* At a locally affine point the sphere maps are positive multiples of the  *)
(* linear part, which is injective.                                         *)

let MOI_S5G_LIN_SPH = prove
 (`!(f:real^3->real^3) s x m.
     open s /\ x IN s /\ f continuous_on s /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\ moi_s35_lin_at f x m
     ==> linear m /\
         ?rho. &0 < rho /\ cball(x,rho) SUBSET s /\
               homotopic_with (\h. T)
                 (subtopology euclidean ((:real^3) DELETE vec 0),
                  subtopology euclidean ((:real^3) DELETE vec 0))
                 m (moi_s5g_sph f x rho)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s35_lin_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real`
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aff")))))))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < min (r / &2) e /\ cball(x:real^3,min (r / &2) e) SUBSET s /\
                cball(x,min (r / &2) e) SUBSET ball(x,r)` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x:real^3,e)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN GEN_TAC THEN
      UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `rho = min (r / &2) e` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN cball(x,rho) ==> f y = f x + (m:real^3->real^3) (y - x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "aff" MATCH_MP_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. ~(v = vec 0) ==> ~((m:real^3->real^3) v = vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `x + (rho / norm v) % (v:real^3) IN cball(x,rho)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S5G_RADIAL_IN_CBALL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `x + (rho / norm v) % (v:real^3) = x` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[VECTOR_ARITH `(x + v) - x:real^3 = v`] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID];
      REWRITE_TAC[VECTOR_ARITH `x + v:real^3 = x <=> v = vec 0`; VECTOR_MUL_EQ_0] THEN
      ASM_SIMP_TAC[REAL_DIV_EQ_0; NORM_EQ_0; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S5G_HOMOTOPIC_POSMUL THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
    MATCH_MP_TAC MOI_S5G_SPH_CONTINUOUS THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:real^3` THEN REWRITE_TAC[IN_DELETE; IN_UNIV] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN EXISTS_TAC `rho / norm(u:real^3)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; moi_s5g_sph] THEN
  SUBGOAL_THEN `x + (rho / norm u) % (u:real^3) IN cball(x,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5G_RADIAL_IN_CBALL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[VECTOR_ARITH `(x + v) - x:real^3 = v`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 3. The theorem LOCAL_SIGN.                                                 *)
(* ------------------------------------------------------------------------- *)

let LOCAL_SIGN = prove
 (MOI_S35_LOCAL_SIGN,
  MAP_EVERY X_GEN_TAC [`f:real^3->real^3`; `s:real^3->bool`; `x:real^3`; `y:real^3`;
                       `m:real^3->real^3`; `m':real^3->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`; `x:real^3`; `m:real^3->real^3`]
    MOI_S5G_LIN_SPH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`; `y:real^3`; `m':real^3->real^3`]
    MOI_S5G_LIN_SPH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `rho':real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`] MOI_S5G_SPH_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `y:real^3`; `rho:real`; `rho':real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_LINEAR_MAPS_ALT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `moi_s5g_sph (f:real^3->real^3) x rho` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `moi_s5g_sph (f:real^3->real^3) y rho'` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. Two close maps: with h = g o f^-1 on the ball B of radius 3r about     *)
(* y0 = f x0, the map w -> h(y0 + w) - h(y0) on B - y0 minus 0 is homotopic *)
(* to the inclusion (push to the sphere of radius 5r/2, where h is within   *)
(* 2r of the identity), and precomposing with a small sphere map of f at x0 *)
(* gives the sphere map of g at x0.  Then the theorem CLOSE_SIGN.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S5G_RADIAL0_CONTINUOUS = prove
 (`!rho. (\u:real^N. (rho / norm u) % u) continuous_on ((:real^N) DELETE vec 0)`,
  GEN_TAC THEN MP_TAC(ISPECL [`vec 0:real^N`; `rho:real`] MOI_S5G_RADIAL_CONTINUOUS) THEN
  REWRITE_TAC[VECTOR_ADD_LID]);;

let MOI_S5G_CLOSE_SPH = prove
 (`!(f:real^3->real^3) g s y0 r x0.
     open s /\ f continuous_on s /\ g continuous_on s /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\
     (!x. x IN s ==> dist(f x,g x) < r) /\
     cball(y0,&3 * r) SUBSET IMAGE f s /\ x0 IN s /\ f x0 = y0
     ==> ?rho. &0 < rho /\ cball(x0,rho) SUBSET s /\
               homotopic_with (\h. T)
                 (subtopology euclidean ((:real^3) DELETE vec 0),
                  subtopology euclidean ((:real^3) DELETE vec 0))
                 (moi_s5g_sph f x0 rho) (moi_s5g_sph g x0 rho)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fi")
      (CONJUNCTS_THEN2 (LABEL_TAC "gi") (CONJUNCTS_THEN2 (LABEL_TAC "cl")
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [USE_THEN "cl" (MP_TAC o C MATCH_MP (ASSUME `(x0:real^3) IN s`)) THEN
    MP_TAC(ISPECL [`(f:real^3->real^3) x0`; `(g:real^3->real^3) x0`] DIST_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`]
    INVARIANCE_OF_DOMAIN_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `fi:real^3->real^3` MP_TAC) THEN
  REWRITE_TAC[homeomorphism] THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y0:real^3) IN cball(y0,&3 * r)` ASSUME_TAC THENL
   [REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN cball(y0,&3 * r)
               ==> (fi:real^3->real^3) w IN s /\ (f:real^3->real^3) (fi w) = w`
  (LABEL_TAC "fif") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN IMAGE (f:real^3->real^3) s` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\w:real^3. (g:real^3->real^3) (fi w)) continuous_on cball(y0,&3 * r)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\w:real^3. (g:real^3->real^3) (fi w)) = g o fi` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (f:real^3->real^3) s` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN cball(y0:real^3,&3 * r) /\ (g:real^3->real^3) (fi w) = g (fi y0) ==> w = y0`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    USE_THEN "fif" (MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN cball(y0,&3 * r)`)) THEN
    USE_THEN "fif" (MP_TAC o C MATCH_MP (ASSUME `(y0:real^3) IN cball(y0,&3 * r)`)) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(fi:real^3->real^3) w = fi y0` MP_TAC THENL
     [USE_THEN "gi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `f:real^3->real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN cball(y0:real^3,&3 * r) ==> norm((g:real^3->real^3) (fi w) - w) < r`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "fif" (MP_TAC o C MATCH_MP (ASSUME `(w:real^3) IN cball(y0,&3 * r)`)) THEN
    STRIP_TAC THEN
    USE_THEN "cl" (MP_TAC o C MATCH_MP (ASSUME `(fi:real^3->real^3) w IN s`)) THEN
    ASM_REWRITE_TAC[dist] THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  ABBREV_TAC `c = &5 / &2 * r` THEN
  SUBGOAL_THEN `&2 * r < c /\ c <= &3 * r /\ &0 < c` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_with (\h. T)
      (subtopology euclidean (cball(vec 0,&3 * r) DELETE vec 0),
       subtopology euclidean ((:real^3) DELETE vec 0))
      (\w. (g:real^3->real^3) (fi(y0 + w)) - g(fi y0)) (\w. w)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
    EXISTS_TAC `\w:real^3. (g:real^3->real^3) (fi(y0 + (c / norm w) % w)) - g(fi y0)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\w:real^3. (g:real^3->real^3) (fi w)`; `cball(y0:real^3,&3 * r)`;
                     `y0:real^3`; `\w:real^3. y0 + w`;
                     `\w:real^3. y0 + (c / norm w) % w`;
                     `cball(vec 0:real^3,&3 * r) DELETE vec 0`] MOI_S5G_COMPOSE) THEN
      BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
        REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        REWRITE_TAC[MOI_S5G_RADIAL_CONTINUOUS] THEN SET_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_DELETE; IN_CBALL_0] THEN STRIP_TAC THEN
      SUBGOAL_THEN `y0 + w:real^3 = y0 + (norm w / norm w) % w` SUBST1_TAC THENL
       [SUBGOAL_THEN `norm(w:real^3) / norm w = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
        MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REWRITE_TAC[NORM_EQ_0];
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(y0:real^3,max (norm(w:real^3)) c) DELETE y0` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S5G_SEG_RADIAL THEN ASM_REWRITE_TAC[NORM_POS_LT];
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DELETE (a:real^3) SUBSET t DELETE a`) THEN
        MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
    EXISTS_TAC `\w:real^3. (c / norm w) % w` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN MATCH_MP_TAC MOI_S5G_HOMOTOPIC_CLOSE THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        REWRITE_TAC[MOI_S5G_RADIAL0_CONTINUOUS] THEN SET_TAC[];
        SUBGOAL_THEN
         `(\w:real^3. (g:real^3->real^3) (fi (y0 + (c / norm w) % w)) - g (fi y0)) =
          (\v. g (fi v) - g (fi y0)) o (\w. y0 + (c / norm w) % w)`
        SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
          REWRITE_TAC[MOI_S5G_RADIAL_CONTINUOUS] THEN SET_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(y0:real^3,&3 * r)` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_CBALL_0] THEN
        X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`y0:real^3`; `c:real`; `&3 * r`] SUBSET_CBALL) THEN
        ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC MOI_S5G_RADIAL_IN_CBALL THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_DELETE; IN_CBALL_0] THEN STRIP_TAC THEN
      SUBGOAL_THEN `y0 + (c / norm w) % (w:real^3) IN cball(y0,&3 * r) /\
                    norm((c / norm w) % (w:real^3)) = c`
      MP_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPECL [`y0:real^3`; `c:real`; `&3 * r`] SUBSET_CBALL) THEN
          ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
          MATCH_MP_TAC MOI_S5G_RADIAL_IN_CBALL THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC MOI_S5G_NORM_RADIAL THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ABBREV_TAC `v = (c / norm w) % (w:real^3)` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `y0 + v:real^3 IN cball(y0,&3 * r)`) o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `r:real`)) (concl th) &&
                         can (find_term ((=) `norm:real^3->real`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(y0:real^3) IN cball(y0,&3 * r)`) o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `r:real`)) (concl th) &&
                         can (find_term ((=) `norm:real^3->real`)) (concl th))) THEN
      UNDISCH_TAC `norm(v:real^3) = c` THEN UNDISCH_TAC `&2 * r < c` THEN
      CONV_TAC NORM_ARITH;
      ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN MATCH_MP_TAC MOI_S5G_HOMOTOPIC_POSMUL THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[CONTINUOUS_ON_ID];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
        REWRITE_TAC[MOI_S5G_RADIAL0_CONTINUOUS] THEN SET_TAC[];
        X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `c / norm(w:real^3)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
        ASM_REWRITE_TAC[NORM_POS_LT]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(fi:real^3->real^3) y0 = x0` ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^3->real^3) x0 = y0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(ASSUME
      `!x. x IN s ==> (fi:real^3->real^3) ((f:real^3->real^3) x) = x`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?rho. &0 < rho /\ cball(x0:real^3,rho) SUBSET s /\
          !x. x IN cball(x0,rho) ==> dist((f:real^3->real^3) x,y0) < &3 * r`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`]
      CONTINUOUS_ON_EQ_CONTINUOUS_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x0:real^3`) THEN
    ASM_REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `&3 * r`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `x0:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min (d / &2) e0` THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(x0:real^3,e0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CBALL THEN REAL_ARITH_TAC;
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (moi_s5g_sph (f:real^3->real^3) x0 rho) ((:real^3) DELETE vec 0) SUBSET
    cball(vec 0,&3 * r) DELETE vec 0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`; `x0:real^3`; `rho:real`]
      MOI_S5G_SPH_NONZERO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV; IN_CBALL_0] THEN
    DISCH_TAC THEN X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[moi_s5g_sph] THEN ASM_REWRITE_TAC[GSYM dist] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC MOI_S5G_RADIAL_IN_CBALL THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\w:real^3. (g:real^3->real^3) (fi(y0 + w)) - g(fi y0)`;
                 `\w:real^3. w`; `moi_s5g_sph (f:real^3->real^3) x0 rho`;
                 `(:real^3) DELETE vec 0`; `cball(vec 0:real^3,&3 * r) DELETE vec 0`;
                 `(:real^3) DELETE vec 0`] HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5G_SPH_CONTINUOUS THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w:real^3. (g:real^3->real^3) (fi(y0 + w)) - g(fi y0)) o
    moi_s5g_sph (f:real^3->real^3) x0 rho = moi_s5g_sph g x0 rho /\
    (\w:real^3. w) o moi_s5g_sph f x0 rho = moi_s5g_sph f x0 rho`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[FUN_EQ_THM; o_THM] THEN BETA_TAC THEN REWRITE_TAC[]] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; moi_s5g_sph] THEN BETA_TAC THEN
    X_GEN_TAC `u:real^3` THEN ASM_CASES_TAC `u:real^3 = vec 0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; VECTOR_SUB_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `x0 + (rho / norm u) % (u:real^3) IN s` ASSUME_TAC THENL
     [UNDISCH_TAC `cball(x0:real^3,rho) SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MOI_S5G_RADIAL_IN_CBALL THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(fi:real^3->real^3) ((f:real^3->real^3) (x0 + (rho / norm u) % u)) =
                  x0 + (rho / norm u) % u` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME
        `!x. x IN s ==> (fi:real^3->real^3) ((f:real^3->real^3) x) = x`) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[VECTOR_ARITH `y0 + (q - y0):real^3 = q`]];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN ASM_REWRITE_TAC[]);;

let CLOSE_SIGN = prove
 (MOI_S35_CLOSE_SIGN,
  MAP_EVERY X_GEN_TAC [`f:real^3->real^3`; `g:real^3->real^3`; `s:real^3->bool`;
                       `y0:real^3`; `r:real`] THEN
  STRIP_TAC THEN REWRITE_TAC[moi_s35_same_orient] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `m:real^3->real^3`; `m':real^3->real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?x0:real^3. x0 IN s /\ (f:real^3->real^3) x0 = y0` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &3 * r` ASSUME_TAC THENL
     [MP_TAC(MATCH_MP (ASSUME `!x. x IN s ==> dist((f:real^3->real^3) x,g x) < r`)
        (ASSUME `(x:real^3) IN s`)) THEN
      MP_TAC(ISPECL [`(f:real^3->real^3) x`; `(g:real^3->real^3) x`] DIST_POS_LE) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`y0:real^3`; `&3 * r`] CENTRE_IN_CBALL) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cball(y0:real^3,&3 * r) SUBSET IMAGE (f:real^3->real^3) s` THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `s:real^3->bool`; `y0:real^3`;
                 `r:real`; `x0:real^3`] MOI_S5G_CLOSE_SPH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`; `x:real^3`; `m:real^3->real^3`]
    MOI_S5G_LIN_SPH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `rho1:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `s:real^3->bool`; `y:real^3`; `m':real^3->real^3`]
    MOI_S5G_LIN_SPH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `rho2:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `s:real^3->bool`] MOI_S5G_SPH_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `x0:real^3`; `rho1:real`; `rho:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `s:real^3->bool`] MOI_S5G_SPH_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`x0:real^3`; `y:real^3`; `rho:real`; `rho2:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_LINEAR_MAPS_ALT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `moi_s5g_sph (f:real^3->real^3) x rho1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `moi_s5g_sph (f:real^3->real^3) x0 rho` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `moi_s5g_sph (g:real^3->real^3) x0 rho` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN
  EXISTS_TAC `moi_s5g_sph (g:real^3->real^3) y rho2` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_WITH_SYM] THEN ASM_REWRITE_TAC[]);;

