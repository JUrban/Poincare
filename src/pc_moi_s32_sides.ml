needs "src/pc_moi_s32_gfacts.ml";;
needs "src/pc_moi_cone_sides.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_comb.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s32_sides: Moise GTM 47, Theorem 32.2 (pp.227-228), the two sides *)
(* of the pseudo-cell P = chain UNION g(rim) in the model B = g(cyl).        *)
(* Main theorem SIDES : |- MOI_S32_SIDES of pc_moi_s3032_stmt.ml.  Route:   *)
(*   1. Jordan curve theorem on a round 2-sphere; the two sides of a cone   *)
(*      over a simple closed curve on a small sphere (both in the separate  *)
(*      file pc_moi_cone_sides, MOI_CSD_SPHERE_JORDAN, MOI_CSD_CONE_SIDES).  *)
(*   2. A PL homeomorphic image of a planar compact set is, near the image  *)
(*      of an interior point, a cone over a simple closed curve (the PL map *)
(*      is radially affine there).                                           *)
(*   3. Two PL annuli glued along a common end form one PL annulus with the *)
(*      common end inside (cone extension of pc_moi_cone).                  *)
(*   4. Near each point Q of the chain minus the centre, P is one annulus or *)
(*      two glued annuli (local finiteness of the tower), so Q has two      *)
(*      local sides.                                                         *)
(*   5. The sets U UNION g(lower hemisphere) and V UNION g(upper hemisphere) *)
(*      separate B DIFF P (U, V from the chain separation).                  *)
(*   6. Every component of B DIFF P has the chain in its closure; at one    *)
(*      point the two local sides bound the number of components by two.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 2. Near the image of an interior point w, a PL homeomorphic image of a   *)
(* planar compact set is a cone over a simple closed curve on a small       *)
(* sphere: the PL map is radially affine at w (MOI_CMB_PL_LOCALLY_CONIC),   *)
(* and the radial projection of the image of a small circle around w is    *)
(* the curve.                                                               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SS_RAY_INJ = prove
 (`!(x:real^2->bool) (f:real^2->real^3) w e t0 z1 z2 l.
     (!z l. z IN x /\ dist(w,z) < e /\ &0 <= l /\ l <= &1
            ==> w + l % (z - w) IN x /\ f(w + l % (z - w)) = f w + l % (f z - f w)) /\
     (!a b. a IN x /\ b IN x /\ f a = f b ==> a = b) /\
     &0 < t0 /\ t0 < e /\ z1 IN x /\ z2 IN x /\ dist(w,z1) = t0 /\ dist(w,z2) = t0 /\
     &0 <= l /\ l <= &1 /\ f z1 - f w = l % (f z2 - f w)
     ==> z1 = z2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`z2:real^2`; `l:real`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `w + l % (z2 - w):real^2 = z1` ASSUME_TAC THENL
   [UNDISCH_TAC `!a b. a IN x /\ b IN x /\ (f:real^2->real^3) a = f b ==> a = b` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(f:real^2->real^3) z1 - f w = l % (f z2 - f w)` THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `z1:real^2`)) THEN
  SUBGOAL_THEN `l = &1` SUBST1_TAC THENL
   [UNDISCH_TAC `dist(w:real^2,w + l % (z2 - w)) = t0` THEN
    REWRITE_TAC[NORM_ARITH `dist(w:real^2,w + y) = norm y`; NORM_MUL] THEN
    SUBGOAL_THEN `norm(z2 - w:real^2) = t0` SUBST1_TAC THENL
     [ASM_MESON_TAC[dist; NORM_SUB]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= l ==> abs l = l`] THEN
    UNDISCH_TAC `&0 < t0` THEN CONV_TAC REAL_FIELD;
    VECTOR_ARITH_TAC]);;

(* The radial projection onto sphere(q,r) and the cone it spans.            *)

let MOI_S3SS_RADPROJ = prove
 (`!(q:real^3) r v.
     &0 < r /\ ~(v = vec 0)
     ==> q + r % (inv(norm v) % v) IN sphere(q,r) /\
         (!t. q + t % ((q + r % (inv(norm v) % v)) - q) = q + (t * r * inv(norm v)) % v)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[IN_SPHERE; dist; VECTOR_ARITH `q - (q + a):real^3 = --a`; NORM_NEG;
                NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; NORM_EQ_0; REAL_MUL_LINV;
                 REAL_MUL_RID; GSYM REAL_MUL_ASSOC];
    REWRITE_TAC[VECTOR_ARITH `(q + a) - q:real^3 = a`; VECTOR_MUL_ASSOC]]);;

(* The abstract cone lemma: radial affinity at w, a circle of radius t0 in  *)
(* the domain, a lower bound m for the image of the circle and a lower      *)
(* bound n for the image of the points outside the disc.                    *)

let MOI_S3SS_RADIAL_CONE = prove
 (`!(x:real^2->bool) (f:real^2->real^3) w e t0 m n.
     (!z l. z IN x /\ dist(w,z) < e /\ &0 <= l /\ l <= &1
            ==> w + l % (z - w) IN x /\ f(w + l % (z - w)) = f w + l % (f z - f w)) /\
     (!a b. a IN x /\ b IN x /\ f a = f b ==> a = b) /\
     &0 < t0 /\ t0 < e /\ w IN x /\ sphere(w,t0) SUBSET x /\
     f continuous_on sphere(w,t0) /\
     &0 < m /\ (!z. z IN sphere(w,t0) ==> m <= dist(f w,f z)) /\
     &0 < n /\ (!z. z IN x /\ t0 <= dist(w,z) ==> n <= dist(f w,f z))
     ==> !r. &0 < r /\ r < m /\ r < n
             ==> ?c. c SUBSET sphere(f w,r) /\
                     c homeomorphic sphere(vec 0:real^2,&1) /\
                     IMAGE f x INTER ball(f w,r) =
                     {f w + t % (z - f w) | t,z | z IN c /\ &0 <= t /\ t < &1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ABBREV_TAC `q = (f:real^2->real^3) w` THEN
  SUBGOAL_THEN `!z. z IN sphere(w:real^2,t0) ==> ~((f:real^2->real^3) z - q = vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `m:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN sphere(w:real^2,t0) ==> m <= norm((f:real^2->real^3) z - q)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `m:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[dist] THEN REWRITE_TAC[NORM_SUB];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\z:real^2. q + r % (inv(norm((f:real^2->real^3) z - q)) %
                                         (f z - q))) (sphere(w,t0))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`q:real^3`; `r:real`; `(f:real^2->real^3) z - q`] MOI_S3SS_RADPROJ) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC(ISPECL [`IMAGE (\z:real^2. q + r % (inv(norm((f:real^2->real^3) z - q)) %
                                         (f z - q))) (sphere(w,t0))`;
                         `sphere(w:real^2,t0)`; `sphere(vec 0:real^2,&1)`]
                 HOMEOMORPHIC_TRANS) THEN
    REWRITE_TAC[HOMEOMORPHIC_SPHERES_EQ] THEN CONJ_TAC THENL
     [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
    EXISTS_TAC `\z:real^2. q + r % (inv(norm((f:real^2->real^3) z - q)) % (f z - q))` THEN
    REWRITE_TAC[COMPACT_SPHERE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SUBGOAL_THEN `(\z:real^2. (f:real^2->real^3) z - q) continuous_on sphere(w,t0)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUB THEN ASM_REWRITE_TAC[CONTINUOUS_ON_CONST];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\z:real^2. norm((f:real^2->real^3) z - q)`; `sphere(w:real^2,t0)`]
        CONTINUOUS_ON_INV) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[NORM_EQ_0]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`z1:real^2`; `z2:real^2`] THEN BETA_TAC THEN STRIP_TAC THEN
    ABBREV_TAC `a1 = norm((f:real^2->real^3) z1 - q)` THEN
    ABBREV_TAC `a2 = norm((f:real^2->real^3) z2 - q)` THEN
    SUBGOAL_THEN `&0 < a1 /\ &0 < a2` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a1"; "a2"] THEN ASM_SIMP_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^3) z1 - q = (a1 * inv a2) % (f z2 - q) /\
                  (f:real^2->real^3) z2 - q = (a2 * inv a1) % (f z1 - q)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `q + r % (inv a1 % ((f:real^2->real^3) z1 - q)) =
                   q + r % (inv a2 % (f z2 - q))` THEN
      REWRITE_TAC[VECTOR_ARITH `q + a:real^3 = q + b <=> a = b`; VECTOR_MUL_ASSOC] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ISPEC `r * inv a1` VECTOR_MUL_LCANCEL_IMP) THEN
        ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_ENTIRE; REAL_INV_EQ_0; REAL_LT_IMP_NZ];
          AP_THM_TAC THEN AP_TERM_TAC THEN
          UNDISCH_TAC `&0 < a1` THEN UNDISCH_TAC `&0 < a2` THEN CONV_TAC REAL_FIELD];
        MATCH_MP_TAC(ISPEC `r * inv a2` VECTOR_MUL_LCANCEL_IMP) THEN
        REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM(ASSUME
          `(r * inv a1) % ((f:real^2->real^3) z1 - q) = (r * inv a2) % (f z2 - q)`)] THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_ENTIRE; REAL_INV_EQ_0; REAL_LT_IMP_NZ];
          AP_THM_TAC THEN AP_TERM_TAC THEN
          UNDISCH_TAC `&0 < a1` THEN UNDISCH_TAC `&0 < a2` THEN CONV_TAC REAL_FIELD]];
      ALL_TAC] THEN
    DISJ_CASES_TAC(REAL_ARITH `a1 <= a2 \/ a2 <= a1`) THENL
     [FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
        `(f:real^2->real^3) z2 - q = (a2 * inv a1) % (f z1 - q)`)) THEN
      MATCH_MP_TAC MOI_S3SS_RAY_INJ THEN
      MAP_EVERY EXISTS_TAC [`x:real^2->bool`; `f:real^2->real^3`; `w:real^2`; `e:real`;
                            `t0:real`; `a1 * inv a2`];
      FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
        `(f:real^2->real^3) z1 - q = (a1 * inv a2) % (f z2 - q)`)) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S3SS_RAY_INJ THEN
      MAP_EVERY EXISTS_TAC [`x:real^2->bool`; `f:real^2->real^3`; `w:real^2`; `e:real`;
                            `t0:real`; `a2 * inv a1`]] THEN
    ASM_REWRITE_TAC[] THEN
    (SUBGOAL_THEN `(z1:real^2) IN x /\ (z2:real^2) IN x` STRIP_ASSUME_TAC THENL
      [UNDISCH_TAC `sphere(w:real^2,t0) SUBSET x` THEN
       UNDISCH_TAC `(z1:real^2) IN sphere(w,t0)` THEN
       UNDISCH_TAC `(z2:real^2) IN sphere(w,t0)` THEN SET_TAC[];
       ALL_TAC] THEN
     SUBGOAL_THEN `dist(w:real^2,z1) = t0 /\ dist(w:real^2,z2) = t0` STRIP_ASSUME_TAC THENL
      [ASM_MESON_TAC[IN_SPHERE]; ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN
     ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
     ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID]);
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM; IN_BALL] THEN BETA_TAC THEN
  X_GEN_TAC `p:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `dist(w:real^2,z) < t0` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `n:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `dist(q:real^3,p) < r` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `z:real^2 = w` THENL
     [EXISTS_TAC `&0` THEN
      EXISTS_TAC `q + r % (inv(norm((f:real^2->real^3) (w + t0 % basis 1) - q)) %
                           (f (w + t0 % basis 1) - q))` THEN
      REWRITE_TAC[REAL_LE_REFL; REAL_LT_01; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `w + t0 % basis 1:real^2` THEN REWRITE_TAC[IN_SPHERE] THEN
        REWRITE_TAC[NORM_ARITH `dist(w:real^2,w + y) = norm y`; NORM_MUL] THEN
        SIMP_TAC[NORM_BASIS; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    ABBREV_TAC `z1 = w + (t0 / norm(z - w:real^2)) % (z - w)` THEN
    ABBREV_TAC `l = norm(z - w:real^2) / t0` THEN
    SUBGOAL_THEN `&0 < norm(z - w:real^2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `norm(z - w:real^2) < t0` ASSUME_TAC THENL
     [ASM_MESON_TAC[dist; NORM_SUB]; ALL_TAC] THEN
    SUBGOAL_THEN `(z1:real^2) IN sphere(w,t0)` ASSUME_TAC THENL
     [EXPAND_TAC "z1" THEN
      REWRITE_TAC[IN_SPHERE; NORM_ARITH `dist(w:real^2,w + y) = norm y`; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_ARITH `&0 < t ==> abs t = t`;
                   REAL_DIV_RMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < l /\ l < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "l" THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z1:real^2) IN x /\ dist(w:real^2,z1) < e` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `sphere(w:real^2,t0) SUBSET x` THEN
        UNDISCH_TAC `(z1:real^2) IN sphere(w,t0)` THEN SET_TAC[];
        UNDISCH_TAC `(z1:real^2) IN sphere(w,t0)` THEN REWRITE_TAC[IN_SPHERE] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^2->real^3) z = q + l % (f z1 - q)` ASSUME_TAC THENL
     [SUBGOAL_THEN `z:real^2 = w + l % (z1 - w)` SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["l"; "z1"] THEN
        REWRITE_TAC[VECTOR_ARITH `(w + a) - w:real^2 = a`; VECTOR_MUL_ASSOC] THEN
        SUBGOAL_THEN `norm(z - w:real^2) / t0 * t0 / norm(z - w) = &1` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < norm(z - w:real^2)` THEN UNDISCH_TAC `&0 < t0` THEN
          CONV_TAC REAL_FIELD;
          VECTOR_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`z1:real^2`; `l:real`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> t = `e:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm((f:real^2->real^3) z1 - q)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[NORM_POS_LT]; ALL_TAC] THEN
    EXISTS_TAC `(l * norm((f:real^2->real^3) z1 - q)) / r` THEN
    EXISTS_TAC `q + r % (inv(norm((f:real^2->real^3) z1 - q)) % (f z1 - q))` THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `z1:real^2` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; NORM_POS_LE];
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
      UNDISCH_TAC `dist(q:real^3,p) < r` THEN
      ASM_REWRITE_TAC[dist; VECTOR_ARITH `q - (q + a):real^3 = --a`; NORM_NEG; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < l ==> abs l = l`];
      MP_TAC(ISPECL [`q:real^3`; `r:real`; `(f:real^2->real^3) z1 - q`] MOI_S3SS_RADPROJ) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th]) THEN
      SUBGOAL_THEN `(l * norm((f:real^2->real^3) z1 - q)) / r * r * inv(norm(f z1 - q)) = l`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < norm((f:real^2->real^3) z1 - q)` THEN UNDISCH_TAC `&0 < r` THEN
        CONV_TAC REAL_FIELD;
        ASM_REWRITE_TAC[]]];
    DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `y:real^3` MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `z1:real^2` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `m <= norm((f:real^2->real^3) z1 - q) /\ ~((f:real^2->real^3) z1 - q = vec 0)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm((f:real^2->real^3) z1 - q)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `p = q + (t * r * inv(norm((f:real^2->real^3) z1 - q))) % (f z1 - q)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`q:real^3`; `r:real`; `(f:real^2->real^3) z1 - q`] MOI_S3SS_RADPROJ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:real` o CONJUNCT2) THEN
      UNDISCH_TAC `p = q + t % (y - q):real^3` THEN
      UNDISCH_TAC `y = q + r % (inv(norm((f:real^2->real^3) z1 - q)) % (f z1 - q))` THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `p = q + t % (y - q):real^3`)) THEN
    ABBREV_TAC `l = t * r * inv(norm((f:real^2->real^3) z1 - q))` THEN
    SUBGOAL_THEN `&0 <= l /\ l < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "l" THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE; NORM_POS_LE];
        REWRITE_TAC[GSYM real_div; REAL_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `r:real` THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z1:real^2) IN x /\ dist(w:real^2,z1) < e` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `sphere(w:real^2,t0) SUBSET x` THEN
        UNDISCH_TAC `(z1:real^2) IN sphere(w,t0)` THEN SET_TAC[];
        UNDISCH_TAC `(z1:real^2) IN sphere(w,t0)` THEN REWRITE_TAC[IN_SPHERE] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`z1:real^2`; `l:real`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `e:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `w + l % (z1 - w):real^2` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[dist; VECTOR_ARITH `q - (q + a):real^3 = --a`; NORM_NEG; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= l ==> abs l = l`] THEN
      EXPAND_TAC "l" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]]]);;

let MOI_S3SS_DISK_CONE = prove
 (`!(x:real^2->bool) (y:real^3->bool) (f:real^2->real^3) g w.
     compact x /\ pl_homeomorphism (x,y) (f,g) /\ w IN interior x
     ==> ?r0. &0 < r0 /\
              !r. &0 < r /\ r < r0
                  ==> ?c. c SUBSET sphere(f w,r) /\
                          c homeomorphic sphere(vec 0:real^2,&1) /\
                          y INTER ball(f w,r) =
                          {f w + t % (z - f w) | t,z | z IN c /\ &0 <= t /\ t < &1}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(w:real^2) IN x` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a IN x /\ b IN x /\ (f:real^2->real^3) a = f b ==> a = b`
  (LABEL_TAC "inj") THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^2->bool`; `f:real^2->real^3`; `w:real^2`]
    MOI_CMB_PL_LOCALLY_CONIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(w:real^2) IN interior x` THEN REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t0 = min e e' / &2` THEN
  SUBGOAL_THEN `&0 < t0 /\ t0 < e /\ t0 < e'` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(w:real^2,t0) SUBSET x` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(w:real^2,e')` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_SPHERE; IN_BALL] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^3) continuous_on sphere(w,t0)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `x:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^2->real^3) (sphere(w,t0))`; `(f:real^2->real^3) w`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[COMPACT_SPHERE];
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^2 = w` ASSUME_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `sphere(w:real^2,t0) SUBSET x` THEN
        UNDISCH_TAC `(z:real^2) IN sphere(w,t0)` THEN SET_TAC[];
        UNDISCH_TAC `(z:real^2) IN sphere(w,t0)` THEN
        ASM_REWRITE_TAC[IN_SPHERE; DIST_REFL] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o REWRITE_RULE[FORALL_IN_IMAGE]))) THEN
  MP_TAC(ISPECL [`IMAGE (f:real^2->real^3) (x DIFF ball(w,t0))`; `(f:real^2->real^3) w`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[COMPACT_DIFF; OPEN_BALL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `x:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_DIFF] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^2 = w` ASSUME_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `~((z:real^2) IN ball(w,t0))` THEN
        ASM_REWRITE_TAC[CENTRE_IN_BALL]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o REWRITE_RULE[FORALL_IN_IMAGE; IN_DIFF; IN_BALL; REAL_NOT_LT]))) THEN
  EXISTS_TAC `min m n` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `y = IMAGE (f:real^2->real^3) x` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^2->bool`; `f:real^2->real^3`; `w:real^2`; `e:real`; `t0:real`;
                 `m:real`; `n:real`] MOI_S3SS_RADIAL_CONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "inj" ACCEPT_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The square model.  Membership in the squares, their boundaries and    *)
(* the square annuli through infnorm; polyhedrality; the cone from 0 over a *)
(* square boundary is the square; scalings between square boundaries.      *)
(* Then two PL annuli glued along a common end are one PL annulus, the      *)
(* image of the bigger square annulus 1 <= infnorm <= 4 with the common end *)
(* the image of the middle square boundary (cone extension of pc_moi_cone). *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SS_SQ_FACTS = prove
 (`!c x:real^2.
     &0 < c
     ==> (x IN interval[--vector[c;c],vector[c;c]] <=> infnorm x <= c) /\
         (x IN interval(--vector[c;c],vector[c;c]) <=> infnorm x < c) /\
         (x IN relative_frontier(interval[--vector[c;c],vector[c;c]]) <=> infnorm x = c)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `relative_frontier(interval[--vector[c;c],vector[c;c]]:real^2->bool) =
                frontier(interval[--vector[c;c],vector[c;c]])` SUBST1_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_2; VECTOR_NEG_COMPONENT; INFNORM_2] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S3SS_SQANN_POLY = prove
 (`!a b. &0 < a /\ a < b
         ==> pl_polyhedron(interval[--vector[b;b],vector[b;b]] DIFF
                           interval(--vector[a;a],vector[a;a]):real^2->bool)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{interval[vector[--b;--b],vector[--a;b]],
               interval[vector[a;--b],vector[b;b]],
               interval[vector[--b;--b],vector[b;--a]],
               interval[vector[--b;a],vector[b;b]]}:(real^2->bool)->bool` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
              POLYTOPE_INTERVAL; UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT] THEN
  GEN_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S3SS_SQ_CONE = prove
 (`!c. &0 < c
       ==> ~(vec 0 IN relative_frontier(interval[--vector[c;c],vector[c;c]]:real^2->bool)) /\
           (!x y. x IN relative_frontier(interval[--vector[c;c],vector[c;c]]:real^2->bool) /\
                  y IN relative_frontier(interval[--vector[c;c],vector[c;c]]) /\
                  y IN segment[vec 0,x] ==> y = x) /\
           UNIONS {segment[vec 0,x] | x IN relative_frontier(interval[--vector[c;c],
                                                                       vector[c;c]]:real^2->bool)} =
           interval[--vector[c;c],vector[c;c]] /\
           pl_polyhedron(relative_frontier(interval[--vector[c;c],vector[c;c]]:real^2->bool)) /\
           ~(relative_frontier(interval[--vector[c;c],vector[c;c]]:real^2->bool) = {})`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_S3SS_SQ_FACTS; INFNORM_0] THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
    ASM_SIMP_TAC[MOI_S3SS_SQ_FACTS] THEN
    REWRITE_TAC[IN_SEGMENT; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `u = &1` (fun th -> ASM_REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
    UNDISCH_TAC `infnorm(y:real^2) = c` THEN ASM_REWRITE_TAC[INFNORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= u ==> abs u = u`] THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[EXTENSION; MOI_CON_IN_CONE; VECTOR_SUB_RZERO; VECTOR_ADD_LID] THEN
    ASM_SIMP_TAC[MOI_S3SS_SQ_FACTS] THEN X_GEN_TAC `p:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[INFNORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= u ==> abs u = u`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN ASM_CASES_TAC `p:real^2 = vec 0` THENL
       [EXISTS_TAC `c % basis 1:real^2` THEN EXISTS_TAC `&0` THEN
        ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL; REAL_POS; INFNORM_MUL] THEN
        SIMP_TAC[INFNORM_2; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < infnorm(p:real^2)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[INFNORM_POS_LT]; ALL_TAC] THEN
      EXISTS_TAC `(c / infnorm(p:real^2)) % p` THEN EXISTS_TAC `infnorm(p:real^2) / c` THEN
      REWRITE_TAC[INFNORM_MUL; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < c ==> abs c = c`; REAL_LE_DIV;
                   REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_ABS_INFNORM] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `&0 < infnorm(p:real^2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      SUBGOAL_THEN `infnorm(p:real^2) / c * c / infnorm p = &1`
        (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
      UNDISCH_TAC `&0 < infnorm(p:real^2)` THEN UNDISCH_TAC `&0 < c` THEN
      CONV_TAC REAL_FIELD];
    REWRITE_TAC[GSYM(ASSUME `&0 < c`)] THEN
    MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
    REWRITE_TAC[POLYTOPE_INTERVAL];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `c % basis 1:real^2` THEN
    ASM_SIMP_TAC[MOI_S3SS_SQ_FACTS; INFNORM_MUL] THEN
    SIMP_TAC[INFNORM_2; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S3SS_PLH_RESTRICT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g s' t'.
     pl_homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ locally_polyhedral s' /\
     IMAGE f s' = t'
     ==> pl_homeomorphism (s',t') (f,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (s':real^M->bool,t':real^N->bool) (f,g)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `t:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (s:real^M->bool,t:real^N->bool) (f,g)` THEN
    REWRITE_TAC[homeomorphism] THEN
    UNDISCH_TAC `IMAGE (f:real^M->real^N) s' = t'` THEN
    UNDISCH_TAC `(s':real^M->bool) SUBSET s` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`s':real^M->bool`; `f:real^M->real^N`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_S3SS_SCALE_IMAGE = prove
 (`!c d. &0 < c /\ &0 < d
         ==> IMAGE (\x:real^2. (d / c) % x)
                   (relative_frontier(interval[--vector[c;c],vector[c;c]])) =
             relative_frontier(interval[--vector[d;d],vector[d;d]])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  ASM_SIMP_TAC[MOI_S3SS_SQ_FACTS] THEN X_GEN_TAC `y:real^2` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[INFNORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < c ==> abs c = c`] THEN
    UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD;
    DISCH_TAC THEN EXISTS_TAC `(c / d) % y:real^2` THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; INFNORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < c ==> abs c = c`] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `d / c * c / d = &1` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LID]) THEN
      UNDISCH_TAC `&0 < c` THEN UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD]]);;

let MOI_S3SS_SQ_SCALE = prove
 (`!c d. &0 < c /\ &0 < d
         ==> pl_homeomorphism
               (relative_frontier(interval[--vector[c;c],vector[c;c]]:real^2->bool),
                relative_frontier(interval[--vector[d;d],vector[d;d]]:real^2->bool))
               ((\x. (d / c) % x),(\x. (c / d) % x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[MOI_S3SS_SCALE_IMAGE] THEN
    REWRITE_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `c / d * d / c = &1 /\ d / c * c / d = &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < c` THEN UNDISCH_TAC `&0 < d` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
    SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\x:real^2. (\x. (d / c) % x) x + vec 0` THEN
    CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN REWRITE_TAC[LINEAR_SCALING] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN ASM_SIMP_TAC[MOI_S3SS_SQ_CONE]]);;

let MOI_S3SS_CONE_EXT = prove
 (`!(h:real^2->real^2) h'.
     pl_homeomorphism
       (relative_frontier(interval[--vector[&4;&4],vector[&4;&4]]),
        relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])) (h,h')
     ==> ?c c'. pl_homeomorphism (interval[--vector[&4;&4],vector[&4;&4]],
                                  interval[--vector[&2;&2],vector[&2;&2]]) (c,c') /\
                (!x r. x IN relative_frontier(interval[--vector[&4;&4],vector[&4;&4]]) /\
                       &0 <= r /\ r <= &1 ==> c (r % x) = r % h x) /\
                (!y. y IN interval[--vector[&4;&4],vector[&4;&4]]
                     ==> infnorm(c y) = infnorm y / &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&4` MOI_S3SS_SQ_CONE) THEN MP_TAC(SPEC `&2` MOI_S3SS_SQ_CONE) THEN
  REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`relative_frontier(interval[--vector[&4;&4],vector[&4;&4]]):real^2->bool`;
                 `relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]):real^2->bool`;
                 `vec 0:real^2`; `vec 0:real^2`; `h:real^2->real^2`; `h':real^2->real^2`]
    MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = moi_con_conemap
                    (relative_frontier(interval[--vector[&4;&4],vector[&4;&4]]))
                    (vec 0:real^2) (vec 0) (h:real^2->real^2)` THEN
  SUBGOAL_THEN
   `!x r. x IN relative_frontier(interval[--vector[&4;&4],vector[&4;&4]]) /\
          &0 <= r /\ r <= &1 ==> (c:real^2->real^2) (r % x) = r % h x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN
    MP_TAC(ISPECL [`relative_frontier(interval[--vector[&4;&4],vector[&4;&4]]):real^2->bool`;
                   `vec 0:real^2`; `vec 0:real^2`; `h:real^2->real^2`; `x:real^2`; `r:real`]
      MOI_CON_CONEMAP_EQ) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_ADD_LID];
    ALL_TAC] THEN
  EXISTS_TAC `c:real^2->real^2` THEN
  EXISTS_TAC `moi_con_conemap
                (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]))
                (vec 0:real^2) (vec 0) (h':real^2->real^2)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?x r. x IN relative_frontier(interval[--vector[&4;&4],vector[&4;&4]]) /\
          &0 <= r /\ r <= &1 /\ y = r % x:real^2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`relative_frontier(interval[--vector[&4;&4],vector[&4;&4]]):real^2->bool`;
                   `vec 0:real^2`; `y:real^2`] MOI_CON_IN_CONE) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_ADD_LID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INFNORM_MUL; REAL_ARITH `&0 <= r ==> abs r = r`] THEN
  SUBGOAL_THEN `(h:real^2->real^2) x IN
                relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])` MP_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism
       (relative_frontier(interval[--vector[&4;&4],vector[&4;&4]]),
        relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]))
       ((h:real^2->real^2),h')` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (h:real^2->real^2)
                   (relative_frontier(interval[--vector[&4;&4],vector[&4;&4]])) =
                 relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])` THEN
    UNDISCH_TAC `(x:real^2) IN relative_frontier(interval[--vector[&4;&4],vector[&4;&4]])` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^2) IN relative_frontier(interval[--vector[&4;&4],vector[&4;&4]])` THEN
  SIMP_TAC[MOI_S3SS_SQ_FACTS; REAL_ARITH `&0 < &4 /\ &0 < &2`] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_S3SS_SQ_MODEL = prove
 (`(!x:real^2. x IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                    interval(--vector[&1;&1],vector[&1;&1]) <=>
               &1 <= infnorm x /\ infnorm x <= &2) /\
   (!x:real^2. x IN interval[--vector[&4;&4],vector[&4;&4]] DIFF
                    interval(--vector[&1;&1],vector[&1;&1]) <=>
               &1 <= infnorm x /\ infnorm x <= &4) /\
   (!x:real^2. x IN interval[--vector[&4;&4],vector[&4;&4]] DIFF
                    interval(--vector[&2;&2],vector[&2;&2]) <=>
               &2 <= infnorm x /\ infnorm x <= &4) /\
   (!x:real^2. x IN interval[--vector[&4;&4],vector[&4;&4]] <=> infnorm x <= &4) /\
   (!x:real^2. x IN interval[--vector[&2;&2],vector[&2;&2]] <=> infnorm x <= &2) /\
   (!x:real^2. x IN relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) <=>
               infnorm x = &1) /\
   (!x:real^2. x IN relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]) <=>
               infnorm x = &2) /\
   (!x:real^2. x IN relative_frontier(interval[--vector[&4;&4],vector[&4;&4]]) <=>
               infnorm x = &4) /\
   locally_polyhedral(relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])
                      :real^2->bool) /\
   locally_polyhedral(relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])
                      :real^2->bool) /\
   locally_polyhedral(interval[--vector[&4;&4],vector[&4;&4]] DIFF
                      interval(--vector[&2;&2],vector[&2;&2]):real^2->bool) /\
   compact(interval[--vector[&4;&4],vector[&4;&4]] DIFF
           interval(--vector[&1;&1],vector[&1;&1]):real^2->bool) /\
   closed(interval[--vector[&2;&2],vector[&2;&2]] DIFF
          interval(--vector[&1;&1],vector[&1;&1]):real^2->bool) /\
   closed(interval[--vector[&4;&4],vector[&4;&4]] DIFF
          interval(--vector[&2;&2],vector[&2;&2]):real^2->bool)`,
  SIMP_TAC[IN_DIFF; MOI_S3SS_SQ_FACTS; REAL_ARITH `&0 < &1 /\ &0 < &2 /\ &0 < &4`;
           REAL_NOT_LT; COMPACT_DIFF; CLOSED_DIFF; COMPACT_INTERVAL; CLOSED_INTERVAL;
           OPEN_INTERVAL] THEN
  REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN REAL_ARITH_TAC) THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THENL
   [MP_TAC(SPEC `&1` MOI_S3SS_SQ_CONE) THEN REWRITE_TAC[REAL_LT_01] THEN SIMP_TAC[];
    MP_TAC(SPEC `&2` MOI_S3SS_SQ_CONE) THEN REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
    SIMP_TAC[];
    MATCH_MP_TAC MOI_S3SS_SQANN_POLY THEN REAL_ARITH_TAC]);;

let MOI_S3SS_DOUBLE = prove
 (`!(a1:real^3->bool) a2 j0 j1 j2.
     pl_annulus_with_ends a1 j0 j1 /\ pl_annulus_with_ends a2 j1 j2 /\ a1 INTER a2 = j1
     ==> ?ff gg. pl_homeomorphism
                  (interval[--vector[&4;&4],vector[&4;&4]] DIFF
                   interval(--vector[&1;&1],vector[&1;&1]):real^2->bool,a1 UNION a2) (ff,gg) /\
                IMAGE ff (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])) = j1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f1:real^2->real^3` (X_CHOOSE_THEN `g1:real^3->real^2`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC))))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `f2:real^2->real^3` (X_CHOOSE_THEN `g2:real^3->real^2`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))
      ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `j1:real^3->bool` &&
    can (find_term (fun t -> t = `f1:real^2->real^3`)) (concl th))) THEN
  MP_TAC MOI_S3SS_SQ_MODEL THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1]) /\
    relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF
    interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]):real^2->bool,
                      relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]):real^2->bool)
                     ((g2:real^3->real^2) o (f1:real^2->real^3),
                      (g1:real^3->real^2) o (f2:real^2->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (f1:real^2->real^3)
                  (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3SS_PLH_RESTRICT THEN
      MAP_EVERY EXISTS_TAC
       [`interval[--vector[&2;&2],vector[&2;&2]] DIFF
         interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`; `a1:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
      MATCH_MP_TAC MOI_S3SS_PLH_RESTRICT THEN
      MAP_EVERY EXISTS_TAC
       [`interval[--vector[&2;&2],vector[&2;&2]] DIFF
         interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`; `a2:real^3->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP PL_HOMEOMORPHISM_COMPOSE
   (CONJ (MATCH_MP PL_HOMEOMORPHISM_COMPOSE
           (CONJ (MATCH_MP MOI_S3SS_SQ_SCALE (REAL_ARITH `&0 < &4 /\ &0 < &2`))
                 (ASSUME `pl_homeomorphism
                    (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]):real^2->bool,
                     relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]):real^2->bool)
                    ((g2:real^3->real^2) o (f1:real^2->real^3),
                     (g1:real^3->real^2) o (f2:real^2->real^3))`)))
         (MATCH_MP MOI_S3SS_SQ_SCALE (REAL_ARITH `&0 < &1 /\ &0 < &2`)))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S3SS_CONE_EXT) THEN
  REWRITE_TAC[o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^2->real^2` (X_CHOOSE_THEN `c':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> can (find_term (fun t -> t = `c':real^2->real^2`)) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> can (find_term (fun t -> t = `g2:real^3->real^2`)) (concl th) &&
                     can (find_term (fun t -> t = `a2:real^3->bool`)) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> can (find_term (fun t -> t = `g1:real^3->real^2`)) (concl th) &&
                     can (find_term (fun t -> t = `a1:real^3->bool`)) (concl th))) THEN
  SUBGOAL_THEN `!x:real^2. infnorm x = &2 ==> (c:real^2->real^2) x = (g2:real^3->real^2)
                                                ((f1:real^2->real^3) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`&2 % x:real^2`; `&1 / &2`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `c:real^2->real^2`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INFNORM_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^2. infnorm y <= &4 ==> infnorm((c:real^2->real^2) y) = infnorm y / &2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `infnorm:real^2->real`)) (concl th) &&
      can (find_term (fun t -> t = `c:real^2->real^2`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^2->real^2)
                  (interval[--vector[&4;&4],vector[&4;&4]] DIFF
                   interval(--vector[&2;&2],vector[&2;&2])) =
                interval[--vector[&2;&2],vector[&2;&2]] DIFF
                interval(--vector[&1;&1],vector[&1;&1])` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^2` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN EXISTS_TAC `(c':real^2->real^2) z` THEN
      SUBGOAL_THEN `(z:real^2) IN interval[--vector[&2;&2],vector[&2;&2]]` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `infnorm((c':real^2->real^2) z) <= &4` ASSUME_TAC THENL
       [SUBGOAL_THEN `(c':real^2->real^2) z IN interval[--vector[&4;&4],vector[&4;&4]]`
        MP_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(c:real^2->real^2) ((c':real^2->real^2) z) = z` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `infnorm(z:real^2) = infnorm((c':real^2->real^2) z) / &2` ASSUME_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `z:real^2`)) THEN ASM_SIMP_TAC[] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `ff = \x:real^2. if infnorm x <= &2 then (f1:real^2->real^3) x
                              else (f2:real^2->real^3) ((c:real^2->real^2) x)` THEN
  SUBGOAL_THEN `!x:real^2. infnorm x = &2
                           ==> (f2:real^2->real^3) ((c:real^2->real^2) x) = (f1:real^2->real^3) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(f1:real^2->real^3) x IN a2` ASSUME_TAC THENL
     [SUBGOAL_THEN `(f1:real^2->real^3) x IN
                    IMAGE f1 (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]))`
      MP_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (f2:real^2->real^3)
                     (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                      interval(--vector[&1;&1],vector[&1;&1])) = a2` THEN
      UNDISCH_TAC `relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) SUBSET
                   interval[--vector[&2;&2],vector[&2;&2]] DIFF
                   interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
      SET_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interval[--vector[&4;&4],vector[&4;&4]] DIFF interval(--vector[&1;&1],vector[&1;&1])
    :real^2->bool =
    (interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1])) UNION
    (interval[--vector[&4;&4],vector[&4;&4]] DIFF interval(--vector[&2;&2],vector[&2;&2]))`
  (LABEL_TAC "xu") THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_UNION] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (interval[--vector[&4;&4],vector[&4;&4]] DIFF
               interval(--vector[&1;&1],vector[&1;&1]):real^2->bool) (ff:real^2->real^3)`
  ASSUME_TAC THENL
   [USE_THEN "xu" SUBST1_TAC THEN MATCH_MP_TAC PL_MAP_ON_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `f1:real^2->real^3` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "ff" THEN SIMP_TAC[];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `(f2:real^2->real^3) o (c:real^2->real^2)` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[o_THM] THEN EXPAND_TAC "ff" THEN X_GEN_TAC `x:real^2` THEN
        BETA_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
        EXISTS_TAC `interval[--vector[&2;&2],vector[&2;&2]] DIFF
                    interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
        ASM_REWRITE_TAC[SUBSET_REFL] THEN
        MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
        EXISTS_TAC `interval[--vector[&4;&4],vector[&4;&4]]:real^2->bool` THEN
        ASM_REWRITE_TAC[SUBSET] THEN GEN_TAC THEN REAL_ARITH_TAC];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. &2 <= infnorm y /\ infnorm y <= &4
               ==> (c:real^2->real^2) y IN
                   interval[--vector[&2;&2],vector[&2;&2]] DIFF
                   interval(--vector[&1;&1],vector[&1;&1])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN interval[--vector[&4;&4],vector[&4;&4]] DIFF
                                interval(--vector[&2;&2],vector[&2;&2])` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (c:real^2->real^2)
                   (interval[--vector[&4;&4],vector[&4;&4]] DIFF
                    interval(--vector[&2;&2],vector[&2;&2])) =
                 interval[--vector[&2;&2],vector[&2;&2]] DIFF
                 interval(--vector[&1;&1],vector[&1;&1])` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^2. &1 <= infnorm x /\ infnorm x <= &2 /\ &2 < infnorm y /\ infnorm y <= &4
                 ==> ~((f1:real^2->real^3) x = (f2:real^2->real^3) ((c:real^2->real^2) y))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(c:real^2->real^2) y IN
                  interval[--vector[&2;&2],vector[&2;&2]] DIFF
                  interval(--vector[&1;&1],vector[&1;&1])` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^2) IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                                interval(--vector[&1;&1],vector[&1;&1])` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f2:real^2->real^3) ((c:real^2->real^2) y) IN a1 INTER a2` MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `(f1:real^2->real^3) x = f2 ((c:real^2->real^2) y)`)) THEN
        SUBST1_TAC(SYM(ASSUME `IMAGE (f1:real^2->real^3)
                         (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                          interval(--vector[&1;&1],vector[&1;&1])) = a1`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        SUBST1_TAC(SYM(ASSUME `IMAGE (f2:real^2->real^3)
                         (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                          interval(--vector[&1;&1],vector[&1;&1])) = a2`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^2) IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                                interval(--vector[&1;&1],vector[&1;&1])` ASSUME_TAC THENL
     [UNDISCH_TAC `relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) SUBSET
                   interval[--vector[&2;&2],vector[&2;&2]] DIFF
                   interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
      UNDISCH_TAC `(z:real^2) IN relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:real^2->real^2) y = z` ASSUME_TAC THENL
     [MP_TAC(AP_TERM `g2:real^3->real^2`
        (ASSUME `(f2:real^2->real^3) ((c:real^2->real^2) y) = f2 z`)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `infnorm(z:real^2) = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^2) IN relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `infnorm((c:real^2->real^2) y) = infnorm y / &2` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN interval[--vector[&4;&4],vector[&4;&4]] DIFF
               interval(--vector[&1;&1],vector[&1;&1]) /\
          y IN interval[--vector[&4;&4],vector[&4;&4]] DIFF
               interval(--vector[&1;&1],vector[&1;&1]) /\
          (ff:real^2->real^3) x = ff y ==> x = y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "ff" THEN BETA_TAC THEN
    ASM_CASES_TAC `infnorm(x:real^2) <= &2` THEN ASM_CASES_TAC `infnorm(y:real^2) <= &2` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `(x:real^2) IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                                  interval(--vector[&1;&1],vector[&1;&1]) /\
                    (y:real^2) IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                                  interval(--vector[&1;&1],vector[&1;&1])`
      STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(AP_TERM `g1:real^3->real^2`
        (ASSUME `(f1:real^2->real^3) x = f1 y`)) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `y:real^2`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> t = `f1:real^2->real^3`)) (concl th) &&
        can (find_term (fun t -> t = `c:real^2->real^2`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^2`; `x:real^2`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> t = `f1:real^2->real^3`)) (concl th) &&
        can (find_term (fun t -> t = `c:real^2->real^2`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(c:real^2->real^2) x IN
                    interval[--vector[&2;&2],vector[&2;&2]] DIFF
                    interval(--vector[&1;&1],vector[&1;&1]) /\
                    (c:real^2->real^2) y IN
                    interval[--vector[&2;&2],vector[&2;&2]] DIFF
                    interval(--vector[&1;&1],vector[&1;&1])` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(c:real^2->real^2) x = c y` ASSUME_TAC THENL
       [MP_TAC(AP_TERM `g2:real^3->real^2`
          (ASSUME `(f2:real^2->real^3) ((c:real^2->real^2) x) = f2 (c y)`)) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^2) IN interval[--vector[&4;&4],vector[&4;&4]] /\
                    (y:real^2) IN interval[--vector[&4;&4],vector[&4;&4]]`
      STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(AP_TERM `c':real^2->real^2` (ASSUME `(c:real^2->real^2) x = c y`)) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ff:real^2->real^3)
                  (interval[--vector[&4;&4],vector[&4;&4]] DIFF
                   interval(--vector[&1;&1],vector[&1;&1])) = a1 UNION a2`
  ASSUME_TAC THENL
   [USE_THEN "xu" SUBST1_TAC THEN REWRITE_TAC[IMAGE_UNION] THEN BINOP_TAC THENL
     [TRANS_TAC EQ_TRANS `IMAGE (f1:real^2->real^3)
                            (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                             interval(--vector[&1;&1],vector[&1;&1]))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> (f:real^2->real^3) x = g x)
                               ==> IMAGE f s = IMAGE g s`) THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "ff" THEN SIMP_TAC[];
        ASM_REWRITE_TAC[]];
      TRANS_TAC EQ_TRANS `IMAGE (f2:real^2->real^3)
                            (IMAGE (c:real^2->real^2)
                              (interval[--vector[&4;&4],vector[&4;&4]] DIFF
                               interval(--vector[&2;&2],vector[&2;&2])))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_o] THEN
        MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> (f:real^2->real^3) x = g x)
                               ==> IMAGE f s = IMAGE g s`) THEN
        ASM_REWRITE_TAC[o_THM] THEN EXPAND_TAC "ff" THEN BETA_TAC THEN
        X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`interval[--vector[&4;&4],vector[&4;&4]] DIFF
                  interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`;
                 `ff:real^2->real^3`; `a1 UNION a2:real^3->bool`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `gg:real^3->real^2`) THEN
  EXISTS_TAC `ff:real^2->real^3` THEN EXISTS_TAC `gg:real^3->real^2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> (f:real^2->real^3) x = g x)
                           ==> IMAGE f s = IMAGE g s`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "ff" THEN SIMP_TAC[REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* 4. Local models.  A point of a PL annulus off its ends, and a point of   *)
(* the common end of two glued PL annuli, are images of interior points of  *)
(* a planar compact set under a PL homeomorphism, so the annulus (or the    *)
(* union) is a cone over a simple closed curve near the point.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SS_ANN_FACTS = prove
 (`!(a:real^3->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> j0 SUBSET a /\ j1 SUBSET a /\ DISJOINT j0 j1 /\ compact a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC MOI_S3SS_SQ_MODEL THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1]) /\
    relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1]) /\
    DISJOINT (relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]))
             (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]):real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3)
                   (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                    interval(--vector[&1;&1],vector[&1;&1])) = a` THEN
    UNDISCH_TAC `relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) SUBSET
                 interval[--vector[&2;&2],vector[&2;&2]] DIFF
                 interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
    SET_TAC[];
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^3)
                   (interval[--vector[&2;&2],vector[&2;&2]] DIFF
                    interval(--vector[&1;&1],vector[&1;&1])) = a` THEN
    UNDISCH_TAC `relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]) SUBSET
                 interval[--vector[&2;&2],vector[&2;&2]] DIFF
                 interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
    SET_TAC[];
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!x. x IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                          interval(--vector[&1;&1],vector[&1;&1])
                     ==> (g:real^3->real^2) ((f:real^2->real^3) x) = x` THEN
    UNDISCH_TAC `relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]) SUBSET
                 interval[--vector[&2;&2],vector[&2;&2]] DIFF
                 interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
    UNDISCH_TAC `relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]) SUBSET
                 interval[--vector[&2;&2],vector[&2;&2]] DIFF
                 interval(--vector[&1;&1],vector[&1;&1]):real^2->bool` THEN
    UNDISCH_TAC `DISJOINT (relative_frontier(interval[--vector[&1;&1],vector[&1;&1]]))
                   (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]]):real^2->bool)` THEN
    SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `a:real^3->bool`)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[COMPACT_DIFF; COMPACT_INTERVAL; OPEN_INTERVAL]]);;

let MOI_S3SS_SQ_INTERIORS = prove
 (`(!x:real^2. &1 < infnorm x /\ infnorm x < &2
               ==> x IN interior(interval[--vector[&2;&2],vector[&2;&2]] DIFF
                                 interval(--vector[&1;&1],vector[&1;&1]))) /\
   (!x:real^2. &1 < infnorm x /\ infnorm x < &4
               ==> x IN interior(interval[--vector[&4;&4],vector[&4;&4]] DIFF
                                 interval(--vector[&1;&1],vector[&1;&1])))`,
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `(x:real^2) IN interval(--vector[&2;&2],vector[&2;&2]) DIFF
                                interval[--vector[&1;&1],vector[&1;&1]]` MP_TAC THENL
     [ASM_SIMP_TAC[IN_DIFF; MOI_S3SS_SQ_FACTS; REAL_ARITH `&0 < &1 /\ &0 < &2`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SPEC_TAC(`x:real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    SIMP_TAC[OPEN_DIFF; OPEN_INTERVAL; CLOSED_INTERVAL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN
    SIMP_TAC[MOI_S3SS_SQ_FACTS; REAL_ARITH `&0 < &1 /\ &0 < &2`] THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `(x:real^2) IN interval(--vector[&4;&4],vector[&4;&4]) DIFF
                                interval[--vector[&1;&1],vector[&1;&1]]` MP_TAC THENL
     [ASM_SIMP_TAC[IN_DIFF; MOI_S3SS_SQ_FACTS; REAL_ARITH `&0 < &1 /\ &0 < &4`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SPEC_TAC(`x:real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    SIMP_TAC[OPEN_DIFF; OPEN_INTERVAL; CLOSED_INTERVAL] THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN
    SIMP_TAC[MOI_S3SS_SQ_FACTS; REAL_ARITH `&0 < &1 /\ &0 < &4`] THEN REAL_ARITH_TAC]);;

let MOI_S3SS_ANN_INNER = prove
 (`!(a:real^3->bool) j0 j1 q.
     pl_annulus_with_ends a j0 j1 /\ q IN a /\ ~(q IN j0) /\ ~(q IN j1)
     ==> ?x (f:real^2->real^3) g w. compact x /\ pl_homeomorphism (x,a) (f,g) /\
                                  w IN interior x /\ f w = q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:real^2->real^3`
    (X_CHOOSE_THEN `g:real^3->real^2` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`interval[--vector[&2;&2],vector[&2;&2]] DIFF
     interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`;
    `f:real^2->real^3`; `g:real^3->real^2`; `(g:real^3->real^2) q`] THEN
  ASM_SIMP_TAC[COMPACT_DIFF; COMPACT_INTERVAL; OPEN_INTERVAL] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> can (find_term (fun t -> t = `g:real^3->real^2`)) (concl th))) THEN
  SUBGOAL_THEN `(f:real^2->real^3) ((g:real^3->real^2) q) = q` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:real^3->real^2) q IN
                interval[--vector[&2;&2],vector[&2;&2]] DIFF
                interval(--vector[&1;&1],vector[&1;&1])` MP_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^3->real^2) a =
                 interval[--vector[&2;&2],vector[&2;&2]] DIFF
                 interval(--vector[&1;&1],vector[&1;&1])` THEN
    UNDISCH_TAC `(q:real^3) IN a` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC MOI_S3SS_SQ_MODEL THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(CONJUNCT1 MOI_S3SS_SQ_INTERIORS) THEN
  SUBGOAL_THEN `~(infnorm((g:real^3->real^2) q) = &1) /\ ~(infnorm((g:real^3->real^2) q) = &2)`
  MP_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [UNDISCH_TAC `~((q:real^3) IN j0)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `j0:real^3->bool`)) THEN
    SUBST1_TAC(SYM(ASSUME `(f:real^2->real^3) ((g:real^3->real^2) q) = q`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~((q:real^3) IN j1)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `j1:real^3->bool`)) THEN
    SUBST1_TAC(SYM(ASSUME `(f:real^2->real^3) ((g:real^3->real^2) q) = q`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

let MOI_S3SS_ANN_DOUBLE_MODEL = prove
 (`!(a1:real^3->bool) a2 j0 j1 j2 q.
     pl_annulus_with_ends a1 j0 j1 /\ pl_annulus_with_ends a2 j1 j2 /\
     a1 INTER a2 = j1 /\ q IN j1
     ==> ?x (f:real^2->real^3) g w. compact x /\ pl_homeomorphism (x,a1 UNION a2) (f,g) /\
                                  w IN interior x /\ f w = q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `a2:real^3->bool`; `j0:real^3->bool`; `j1:real^3->bool`;
                 `j2:real^3->bool`] MOI_S3SS_DOUBLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^2->real^3` (X_CHOOSE_THEN `gg:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(q:real^3) IN j1` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `j1:real^3->bool`)) THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`interval[--vector[&4;&4],vector[&4;&4]] DIFF
     interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`;
    `ff:real^2->real^3`; `gg:real^3->real^2`; `w:real^2`] THEN
  ASM_SIMP_TAC[COMPACT_DIFF; COMPACT_INTERVAL; OPEN_INTERVAL] THEN
  MATCH_MP_TAC(CONJUNCT2 MOI_S3SS_SQ_INTERIORS) THEN
  UNDISCH_TAC `(w:real^2) IN relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])` THEN
  SIMP_TAC[MOI_S3SS_SQ_FACTS; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC);;

let MOI_S3SS_MODEL_CONE = prove
 (`!(y:real^3->bool) q.
     (?x (f:real^2->real^3) g w. compact x /\ pl_homeomorphism (x,y) (f,g) /\
                                w IN interior x /\ f w = q)
     ==> ?r0. &0 < r0 /\
              !r. &0 < r /\ r < r0
                  ==> ?c. c SUBSET sphere(q,r) /\ c homeomorphic sphere(vec 0:real^2,&1) /\
                          y INTER ball(q,r) =
                          {q + t % (z - q) | t,z | z IN c /\ &0 <= t /\ t < &1}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^3`
    (X_CHOOSE_THEN `g:real^3->real^2` (X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_S3SS_DISK_CONE THEN
  MAP_EVERY EXISTS_TAC [`x:real^2->bool`; `g:real^3->real^2`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. The pieces of the chain: annuli hh i and bridges bb i, consecutive    *)
(* pieces meeting exactly in a common end, all other pairs disjoint.        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SS_PIECES = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh
     ==> (!i. pl_annulus_with_ends (hh i) (jl i) (jh i)) /\
         (!i. pl_annulus_with_ends (bb i) (jh i) (jl (i + &1))) /\
         (!i k. ~(i = k) ==> DISJOINT (hh i) (hh k)) /\
         (!i k. ~(i = k) ==> DISJOINT (bb i) (bb k)) /\
         (!i k. bb i INTER hh k SUBSET jh i UNION jl (i + &1)) /\
         (!i. jl i SUBSET hh i /\ jh i SUBSET hh i /\ jh i SUBSET bb i /\
              jl (i + &1) SUBSET bb i) /\
         (!i. DISJOINT (jl i) (jh i)) /\
         (!i. compact (hh i) /\ compact (bb i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3GF_CHAIN_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_chain] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "moi_s32_chain"
                                              with Failure _ -> false)) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_tower] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "moi_s32_tower"
                                              with Failure _ -> false)) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_model] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "moi_s32_model"
                                              with Failure _ -> false)) (concl th))) THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. pl_annulus_with_ends ((hh:int->real^3->bool) i) (jl i) (jh i) /\
                    pl_annulus_with_ends ((bb:int->real^3->bool) i) (jh i) (jl (i + &1))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i k. ~(i = k) ==> DISJOINT ((hh:int->real^3->bool) i) (hh k)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `DISJOINT ((dd:int->real^3->bool) (&2 * i)) (dd (&2 * k))` ASSUME_TAC THENL
     [SUBGOAL_THEN `&2 * (i:int) + &2 <= &2 * k \/ &2 * k + &2 <= &2 * i` MP_TAC THENL
       [UNDISCH_TAC `~(i:int = k)` THEN INT_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[DISJOINT_SYM]] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `dd:int->real^3->bool`)) (concl th) &&
        is_imp(snd(strip_forall(concl th))) &&
        can (find_term (fun t -> try fst(dest_const t) = "DISJOINT" with Failure _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `moi_s32_cyl`; `(dd:int->real^3->bool) (&2 * i)`;
                   `(dd:int->real^3->bool) (&2 * k)`] MOI_STD_IMAGE_REV_DISJOINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM DISJOINT] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET_TRANS]; ASM_MESON_TAC[SUBSET_TRANS]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(hh:int->real^3->bool) i SUBSET IMAGE (g:real^3->real^3)
                    (revolution ((dd:int->real^3->bool) (&2 * i))) /\
                  (hh:int->real^3->bool) k SUBSET IMAGE (g:real^3->real^3)
                    (revolution ((dd:int->real^3->bool) (&2 * k)))` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i k. (bb:int->real^3->bool) i INTER (hh:int->real^3->bool) k SUBSET
                      jh i UNION jl (i + &1)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `(hh:int->real^3->bool) k SUBSET moi_s32_evens s2` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `frontier((s2:int->real^3->bool) (&2 * k))` THEN
      ASM_REWRITE_TAC[moi_s32_evens] THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      EXISTS_TAC `frontier((s2:int->real^3->bool) (&2 * k))` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `k:int` THEN REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(bb:int->real^3->bool) i INTER moi_s32_evens s2 = jh i UNION jl (i + &1)`
    MP_TAC THENL [ASM_MESON_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i. jl i SUBSET (hh:int->real^3->bool) i /\ jh i SUBSET hh i /\
                    DISJOINT (jl i) (jh i) /\ compact (hh i) /\
                    jh i SUBSET (bb:int->real^3->bool) i /\ jl (i + &1) SUBSET bb i /\
                    compact (bb i)`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`(hh:int->real^3->bool) i`; `(jl:int->real^3->bool) i`;
                   `(jh:int->real^3->bool) i`] MOI_S3SS_ANN_FACTS) THEN
    MP_TAC(ISPECL [`(bb:int->real^3->bool) i`; `(jh:int->real^3->bool) i`;
                   `(jl:int->real^3->bool) (i + &1)`] MOI_S3SS_ANN_FACTS) THEN
    ASM_SIMP_TAC[];
    SIMP_TAC[]]);;

let MOI_S3SS_PIECE_INTER = prove
 (`!(hh:int->real^3->bool) bb jl jh.
     (!i k. ~(i = k) ==> DISJOINT (hh i) (hh k)) /\
     (!i k. bb i INTER hh k SUBSET jh i UNION jl (i + &1)) /\
     (!i. jl i SUBSET hh i /\ jh i SUBSET hh i /\ jh i SUBSET bb i /\
          jl (i + &1) SUBSET bb i)
     ==> (!i. hh i INTER bb i = jh i) /\
         (!i. bb i INTER hh (i + &1) = jl (i + &1)) /\
         (!i k. ~(k = i) /\ ~(k = i + &1) ==> DISJOINT (bb i) (hh k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [SUBGOAL_THEN `DISJOINT ((hh:int->real^3->bool) i) (hh (i + &1))` MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `(i:int) + &1` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:int`; `i:int`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        not(is_imp(snd(strip_forall(concl th)))))) THEN
      SET_TAC[];
      FIRST_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      SET_TAC[]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [SUBGOAL_THEN `DISJOINT ((hh:int->real^3->bool) i) (hh (i + &1))` MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:int`; `(i:int) + &1`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        not(is_imp(snd(strip_forall(concl th)))))) THEN
      SET_TAC[];
      FIRST_ASSUM(MP_TAC o SPEC `(i:int) + &1` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      FIRST_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      SET_TAC[]];
    SUBGOAL_THEN `DISJOINT ((hh:int->real^3->bool) k) (hh i) /\
                  DISJOINT ((hh:int->real^3->bool) k) (hh (i + &1))` MP_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(i:int) + &1` o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:int`; `k:int`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      not(is_imp(snd(strip_forall(concl th)))))) THEN
    SET_TAC[]]);;

(* Which pieces contain a given point (the abstract incidence facts).       *)

let MOI_S3SS_PIECE_CASES = prove
 (`!(hh:int->real^3->bool) bb jl jh q.
     (!i k. ~(i = k) ==> DISJOINT (hh i) (hh k)) /\
     (!i k. ~(i = k) ==> DISJOINT (bb i) (bb k)) /\
     (!i. jl i SUBSET hh i /\ jh i SUBSET hh i /\ jh i SUBSET bb i /\
          jl (i + &1) SUBSET bb i) /\
     (!i. DISJOINT (jl i) (jh i)) /\
     (!i. hh i INTER bb i = jh i) /\
     (!i. bb i INTER hh (i + &1) = jl (i + &1)) /\
     (!i k. ~(k = i) /\ ~(k = i + &1) ==> DISJOINT (bb i) (hh k))
     ==> (!i. q IN hh i ==> !k. q IN hh k ==> k = i) /\
         (!i. q IN bb i ==> !k. q IN bb k ==> k = i) /\
         (!i. q IN jh i ==> !k. q IN bb k ==> k = i) /\
         (!i. q IN jl i ==> !k. q IN bb k ==> k = i - &1) /\
         (!i. q IN hh i /\ ~(q IN jl i) /\ ~(q IN jh i) ==> !k. ~(q IN bb k)) /\
         (!i. q IN bb i /\ (!k. ~(q IN hh k)) ==> ~(q IN jh i) /\ ~(q IN jl (i + &1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `k:int = i` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:int`; `i:int`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `hh:int->real^3->bool`)) (concl th) &&
      not(can (find_term (fun t -> t = `bb:int->real^3->bool`)) (concl th)))) THEN
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `k:int = i` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:int`; `i:int`] o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `bb:int->real^3->bool`)) (concl th) &&
      not(can (find_term (fun t -> t = `hh:int->real^3->bool`)) (concl th)))) THEN
    ASM SET_TAC[];
    X_GEN_TAC `i:int` THEN DISCH_TAC THEN X_GEN_TAC `k:int` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k:int = i` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(q:real^3) IN hh (i:int)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `i = (k:int) + &1` THENL
     [SUBGOAL_THEN `(q:real^3) IN jl (i:int)` ASSUME_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`k:int`; `i:int`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> t = `bb:int->real^3->bool`)) (concl th) &&
        can (find_term (fun t -> t = `hh:int->real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    X_GEN_TAC `i:int` THEN DISCH_TAC THEN X_GEN_TAC `k:int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:real^3) IN hh (i:int)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `k:int = i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(q:real^3) IN jh (k:int)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = (k:int) + &1` THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:int`; `i:int`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `bb:int->real^3->bool`)) (concl th) &&
      can (find_term (fun t -> t = `hh:int->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN X_GEN_TAC `k:int` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k:int = i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `i = (k:int) + &1` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:int`; `i:int`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `bb:int->real^3->bool`)) (concl th) &&
      can (find_term (fun t -> t = `hh:int->real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `i:int` THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:int` o check (fun th -> is_forall(concl th) &&
        is_neg(snd(strip_forall(concl th))))) THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `(i:int) + &1` o check (fun th -> is_forall(concl th) &&
        is_neg(snd(strip_forall(concl th))))) THEN ASM SET_TAC[]]]);;

let MOI_S3SS_CLASSIFY = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh q.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh /\
     q IN moi_s32_chainset g hh bb /\ ~(q = g (vec 0))
     ==> ?y. y SUBSET moi_s32_chainset g hh bb /\
             (!k. q IN hh k ==> hh k SUBSET y) /\ (!k. q IN bb k ==> bb k SUBSET y) /\
             (?x (f:real^2->real^3) g' w. compact x /\ pl_homeomorphism (x,y) (f,g') /\
                                         w IN interior x /\ f w = q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3SS_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hh:int->real^3->bool`; `bb:int->real^3->bool`; `jl:int->real^3->bool`;
                 `jh:int->real^3->bool`] MOI_S3SS_PIECE_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hh:int->real^3->bool`; `bb:int->real^3->bool`; `jl:int->real^3->bool`;
                 `jh:int->real^3->bool`; `q:real^3`] MOI_S3SS_PIECE_CASES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. (hh:int->real^3->bool) k SUBSET moi_s32_chainset g hh bb /\
                    (bb:int->real^3->bool) k SUBSET moi_s32_chainset g hh bb`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[moi_s32_chainset] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    CONJ_TAC THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN DISJ1_TAC THEN
    EXISTS_TAC `(hh:int->real^3->bool) k UNION bb k` THEN
    (CONJ_TAC THENL [EXISTS_TAC `k:int` THEN REWRITE_TAC[]; ASM_REWRITE_TAC[IN_UNION]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `?i. (q:real^3) IN (hh:int->real^3->bool) i \/ q IN (bb:int->real^3->bool) i`
  (X_CHOOSE_THEN `i:int` ASSUME_TAC) THENL
   [UNDISCH_TAC `(q:real^3) IN moi_s32_chainset g hh bb` THEN
    UNDISCH_TAC `~(q = (g:real^3->real^3) (vec 0))` THEN
    REWRITE_TAC[moi_s32_chainset; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_UNIV; IN_SING] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `i:int`) ASSUME_TAC)) THEN
    EXISTS_TAC `i:int` THEN UNDISCH_TAC `(q:real^3) IN t` THEN
    ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  ASM_CASES_TAC `?k. (q:real^3) IN (hh:int->real^3->bool) k` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `i0:int` o check (fun th -> is_exists(concl th))) THEN
    ASM_CASES_TAC `(q:real^3) IN (jh:int->real^3->bool) i0` THENL
     [EXISTS_TAC `(hh:int->real^3->bool) i0 UNION bb i0` THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[UNION_SUBSET];
        X_GEN_TAC `k:int` THEN DISCH_TAC THEN
        SUBGOAL_THEN `k:int = i0` SUBST1_TAC THENL [ASM_MESON_TAC[]; SET_TAC[]];
        X_GEN_TAC `k:int` THEN DISCH_TAC THEN
        SUBGOAL_THEN `k:int = i0` SUBST1_TAC THENL [ASM_MESON_TAC[]; SET_TAC[]];
        MATCH_MP_TAC MOI_S3SS_ANN_DOUBLE_MODEL THEN
        MAP_EVERY EXISTS_TAC [`(jl:int->real^3->bool) i0`; `(jh:int->real^3->bool) i0`;
                              `(jl:int->real^3->bool) (i0 + &1)`] THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(q:real^3) IN (jl:int->real^3->bool) i0` THENL
     [EXISTS_TAC `(bb:int->real^3->bool) (i0 - &1) UNION hh i0` THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[UNION_SUBSET];
        X_GEN_TAC `k:int` THEN DISCH_TAC THEN
        SUBGOAL_THEN `k:int = i0` SUBST1_TAC THENL [ASM_MESON_TAC[]; SET_TAC[]];
        X_GEN_TAC `k:int` THEN DISCH_TAC THEN
        SUBGOAL_THEN `k:int = i0 - &1` SUBST1_TAC THENL [ASM_MESON_TAC[]; SET_TAC[]];
        MATCH_MP_TAC MOI_S3SS_ANN_DOUBLE_MODEL THEN
        MAP_EVERY EXISTS_TAC [`(jh:int->real^3->bool) (i0 - &1)`; `(jl:int->real^3->bool) i0`;
                              `(jh:int->real^3->bool) i0`] THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `(i0:int) - &1` (ASSUME
          `!i. pl_annulus_with_ends ((bb:int->real^3->bool) i) (jh i) (jl (i + &1))`)) THEN
        MP_TAC(SPEC `(i0:int) - &1` (ASSUME
          `!i. (bb:int->real^3->bool) i INTER hh (i + &1) = jl (i + &1)`)) THEN
        REWRITE_TAC[INT_ARITH `(i0:int) - &1 + &1 = i0`] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `(hh:int->real^3->bool) i0` THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `k:int` THEN DISCH_TAC THEN
      SUBGOAL_THEN `k:int = i0` SUBST1_TAC THENL [ASM_MESON_TAC[]; SET_TAC[]];
      ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_S3SS_ANN_INNER THEN
      MAP_EVERY EXISTS_TAC [`(jl:int->real^3->bool) i0`; `(jh:int->real^3->bool) i0`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN (bb:int->real^3->bool) i` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM]) THEN
  EXISTS_TAC `(bb:int->real^3->bool) i` THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    X_GEN_TAC `k:int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `k:int = i` SUBST1_TAC THENL [ASM_MESON_TAC[]; SET_TAC[]];
    MATCH_MP_TAC MOI_S3SS_ANN_INNER THEN
    MAP_EVERY EXISTS_TAC [`(jh:int->real^3->bool) i`; `(jl:int->real^3->bool) (i + &1)`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* Local finiteness: near a point q of the chain other than the centre only *)
(* finitely many pieces occur (the tower is locally finite off the centre   *)
(* and the rim), so the pseudo-cell is near q the union of the pieces that  *)
(* contain q.                                                               *)

let MOI_S3SS_LOCFIN = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh q y.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh /\
     q IN moi_s32_chainset g hh bb /\ ~(q = g (vec 0)) /\
     y SUBSET moi_s32_chainset g hh bb /\
     (!k. q IN hh k ==> hh k SUBSET y) /\ (!k. q IN bb k ==> bb k SUBSET y)
     ==> ?rho. &0 < rho /\ ball(q,rho) SUBSET moi_s32_open g /\
               (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim) INTER ball(q,rho) =
               y INTER ball(q,rho)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3SS_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3GF_CHAIN_PIECES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3GF_CHAIN_V) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`] MOI_S3GF_TOWER_TORI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_model] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "moi_s32_model"
                                              with Failure _ -> false)) (concl th))) THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `?p. p IN v /\ (g:real^3->real^3) p = q` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s32_chainset g hh bb SUBSET (g:real^3->real^3) (vec 0) INSERT IMAGE g v` THEN
    UNDISCH_TAC `(q:real^3) IN moi_s32_chainset g hh bb` THEN
    UNDISCH_TAC `~(q = (g:real^3->real^3) (vec 0))` THEN
    REWRITE_TAC[SUBSET; IN_INSERT; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d. &0 < d /\ cball(p:real^3,d) SUBSET v` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_CBALL]; ALL_TAC] THEN
  SUBGOAL_THEN `v SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  ABBREV_TAC `ss = {i:int | ~(revolution ((dd:int->real^3->bool) i) INTER cball(p,d) = {})}` THEN
  SUBGOAL_THEN `FINITE (ss:int->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ss" THEN
    FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2 o REWRITE_RULE[moi_s32_tower] o
      check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "moi_s32_tower"
                                                with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[COMPACT_CBALL] THEN
    UNDISCH_TAC `cball(p:real^3,d) SUBSET v` THEN
    UNDISCH_TAC `DISJOINT (v:real^3->bool) moi_s32_axis` THEN
    UNDISCH_TAC `vec 0 IN moi_s32_axis` THEN
    UNDISCH_TAC `v SUBSET interior moi_s32_cyl` THEN
    UNDISCH_TAC `moi_s32_rim SUBSET frontier moi_s32_cyl` THEN
    UNDISCH_TAC `frontier moi_s32_cyl INTER interior moi_s32_cyl = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `o0 = IMAGE (g:real^3->real^3) (ball(p,d))` THEN
  SUBGOAL_THEN `open (o0:real^3->bool) /\ (q:real^3) IN o0 /\
                o0 SUBSET IMAGE (g:real^3->real^3) v`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "o0" THEN
    SUBGOAL_THEN `ball(p:real^3,d) SUBSET v` ASSUME_TAC THENL
     [ASM_MESON_TAC[BALL_SUBSET_CBALL; SUBSET_TRANS]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS];
        ASM_MESON_TAC[SUBSET]];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `p:real^3` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL];
      MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j x. x IN IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) j)) /\
                      x IN o0 ==> j IN ss` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "o0" THEN EXPAND_TAC "ss" THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `a:real^3 = b` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `moi_s32_cyl`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `revolution ((dd:int->real^3->bool) j) SUBSET v` MP_TAC THENL
         [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`p:real^3`; `d:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
          ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `a:real^3` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:real^3`; `d:real`] BALL_SUBSET_CBALL) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `tt = {k:int | &2 * k IN ss \/ &2 * k + &1 IN ss \/ &2 * k + &2 IN ss}` THEN
  SUBGOAL_THEN `FINITE (tt:int->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\k:int. &2 * k`; `ss:int->bool`] FINITE_IMAGE_INJ) THEN
    MP_TAC(ISPECL [`\k:int. &2 * k + &1`; `ss:int->bool`] FINITE_IMAGE_INJ) THEN
    MP_TAC(ISPECL [`\k:int. &2 * k + &2`; `ss:int->bool`] FINITE_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[INT_ARITH `!x y:int. &2 * x = &2 * y <=> x = y`;
                    INT_ARITH `!x y:int. &2 * x + &1 = &2 * y + &1 <=> x = y`;
                    INT_ARITH `!x y:int. &2 * x + &2 = &2 * y + &2 <=> x = y`] THEN
    REPEAT DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{k:int | &2 * k IN ss} UNION {k:int | &2 * k + &1 IN ss} UNION
                {k:int | &2 * k + &2 IN ss}` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[FINITE_UNION];
      EXPAND_TAC "tt" THEN REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `zz = UNIONS ({(hh:int->real^3->bool) k | k | k IN tt /\ ~((q:real^3) IN hh k)}
                           UNION
                           {(bb:int->real^3->bool) k | k | k IN tt /\ ~((q:real^3) IN bb k)})` THEN
  SUBGOAL_THEN `compact (zz:real^3->bool) /\ ~((q:real^3) IN zz)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zz" THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_UNION_IMP THEN CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THENL
         [EXISTS_TAC `IMAGE (hh:int->real^3->bool) tt`;
          EXISTS_TAC `IMAGE (bb:int->real^3->bool) tt`] THEN
        ASM_SIMP_TAC[FINITE_IMAGE] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
        REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_GSPEC] THEN ASM_SIMP_TAC[]];
      REWRITE_TAC[IN_UNIONS; IN_UNION; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
      UNDISCH_TAC `(q:real^3) IN t` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`zz:real^3->bool`; `q:real^3`] SEPARATE_POINT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open (o0:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  SUBGOAL_THEN `ball(q:real^3,min d1 d2) SUBSET o0` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(q:real^3,d2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:real^3) IN o0` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?k. (x:real^3) IN (hh:int->real^3->bool) k \/ x IN (bb:int->real^3->bool) k`
  (X_CHOOSE_THEN `k:int` ASSUME_TAC) THENL
   [UNDISCH_TAC `(x:real^3) IN moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim` THEN
    REWRITE_TAC[moi_s32_chainset; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_UNIV; IN_SING] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `i:int` THEN UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[IN_UNION];
      UNDISCH_TAC `~((g:real^3->real^3) (vec 0) IN IMAGE g v)` THEN
      UNDISCH_TAC `o0 SUBSET IMAGE (g:real^3->real^3) v` THEN
      UNDISCH_TAC `(x:real^3) IN o0` THEN UNDISCH_TAC `x = (g:real^3->real^3) (vec 0)` THEN
      SET_TAC[];
      UNDISCH_TAC `DISJOINT (IMAGE (g:real^3->real^3) v) (IMAGE g moi_s32_rim)` THEN
      UNDISCH_TAC `o0 SUBSET IMAGE (g:real^3->real^3) v` THEN
      UNDISCH_TAC `(x:real^3) IN o0` THEN
      UNDISCH_TAC `(x:real^3) IN IMAGE (g:real^3->real^3) moi_s32_rim` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:int) IN tt` ASSUME_TAC THENL
   [EXPAND_TAC "tt" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [DISJ1_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> t = `o0:real^3->bool`)) (concl th))) THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `k:int` (ASSUME `!i. (hh:int->real^3->bool) i SUBSET
        IMAGE (g:real^3->real^3) (revolution ((dd:int->real^3->bool) (&2 * i)))`)) THEN
      UNDISCH_TAC `(x:real^3) IN (hh:int->real^3->bool) k` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s32_lvl g dd k` MP_TAC THENL
     [MP_TAC(ASSUME `moi_s32_chain (g:real^3->real^3) dd s2 hh bb jl jh`) THEN
      REWRITE_TAC[moi_s32_chain] THEN
      DISCH_THEN(MP_TAC o SPEC `k:int` o CONJUNCT1) THEN STRIP_TAC THEN
      UNDISCH_TAC `(bb:int->real^3->bool) k SUBSET moi_s32_lvl g dd k` THEN
      UNDISCH_TAC `(x:real^3) IN (bb:int->real^3->bool) k` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_s32_lvl; IN_UNION] THEN STRIP_TAC THENL
     [DISJ1_TAC; DISJ2_TAC THEN DISJ1_TAC; DISJ2_TAC THEN DISJ2_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `o0:real^3->bool`)) (concl th))) THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN zz ==> ~(z IN ball(q,min d1 d2))` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `d1:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
   [ASM_CASES_TAC `(q:real^3) IN (hh:int->real^3->bool) k` THENL
     [UNDISCH_TAC `(x:real^3) IN (hh:int->real^3->bool) k` THEN
      MP_TAC(MP (SPEC `k:int` (ASSUME `!k. (q:real^3) IN (hh:int->real^3->bool) k
                                            ==> hh k SUBSET y`))
                (ASSUME `(q:real^3) IN (hh:int->real^3->bool) k`)) THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN zz` MP_TAC THENL
     [EXPAND_TAC "zz" THEN REWRITE_TAC[IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN
      EXISTS_TAC `(hh:int->real^3->bool) k` THEN ASM_REWRITE_TAC[] THEN
      DISJ1_TAC THEN EXISTS_TAC `k:int` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ASM_CASES_TAC `(q:real^3) IN (bb:int->real^3->bool) k` THENL
     [UNDISCH_TAC `(x:real^3) IN (bb:int->real^3->bool) k` THEN
      MP_TAC(MP (SPEC `k:int` (ASSUME `!k. (q:real^3) IN (bb:int->real^3->bool) k
                                            ==> bb k SUBSET y`))
                (ASSUME `(q:real^3) IN (bb:int->real^3->bool) k`)) THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN zz` MP_TAC THENL
     [EXPAND_TAC "zz" THEN REWRITE_TAC[IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN
      EXISTS_TAC `(bb:int->real^3->bool) k` THEN ASM_REWRITE_TAC[] THEN
      DISJ2_TAC THEN EXISTS_TAC `k:int` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]]]);;

(* The local two sides at every point of the chain other than the centre.  *)

let MOI_S3SS_LOCAL_SIDES = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh q.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh /\
     q IN moi_s32_chainset g hh bb /\ ~(q = g (vec 0))
     ==> ?r e1 e2. &0 < r /\ ball(q,r) SUBSET moi_s32_open g /\
                   connected e1 /\ connected e2 /\ ~(e1 = {}) /\ ~(e2 = {}) /\
                   DISJOINT e1 e2 /\
                   ball(q,r) DIFF (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim) =
                   e1 UNION e2 /\
                   (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim) INTER ball(q,r)
                   SUBSET closure e1 INTER closure e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`;
                 `q:real^3`] MOI_S3SS_CLASSIFY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`;
                 `q:real^3`; `y:real^3->bool`] MOI_S3SS_LOCFIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`y:real^3->bool`; `q:real^3`] MOI_S3SS_MODEL_CONE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `min rho r0 / &2`))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min rho r0 / &2` THEN
  SUBGOAL_THEN `&0 < r /\ ball(q:real^3,r) SUBSET ball(q,rho)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim) INTER ball(q:real^3,r) =
                {q + t % (z - q) | t,z | z IN c /\ &0 <= t /\ t < &1}` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `c:real^3->bool`)) (concl th))) THEN
    UNDISCH_TAC `(moi_s32_chainset g hh bb UNION IMAGE (g:real^3->real^3) moi_s32_rim) INTER
                 ball(q,rho) = y INTER ball(q,rho)` THEN
    UNDISCH_TAC `ball(q:real^3,r) SUBSET ball(q,rho)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3`; `r:real`; `c:real^3->bool`;
                 `moi_s32_chainset g hh bb UNION IMAGE (g:real^3->real^3) moi_s32_rim`]
    MOI_CSD_CONE_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3->bool` (X_CHOOSE_THEN `e2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `e1:real^3->bool`; `e2:real^3->bool`] THEN
  ASM_REWRITE_TAC[SUBSET_INTER] THEN ASM_MESON_TAC[SUBSET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* 6. The model cylinder from the inside: convex, the closure of its        *)
(* interior; the lower and upper hemispheres minus the rim are connected.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SS_CYL_CONVEX = prove
 (`convex moi_s32_cyl /\ convex (interior moi_s32_cyl)`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[CONVEX_INTERIOR]] THEN
  REWRITE_TAC[MOI_S3GF_CYL_EQ] THEN
  REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
  REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LE; CONVEX_HALFSPACE_COMPONENT_GE] THEN
  SUBGOAL_THEN `{x:real^3 | x$1 pow 2 + x$3 pow 2 <= &1} =
                {x | (\x:real^3. vector[x$1; x$3]:real^2) x IN cball(vec 0,&1)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_CBALL_0; NORM_LE_SQUARE; DOT_2; VECTOR_2] THEN
    GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CONVEX_LINEAR_PREIMAGE THEN REWRITE_TAC[CONVEX_CBALL] THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MOI_S3SS_CYL_CLOSURE = prove
 (`closure(interior moi_s32_cyl) = moi_s32_cyl /\
   (!y d. y IN moi_s32_cyl /\ &0 < d ==> ~(interior moi_s32_cyl INTER ball(y,d) = {}))`,
  SUBGOAL_THEN `closure(interior moi_s32_cyl) = moi_s32_cyl` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_s32_cyl` CONVEX_CLOSURE_INTERIOR) THEN
    REWRITE_TAC[MOI_S3SS_CYL_CONVEX; MATCH_MP CLOSURE_CLOSED MOI_S3GF_CYL_CLOSED] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `vec 0:real^3` THEN REWRITE_TAC[MOI_S3GF_MODEL_POINTS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN closure(interior moi_s32_cyl)` MP_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN EXISTS_TAC `z:real^3` THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_S3SS_L0_IN = prove
 (`!x:real^3. x IN moi_s32_lohemi DIFF moi_s32_rim <=>
              x$1 pow 2 + x$3 pow 2 <= &1 /\ -- &1 <= x$2 /\ x$2 < &0 /\
              (x$1 pow 2 + x$3 pow 2 = &1 \/ x$2 = -- &1)`,
  REWRITE_TAC[moi_s32_lohemi; moi_s32_rim; moi_s32_disk; moi_s32_lo; moi_s32_cyl;
              IN_DIFF; IN_ELIM_THM] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3SS_H0_IN = prove
 (`!x:real^3. x IN moi_s32_hihemi DIFF moi_s32_rim <=>
              x$1 pow 2 + x$3 pow 2 <= &1 /\ &0 < x$2 /\ x$2 <= &1 /\
              (x$1 pow 2 + x$3 pow 2 = &1 \/ x$2 = &1)`,
  REWRITE_TAC[moi_s32_hihemi; moi_s32_rim; moi_s32_disk; moi_s32_hi; moi_s32_cyl;
              IN_DIFF; IN_ELIM_THM] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3SS_L0_SEG1 = prove
 (`!x:real^3 u. x IN moi_s32_lohemi DIFF moi_s32_rim /\ &0 <= u /\ u <= &1
                ==> (&1 - u) % x + u % vector[x$1; -- &1; x$3] IN
                    moi_s32_lohemi DIFF moi_s32_rim`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_S3SS_L0_IN; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= u * (&1 + (x:real^3)$2) /\ &0 <= (&1 + x$2) * (&1 - u)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((&1 - u) * (x:real^3)$1 + u * x$1) pow 2 +
                ((&1 - u) * x$3 + u * x$3) pow 2 = x$1 pow 2 + x$3 pow 2`
  SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S3SS_L0_SEG2 = prove
 (`!x:real^3 u. x IN moi_s32_lohemi DIFF moi_s32_rim /\ &0 <= u /\ u <= &1
                ==> (&1 - u) % vector[x$1; -- &1; x$3] + u % vector[&0; -- &1; &0] IN
                    moi_s32_lohemi DIFF moi_s32_rim`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_S3SS_L0_IN; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_3] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(&1 - u) pow 2 * ((x:real^3)$1 pow 2 + x$3 pow 2) <= &1 * &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 - u) * (x:real^3)$1 + u * &0) pow 2 +
                ((&1 - u) * x$3 + u * &0) pow 2 =
                (&1 - u) pow 2 * (x$1 pow 2 + x$3 pow 2)`
  SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let MOI_S3SS_L0_CONNECTED = prove
 (`connected (moi_s32_lohemi DIFF moi_s32_rim)`,
  SUBGOAL_THEN
   `moi_s32_lohemi DIFF moi_s32_rim =
    UNIONS {segment[x,vector[x$1; -- &1; x$3]] UNION
            segment[vector[x$1; -- &1; x$3],vector[&0; -- &1; &0]] |
            x | x IN moi_s32_lohemi DIFF moi_s32_rim}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      EXISTS_TAC `segment[x,vector[x$1; -- &1; x$3]] UNION
                  segment[vector[x$1; -- &1; x$3],vector[&0; -- &1; &0]:real^3]` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT]];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; UNION_SUBSET] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[SUBSET; IN_SEGMENT] THEN CONJ_TAC THEN
      X_GEN_TAC `p:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[MOI_S3SS_L0_SEG1; MOI_S3SS_L0_SEG2]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CONNECTED_UNION THEN
    REWRITE_TAC[CONNECTED_SEGMENT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `vector[(x:real^3)$1; -- &1; x$3]:real^3` THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTERS; FORALL_IN_GSPEC] THEN
    EXISTS_TAC `vector[&0; -- &1; &0]:real^3` THEN REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT]]);;

let MOI_S3SS_H0_CONNECTED = prove
 (`connected (moi_s32_hihemi DIFF moi_s32_rim)`,
  SUBGOAL_THEN `moi_s32_hihemi DIFF moi_s32_rim =
                IMAGE (\x:real^3. vector[x$1; --(x$2); x$3])
                      (moi_s32_lohemi DIFF moi_s32_rim)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; MOI_S3SS_L0_IN; MOI_S3SS_H0_IN] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `vector[(y:real^3)$1; --(y$2); y$3]:real^3` THEN
      REWRITE_TAC[VECTOR_3; CART_EQ; DIMINDEX_3; FORALL_3; REAL_NEG_NEG] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_S3SS_L0_CONNECTED] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 7. The separation of B DIFF P by the hemispheres.  B DIFF P is M DIFF C  *)
(* together with the images of the two hemispheres minus the rim.  Near a   *)
(* point of the lower hemisphere the interior points of B lie on one side   *)
(* of the chain separation, the same side all along the hemisphere, which  *)
(* is the side of g qlo (the axis below qlo); similarly for the upper one.  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SS_CONN_SPLIT = prove
 (`!(m:real^N->bool) u w s.
     open_in (subtopology euclidean m) u /\ open_in (subtopology euclidean m) w /\
     DISJOINT u w /\ connected s /\ s SUBSET u UNION w /\ s SUBSET m
     ==> s SUBSET u \/ s SUBSET w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `t2:real^N->bool` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `connected (s:real^N->bool)` THEN
  REWRITE_TAC[CONNECTED_OPEN_IN; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`s INTER t1:real^N->bool`; `s INTER t2:real^N->bool`]) THEN
  ASM_SIMP_TAC[OPEN_IN_OPEN_INTER] THEN ASM SET_TAC[]);;

let MOI_S3SS_DISJOINT_IMAGE_INJ = prove
 (`!(g:real^3->real^3) s a b.
     (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\ a SUBSET s /\ b SUBSET s /\
     DISJOINT a b
     ==> DISJOINT (IMAGE g a) (IMAGE g b)`,
  SET_TAC[]);;

let MOI_S3SS_DECOMP_SET = prove
 (`!(g:real^3->real^3) i lo hi rim c.
     (!x y. x IN i UNION lo UNION hi /\ y IN i UNION lo UNION hi /\ g x = g y ==> x = y) /\
     lo INTER hi = rim /\ DISJOINT i (lo UNION hi) /\ c SUBSET IMAGE g i
     ==> IMAGE g (i UNION lo UNION hi) DIFF (c UNION IMAGE g rim) =
         (IMAGE g i DIFF c) UNION IMAGE g (lo DIFF rim) UNION IMAGE g (hi DIFF rim) /\
         DISJOINT (IMAGE g i) (IMAGE g (lo DIFF rim)) /\
         DISJOINT (IMAGE g i) (IMAGE g (hi DIFF rim)) /\
         DISJOINT (IMAGE g (lo DIFF rim)) (IMAGE g (hi DIFF rim))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b. a SUBSET i UNION lo UNION hi /\ b SUBSET i UNION lo UNION hi /\
                      DISJOINT a b ==> DISJOINT (IMAGE (g:real^3->real^3) a) (IMAGE g b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3SS_DISJOINT_IMAGE_INJ THEN
    EXISTS_TAC `i UNION lo UNION hi:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (g:real^3->real^3) i) (IMAGE g (lo DIFF rim)) /\
    DISJOINT (IMAGE (g:real^3->real^3) i) (IMAGE g (hi DIFF rim)) /\
    DISJOINT (IMAGE (g:real^3->real^3) (lo DIFF rim)) (IMAGE g (hi DIFF rim)) /\
    DISJOINT (IMAGE (g:real^3->real^3) i) (IMAGE g rim) /\
    DISJOINT (IMAGE (g:real^3->real^3) (lo DIFF rim)) (IMAGE g rim) /\
    DISJOINT (IMAGE (g:real^3->real^3) (hi DIFF rim)) (IMAGE g rim)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `lo INTER hi = (rim:real^3->bool)` THEN
    UNDISCH_TAC `DISJOINT (i:real^3->bool) (lo UNION hi)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SET_TAC[];
    UNDISCH_TAC `DISJOINT (IMAGE (g:real^3->real^3) i) (IMAGE g (lo DIFF rim))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (g:real^3->real^3) i) (IMAGE g (hi DIFF rim))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (g:real^3->real^3) i) (IMAGE g rim)` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (g:real^3->real^3) (lo DIFF rim)) (IMAGE g rim)` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (g:real^3->real^3) (hi DIFF rim)) (IMAGE g rim)` THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET IMAGE (g:real^3->real^3) i` THEN
    SET_TAC[]]);;

let MOI_S3SS_DECOMP = prove
 (`!(g:real^3->real^3) v c.
     moi_s32_model g v /\ c SUBSET moi_s32_open g
     ==> IMAGE g moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim) =
         (moi_s32_open g DIFF c) UNION IMAGE g (moi_s32_lohemi DIFF moi_s32_rim) UNION
         IMAGE g (moi_s32_hihemi DIFF moi_s32_rim) /\
         DISJOINT (moi_s32_open g) (IMAGE g (moi_s32_lohemi DIFF moi_s32_rim)) /\
         DISJOINT (moi_s32_open g) (IMAGE g (moi_s32_hihemi DIFF moi_s32_rim)) /\
         DISJOINT (IMAGE g (moi_s32_lohemi DIFF moi_s32_rim))
                  (IMAGE g (moi_s32_hihemi DIFF moi_s32_rim))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_S3GF_MODEL_OPEN) THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_model] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "moi_s32_model"
                                              with Failure _ -> false)) (concl th))) THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s32_cyl = interior moi_s32_cyl UNION moi_s32_lohemi UNION moi_s32_hihemi`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_S3GF_FRONTIER_CYL] THEN
    MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN
    REWRITE_TAC[frontier; MATCH_MP CLOSURE_CLOSED MOI_S3GF_CYL_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `interior moi_s32_cyl`; `moi_s32_lohemi`;
                 `moi_s32_hihemi`; `moi_s32_rim`; `c:real^3->bool`] MOI_S3SS_DECOMP_SET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_S3GF_HEMI_INTER] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `moi_s32_cyl`)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM MOI_S3GF_FRONTIER_CYL] THEN
      UNDISCH_TAC `frontier moi_s32_cyl INTER interior moi_s32_cyl = {}` THEN SET_TAC[];
      UNDISCH_TAC `c SUBSET moi_s32_open g` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_s32_cyl`)) THEN
  SIMP_TAC[]);;

let MOI_S3SS_HEMI_NBHD = prove
 (`!(g:real^3->real^3) v p y.
     moi_s32_model g v /\ closed p /\ p SUBSET moi_s32_open g UNION IMAGE g moi_s32_rim /\
     y IN (moi_s32_lohemi DIFF moi_s32_rim) UNION (moi_s32_hihemi DIFF moi_s32_rim)
     ==> ?d. &0 < d /\ IMAGE g (moi_s32_cyl INTER ball(y,d)) INTER p = {} /\
             (y IN moi_s32_lohemi DIFF moi_s32_rim
              ==> moi_s32_cyl INTER ball(y,d) INTER moi_s32_hihemi = {}) /\
             (y IN moi_s32_hihemi DIFF moi_s32_rim
              ==> moi_s32_cyl INTER ball(y,d) INTER moi_s32_lohemi = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3GF_MODEL_BD_INTERIOR) THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_model] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "moi_s32_model"
                                              with Failure _ -> false)) (concl th))) THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN frontier moi_s32_cyl /\ ~(y IN moi_s32_rim)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN (moi_s32_lohemi DIFF moi_s32_rim) UNION
                               (moi_s32_hihemi DIFF moi_s32_rim)` THEN
    UNDISCH_TAC `moi_s32_lohemi SUBSET frontier moi_s32_cyl` THEN
    UNDISCH_TAC `moi_s32_hihemi SUBSET frontier moi_s32_cyl` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s32_cyl` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((g:real^3->real^3) y IN p)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^3) y IN moi_s32_open g UNION IMAGE g moi_s32_rim` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION; moi_s32_open] THEN STRIP_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^3->real^3) (frontier moi_s32_cyl) INTER
                   interior (IMAGE g moi_s32_cyl) = {}` THEN
      UNDISCH_TAC `(g:real^3->real^3) y IN interior (IMAGE g moi_s32_cyl)` THEN
      UNDISCH_TAC `(y:real^3) IN frontier moi_s32_cyl` THEN SET_TAC[];
      UNDISCH_TAC `(g:real^3->real^3) y IN IMAGE g moi_s32_rim` THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `y:real^3 = z` (fun th -> ASM_MESON_TAC[th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `moi_s32_cyl`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_s32_rim SUBSET frontier moi_s32_cyl` THEN
      UNDISCH_TAC `frontier moi_s32_cyl SUBSET moi_s32_cyl` THEN
      UNDISCH_TAC `(z:real^3) IN moi_s32_rim` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `moi_s32_cyl`; `p:real^3->bool`]
    CONTINUOUS_CLOSED_PREIMAGE) THEN
  ASM_REWRITE_TAC[MOI_S3GF_CYL_CLOSED] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{x | x IN moi_s32_cyl /\ (g:real^3->real^3) x IN p}`; `y:real^3`]
    SEPARATE_POINT_CLOSED) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < abs((y:real^3)$2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN (moi_s32_lohemi DIFF moi_s32_rim) UNION
                               (moi_s32_hihemi DIFF moi_s32_rim)` THEN
    REWRITE_TAC[IN_UNION; MOI_S3SS_L0_IN; MOI_S3SS_H0_IN] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min d1 (abs((y:real^3)$2))` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  SUBGOAL_THEN `!z:real^3. z IN ball(y,min d1 (abs(y$2)))
                           ==> dist(y,z) < d1 /\ abs(z$2 - y$2) < abs(y$2)` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `dist(y:real^3,z)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[GSYM REAL_ABS_NEG] THEN
    REWRITE_TAC[REAL_NEG_SUB; GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN X_GEN_TAC `w:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `d1:real`)) (concl th))) THEN
    ASM_MESON_TAC[REAL_NOT_LE];
    REWRITE_TAC[MOI_S3SS_L0_IN] THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; moi_s32_hihemi; moi_s32_hi; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[MOI_S3SS_H0_IN] THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; moi_s32_lohemi; moi_s32_lo; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The side is constant along a connected set of boundary points.          *)

let MOI_S3SS_SIDE_CONST = prove
 (`!(g:real^3->real^3) l p u w b.
     g continuous_on moi_s32_cyl /\
     connected l /\ l SUBSET moi_s32_cyl /\ b IN l /\
     (!y. y IN l ==> ?d. &0 < d /\ IMAGE g (moi_s32_cyl INTER ball(y,d)) INTER p = {}) /\
     open_in (subtopology euclidean (IMAGE g (interior moi_s32_cyl))) u /\
     open_in (subtopology euclidean (IMAGE g (interior moi_s32_cyl))) w /\
     DISJOINT u w /\ IMAGE g (interior moi_s32_cyl) DIFF p SUBSET u UNION w /\
     (?d. &0 < d /\ IMAGE g (moi_s32_cyl INTER ball(b,d)) INTER p = {} /\
          ~(IMAGE g (interior moi_s32_cyl INTER ball(b,d)) INTER u = {}))
     ==> !y. y IN l
             ==> ?d. &0 < d /\ IMAGE g (moi_s32_cyl INTER ball(y,d)) INTER p = {} /\
                     IMAGE g (interior moi_s32_cyl INTER ball(y,d)) SUBSET u`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN
   `!y d. y IN moi_s32_cyl /\ &0 < d
          ==> connected (IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(y,d))) /\
              ~(IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(y,d)) = {})`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
        ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN SET_TAC[];
        MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[MOI_S3SS_CYL_CONVEX; CONVEX_BALL]];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_SIMP_TAC[MOI_S3SS_CYL_CLOSURE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y d. y IN moi_s32_cyl /\ &0 < d /\
          IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) INTER p = {}
          ==> IMAGE g (interior moi_s32_cyl INTER ball(y,d)) SUBSET u \/
              IMAGE g (interior moi_s32_cyl INTER ball(y,d)) SUBSET w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3SS_CONN_SPLIT THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) (interior moi_s32_cyl)` THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (g:real^3->real^3) (interior moi_s32_cyl) DIFF p SUBSET u UNION w` THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) INTER p = {}` THEN
      MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN SET_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `lu = {y | y IN l /\
                        ?d. &0 < d /\
                            IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) INTER p = {} /\
                            IMAGE g (interior moi_s32_cyl INTER ball(y,d)) SUBSET u}` THEN
  ABBREV_TAC `lw = {y | y IN l /\
                        ?d. &0 < d /\
                            IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) INTER p = {} /\
                            IMAGE g (interior moi_s32_cyl INTER ball(y,d)) SUBSET w}` THEN
  SUBGOAL_THEN `!y d d'. &0 < d' /\ d' <= d /\
                         IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) INTER p = {}
                         ==> IMAGE g (moi_s32_cyl INTER ball(y,d')) INTER p = {} /\
                             IMAGE g (interior moi_s32_cyl INTER ball(y,d')) SUBSET
                             IMAGE g (interior moi_s32_cyl INTER ball(y,d))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^3`; `d':real`; `d:real`] SUBSET_BALL) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC
     `IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) INTER p = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean l) (lu:real^3->bool) /\
                open_in (subtopology euclidean l) (lw:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN MAP_EVERY EXPAND_TAC ["lu"; "lw"] THEN
    REWRITE_TAC[SUBSET_RESTRICT; IN_ELIM_THM] THEN CONJ_TAC THEN
    (X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `d / &2` THEN
    REWRITE_TAC[REAL_HALF; SUBSET; IN_INTER; IN_ELIM_THM; IN_BALL] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    SUBGOAL_THEN `ball(z:real^3,d / &2) SUBSET ball(y,d)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL] THEN UNDISCH_TAC `dist(y:real^3,z) < d / &2` THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SUBSET] THEN
    (CONJ_TAC THENL
      [UNDISCH_TAC `IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) INTER p = {}` THEN
       UNDISCH_TAC `ball(z:real^3,d / &2) SUBSET ball(y,d)` THEN SET_TAC[];
       MATCH_MP_TAC SUBSET_TRANS THEN
       EXISTS_TAC `IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(y,d))` THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
       UNDISCH_TAC `ball(z:real^3,d / &2) SUBSET ball(y,d)` THEN SET_TAC[]]));
    ALL_TAC] THEN
  SUBGOAL_THEN `lu UNION lw = (l:real^3->bool)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["lu"; "lw"] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    ASM_CASES_TAC `(y:real^3) IN l` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `l:real^3->bool`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `d:real`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `w:real^3->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lu INTER lw = {}:real^3->bool` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["lu"; "lw"] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s32_cyl` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`; `min d1 d2`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      not(can (find_term (fun t -> t = `p:real^3->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`y:real^3`; `min d1 d2`; `d1:real`] SUBSET_BALL) THEN
    MP_TAC(ISPECL [`y:real^3`; `min d1 d2`; `d2:real`] SUBSET_BALL) THEN
    REWRITE_TAC[REAL_MIN_MIN] THEN REPEAT DISCH_TAC THEN
    UNDISCH_TAC `~(IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(y,min d1 d2)) = {})` THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(y,d1)) SUBSET u` THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(y,d2)) SUBSET w` THEN
    UNDISCH_TAC `DISJOINT (u:real^3->bool) w` THEN
    UNDISCH_TAC `ball(y:real^3,min d1 d2) SUBSET ball(y,d1)` THEN
    UNDISCH_TAC `ball(y:real^3,min d1 d2) SUBSET ball(y,d2)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^3) IN lu` ASSUME_TAC THENL
   [EXPAND_TAC "lu" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o check (fun th ->
      is_exists(concl th))) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`b:real^3`; `d:real`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `w:real^3->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(b,d)) INTER u = {})` THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(b,d)) SUBSET w` THEN
    UNDISCH_TAC `DISJOINT (u:real^3->bool) w` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lw = {}:real^3->bool` ASSUME_TAC THENL
   [UNDISCH_TAC `connected (l:real^3->bool)` THEN
    REWRITE_TAC[CONNECTED_OPEN_IN_EQ; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`lu:real^3->bool`; `lw:real^3->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN lu` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "lu" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 8. Generic facts for the global argument: a punctured open disk is      *)
(* connected and has the puncture in its closure; the punctured open set M  *)
(* is connected; the components of B DIFF P are open in it.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SS_PUNCT = prove
 (`!(c:real^3->bool) c0.
     c homeomorphic ball(vec 0:real^2,&1) /\ c0 IN c
     ==> connected (c DELETE c0) /\ c0 IN closure (c DELETE c0) /\ ~(c DELETE c0 = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:real^3->real^2`
    (X_CHOOSE_TAC `h:real^2->real^3`)) ASSUME_TAC) THEN
  SUBGOAL_THEN `(c0:real^3) IN closure (c DELETE c0)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `open_in (subtopology euclidean c) {c0:real^3}` MP_TAC THENL
     [UNDISCH_TAC `~((c0:real^3) IN closure (c DELETE c0))` THEN
      REWRITE_TAC[CLOSURE_APPROACHABLE; NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `ball(c0:real^3,e)` THEN
      REWRITE_TAC[OPEN_BALL; EXTENSION; IN_INTER; IN_SING; IN_BALL] THEN
      X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
       [DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[DIST_REFL]; ALL_TAC] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^3->real^2`; `h:real^2->real^3`; `c:real^3->bool`;
                   `ball(vec 0:real^2,&1)`; `{c0:real^3}`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN DISCH_TAC THEN
    SUBGOAL_THEN `open {(f:real^3->real^2) c0}` MP_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[NOT_OPEN_SING]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `homeomorphism (c,ball(vec 0:real^2,&1))
                   ((f:real^3->real^2),(h:real^2->real^3))` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c:real^3->bool) DELETE c0 =
                  IMAGE (h:real^2->real^3) (ball(vec 0,&1) DELETE f c0)` SUBST1_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^2->real^3) (ball(vec 0,&1)) = c` THEN
      UNDISCH_TAC `IMAGE (f:real^3->real^2) c = ball(vec 0,&1)` THEN
      UNDISCH_TAC `!x. x IN c ==> (h:real^2->real^3) ((f:real^3->real^2) x) = x` THEN
      UNDISCH_TAC `!y. y IN ball(vec 0,&1) ==> (f:real^3->real^2) ((h:real^2->real^3) y) = y` THEN
      UNDISCH_TAC `(c0:real^3) IN c` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[DELETE_SUBSET];
      MATCH_MP_TAC CONNECTED_OPEN_DELETE THEN
      REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; DIMINDEX_2; LE_REFL]];
    DISCH_TAC THEN UNDISCH_TAC `(c0:real^3) IN closure (c DELETE c0)` THEN
    ASM_REWRITE_TAC[CLOSURE_EMPTY; NOT_IN_EMPTY]]);;

let MOI_S3SS_M_CONNECTED = prove
 (`!(g:real^3->real^3) v z.
     moi_s32_model g v
     ==> open (moi_s32_open g) /\ connected (moi_s32_open g) /\
         connected (moi_s32_open g DELETE z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3GF_MODEL_OPEN) THEN
  SUBGOAL_THEN `connected (moi_s32_open (g:real^3->real^3))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
      REWRITE_TAC[INTERIOR_SUBSET] THEN ASM_MESON_TAC[moi_s32_model];
      MATCH_MP_TAC CONVEX_CONNECTED THEN REWRITE_TAC[MOI_S3SS_CYL_CONVEX]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC CONNECTED_OPEN_DELETE THEN
  REWRITE_TAC[DIMINDEX_3; ARITH] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

let MOI_S3SS_COMPONENTS_OPEN = prove
 (`!(g:real^3->real^3) v p k.
     moi_s32_model g v /\ closed p /\
     k IN components (IMAGE g moi_s32_cyl DIFF p)
     ==> open_in (subtopology euclidean (IMAGE g moi_s32_cyl DIFF p)) k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_COMPONENTS_LOCALLY_CONNECTED THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_OPEN_SUBSET THEN
  EXISTS_TAC `IMAGE (g:real^3->real^3) moi_s32_cyl` THEN CONJ_TAC THENL
   [FIRST_ASSUM(X_CHOOSE_TAC `g':real^3->real^3` o MATCH_MP MOI_S3GF_MODEL_HOMEO) THEN
    MP_TAC(ISPECL [`moi_s32_cyl`; `IMAGE (g:real^3->real^3) moi_s32_cyl`]
      HOMEOMORPHIC_LOCAL_CONNECTEDNESS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `g':real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CONVEX_IMP_LOCALLY_CONNECTED THEN
      REWRITE_TAC[MOI_S3SS_CYL_CONVEX]];
    REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `(:real^3) DIFF p` THEN
    ASM_REWRITE_TAC[GSYM closed] THEN SET_TAC[]]);;

(* The axis below qlo (above qhi) joins g qlo (g qhi) to interior points of *)
(* B near the bottom (top) centre inside M DIFF C.                         *)

let MOI_S3SS_AXIS_BOUND = prove
 (`!t s. &0 <= t /\ t <= &1 /\ &0 < s /\ s <= &1 / &4
         ==> &0 < (&1 - t) / &2 + t * (&1 - s) /\ (&1 - t) / &2 + t * (&1 - s) < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 / &4 - s) * t /\ &0 <= (&1 / &2 - s) * (&1 - t)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S3SS_AXIS_SIDE = prove
 (`!(g:real^3->real^3) v c u w sg d.
     moi_s32_model g v /\ c SUBSET g (vec 0) INSERT IMAGE g v /\
     open_in (subtopology euclidean (moi_s32_open g)) u /\
     open_in (subtopology euclidean (moi_s32_open g)) w /\ DISJOINT u w /\
     moi_s32_open g DIFF c SUBSET u UNION w /\
     (sg = &1 \/ sg = -- &1) /\ g (vector[&0; sg / &2; &0]) IN u /\ &0 < d
     ==> ~(IMAGE g (interior moi_s32_cyl INTER ball(vector[&0; sg; &0],d)) INTER u = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN (
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3GF_MODEL_OPEN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_model] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "moi_s32_model"
                                              with Failure _ -> false)) (concl th))) THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  ABBREV_TAC `s = min (d / &2) (&1 / &4)` THEN
  SUBGOAL_THEN `&0 < s /\ s <= &1 / &4 /\ s < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= &1
                    ==> (&1 - t) % vector[&0; sg / &2; &0] +
                        t % vector[&0; sg * (&1 - s); &0] =
                        vector[&0; sg * ((&1 - t) / &2 + t * (&1 - s)); &0]:real^3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. &0 < a /\ a < &1
                    ==> vector[&0; sg * a; &0]:real^3 IN interior moi_s32_cyl /\
                        vector[&0; sg * a; &0]:real^3 IN moi_s32_axis /\
                        ~(vector[&0; sg * a; &0]:real^3 = vec 0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[MOI_S3GF_INTERIOR_CYL; moi_s32_axis; IN_ELIM_THM; VECTOR_3; CART_EQ;
                DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `sg:real`)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `seg = segment[vector[&0; sg / &2; &0],vector[&0; sg * (&1 - s); &0]:real^3]` THEN
  SUBGOAL_THEN `!x:real^3. x IN seg
                           ==> x IN interior moi_s32_cyl /\ x IN moi_s32_axis /\
                               ~(x = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "seg" THEN REWRITE_TAC[IN_SEGMENT] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^3 = vector[&0; sg * ((&1 - t) / &2 + t * (&1 - s)); &0]`
    SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `moi_s32_axis`)) (concl th))) THEN
    MATCH_MP_TAC MOI_S3SS_AXIS_BOUND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) seg SUBSET u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s32_open (g:real^3->real^3)`; `u:real^3->bool`; `w:real^3->bool`;
                   `IMAGE (g:real^3->real^3) seg`] MOI_S3SS_CONN_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN EXPAND_TAC "seg" THEN
        REWRITE_TAC[CONNECTED_SEGMENT] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `moi_s32_cyl` THEN ASM_REWRITE_TAC[] THEN
        EXPAND_TAC "seg" THEN ASM SET_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `moi_s32_open (g:real^3->real^3) DIFF c` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
        DISCH_TAC THEN CONJ_TAC THENL
         [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `(g:real^3->real^3) x IN g (vec 0) INSERT IMAGE g v` MP_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN STRIP_TAC THENL
         [SUBGOAL_THEN `x:real^3 = vec 0` (fun th -> ASM_MESON_TAC[th]) THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> t = `moi_s32_cyl`)) (concl th) &&
            length(fst(strip_forall(concl th))) = 2)) THEN
          ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[SUBSET; MOI_S3GF_MODEL_POINTS]];
          SUBGOAL_THEN `x:real^3 = x'` SUBST_ALL_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
              can (find_term (fun t -> t = `moi_s32_cyl`)) (concl th) &&
              length(fst(strip_forall(concl th))) = 2)) THEN
            ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
            UNDISCH_TAC `DISJOINT (v:real^3->bool) moi_s32_axis` THEN ASM SET_TAC[]]];
        EXPAND_TAC "seg" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^3) (vector[&0; sg / &2; &0]) IN IMAGE g seg` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN EXPAND_TAC "seg" THEN REWRITE_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) seg SUBSET w` THEN
    UNDISCH_TAC `(g:real^3->real^3) (vector[&0; sg / &2; &0]) IN u` THEN
    UNDISCH_TAC `DISJOINT (u:real^3->bool) w` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `(g:real^3->real^3) (vector[&0; sg * (&1 - s); &0])` THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `&1 - s` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `moi_s32_axis`)) (concl th) &&
        not(can (find_term (fun t -> t = `seg:real^3->bool`)) (concl th)))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      REWRITE_TAC[IN_BALL; dist; NORM_LT_SQUARE; DOT_3; VECTOR_SUB_COMPONENT; VECTOR_3] THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) && lhs(concl th) = `sg:real`)) THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `s * s < d * d` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    SUBGOAL_THEN `(g:real^3->real^3) (vector[&0; sg * (&1 - s); &0]) IN IMAGE g seg`
    MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN EXPAND_TAC "seg" THEN REWRITE_TAC[ENDS_IN_SEGMENT];
      UNDISCH_TAC `IMAGE (g:real^3->real^3) seg SUBSET u` THEN SET_TAC[]]]));;

(* Near a hemisphere point the interior side is the side of the hemisphere. *)

let MOI_S3SS_HEMI_SIDE = prove
 (`!(g:real^3->real^3) v c u w lh oh sg.
     moi_s32_model g v /\ c SUBSET g (vec 0) INSERT IMAGE g v /\ c SUBSET moi_s32_open g /\
     closed (c UNION IMAGE g moi_s32_rim) /\
     open_in (subtopology euclidean (moi_s32_open g)) u /\
     open_in (subtopology euclidean (moi_s32_open g)) w /\ DISJOINT u w /\
     u UNION w = moi_s32_open g DIFF c /\
     ((lh = moi_s32_lohemi /\ oh = moi_s32_hihemi /\ sg = -- &1) \/
      (lh = moi_s32_hihemi /\ oh = moi_s32_lohemi /\ sg = &1)) /\
     g (vector[&0; sg / &2; &0]) IN u
     ==> !y. y IN lh DIFF moi_s32_rim
             ==> ?d. &0 < d /\
                     IMAGE g (moi_s32_cyl INTER ball(y,d)) INTER
                     (c UNION IMAGE g moi_s32_rim) = {} /\
                     IMAGE g (interior moi_s32_cyl INTER ball(y,d)) SUBSET u /\
                     moi_s32_cyl INTER ball(y,d) INTER oh = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN (
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3GF_MODEL_OPEN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_model] o
    check (fun th -> can (find_term (fun t -> try fst(dest_const t) = "moi_s32_model"
                                              with Failure _ -> false)) (concl th))) THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_MODEL_POINTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `c UNION IMAGE (g:real^3->real^3) moi_s32_rim SUBSET
                moi_s32_open g UNION IMAGE g moi_s32_rim` ASSUME_TAC THENL
   [UNDISCH_TAC `c SUBSET moi_s32_open (g:real^3->real^3)` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN lh DIFF moi_s32_rim
                    ==> ?d. &0 < d /\
                            IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) INTER
                            (c UNION IMAGE g moi_s32_rim) = {} /\
                            moi_s32_cyl INTER ball(y,d) INTER oh = {}` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
                   `c UNION IMAGE (g:real^3->real^3) moi_s32_rim`; `y:real^3`]
      MOI_S3SS_HEMI_NBHD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `(y:real^3) IN lh DIFF moi_s32_rim` THEN ASM_REWRITE_TAC[IN_UNION] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(y:real^3) IN lh DIFF moi_s32_rim` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (lh DIFF moi_s32_rim) /\ lh DIFF moi_s32_rim SUBSET moi_s32_cyl /\
                vector[&0; sg; &0] IN lh DIFF moi_s32_rim`
  STRIP_ASSUME_TAC THENL
   [    ASM_REWRITE_TAC[MOI_S3SS_L0_CONNECTED; MOI_S3SS_H0_CONNECTED; MOI_S3SS_L0_IN;
                    MOI_S3SS_H0_IN; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    UNDISCH_TAC `moi_s32_lohemi SUBSET frontier moi_s32_cyl` THEN
    UNDISCH_TAC `moi_s32_hihemi SUBSET frontier moi_s32_cyl` THEN
    UNDISCH_TAC `frontier moi_s32_cyl SUBSET moi_s32_cyl` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `lh DIFF moi_s32_rim`;
                 `c UNION IMAGE (g:real^3->real^3) moi_s32_rim`; `u:real^3->bool`;
                 `w:real^3->bool`; `vector[&0; sg; &0]:real^3`] MOI_S3SS_SIDE_CONST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `open_in (subtopology euclidean (moi_s32_open g)) (u:real^3->bool)` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `open_in (subtopology euclidean (moi_s32_open g)) (w:real^3->bool)` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `u UNION w = moi_s32_open (g:real^3->real^3) DIFF c` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `vector[&0; sg; &0]:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term (fun t -> t = `oh:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(vector[&0; sg; &0],d))
                    = IMAGE g (interior moi_s32_cyl INTER ball(vector[&0; sg; &0],d))`
        (K ALL_TAC) THENL [REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `c:real^3->bool`; `u:real^3->bool`;
                     `w:real^3->bool`; `sg:real`; `d:real`] MOI_S3SS_AXIS_SIDE) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
         [UNDISCH_TAC `u UNION w = moi_s32_open (g:real^3->real^3) DIFF c` THEN SET_TAC[];
          ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `u:real^3->bool`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `oh:real^3->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MP_TAC(ISPECL [`y:real^3`; `min d1 d2`; `d1:real`] SUBSET_BALL) THEN
  MP_TAC(ISPECL [`y:real^3`; `min d1 d2`; `d2:real`] SUBSET_BALL) THEN
  REWRITE_TAC[REAL_MIN_MIN] THEN REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d1)) INTER
                 (c UNION IMAGE g moi_s32_rim) = {}` THEN
    UNDISCH_TAC `ball(y:real^3,min d1 d2) SUBSET ball(y,d1)` THEN SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(y,d2))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    UNDISCH_TAC `ball(y:real^3,min d1 d2) SUBSET ball(y,d2)` THEN SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `d1:real`)) (concl th) &&
      not(can (find_term (fun t -> t = `g:real^3->real^3`)) (concl th)))) THEN
    UNDISCH_TAC `ball(y:real^3,min d1 d2) SUBSET ball(y,d1)` THEN SET_TAC[]]));;

let MOI_S3SS_W_OPEN = prove
 (`!(g:real^3->real^3) g' p z lh oh.
     homeomorphism (moi_s32_cyl,IMAGE g moi_s32_cyl) (g,g') /\
     open_in (subtopology euclidean (moi_s32_open g)) z /\ open (moi_s32_open g) /\
     z SUBSET IMAGE g moi_s32_cyl DIFF p /\
     frontier moi_s32_cyl = lh UNION oh /\ moi_s32_rim SUBSET oh /\
     (!y. y IN lh DIFF moi_s32_rim
          ==> ?d. &0 < d /\ IMAGE g (moi_s32_cyl INTER ball(y,d)) INTER p = {} /\
                  IMAGE g (interior moi_s32_cyl INTER ball(y,d)) SUBSET z /\
                  moi_s32_cyl INTER ball(y,d) INTER oh = {})
     ==> open_in (subtopology euclidean (IMAGE g moi_s32_cyl DIFF p))
                 (z UNION IMAGE g (lh DIFF moi_s32_rim))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S3GF_CYL_PARTS THEN STRIP_TAC THEN
  SUBGOAL_THEN `lh SUBSET moi_s32_cyl` ASSUME_TAC THENL
   [UNDISCH_TAC `frontier moi_s32_cyl = lh UNION oh` THEN
    UNDISCH_TAC `frontier moi_s32_cyl SUBSET moi_s32_cyl` THEN SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_UNION] THEN
  X_GEN_TAC `x:real^3` THEN STRIP_TAC THENL
   [EXISTS_TAC `z:real^3->bool` THEN ASM_REWRITE_TAC[SUBSET_UNION] THEN
    MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `open_in (subtopology euclidean (moi_s32_open g)) (z:real^3->bool)` THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN IMAGE g (lh DIFF moi_s32_rim)` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `oh:real^3->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) moi_s32_cyl` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `moi_s32_cyl`] THEN
      ASM_SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL];
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) INTER p = {}` THEN
      SET_TAC[];
      SET_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_UNION] THEN
    X_GEN_TAC `y':real^3` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(y':real^3) IN interior moi_s32_cyl` THENL
     [DISJ1_TAC THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (interior moi_s32_cyl INTER ball(y,d)) SUBSET z` THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      SUBGOAL_THEN `(y':real^3) IN frontier moi_s32_cyl` MP_TAC THENL
       [REWRITE_TAC[frontier; MATCH_MP CLOSURE_CLOSED MOI_S3GF_CYL_CLOSED] THEN
        ASM_REWRITE_TAC[IN_DIFF];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_UNION; IN_DIFF] THEN
      UNDISCH_TAC `moi_s32_cyl INTER ball(y:real^3,d) INTER oh = {}` THEN
      UNDISCH_TAC `moi_s32_rim SUBSET oh` THEN
      UNDISCH_TAC `(y':real^3) IN moi_s32_cyl` THEN UNDISCH_TAC `(y':real^3) IN ball(y,d)` THEN
      SET_TAC[]]]);;

let MOI_S3SS_W_SEP = prove
 (`!(g:real^3->real^3) v c u w.
     moi_s32_model g v /\ c SUBSET g (vec 0) INSERT IMAGE g v /\ c SUBSET moi_s32_open g /\
     closed (c UNION IMAGE g moi_s32_rim) /\
     open_in (subtopology euclidean (moi_s32_open g)) u /\
     open_in (subtopology euclidean (moi_s32_open g)) w /\ DISJOINT u w /\
     u UNION w = moi_s32_open g DIFF c /\
     g moi_s32_qlo IN u /\ g moi_s32_qhi IN w
     ==> open_in (subtopology euclidean
                   (IMAGE g moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim)))
                 (u UNION IMAGE g (moi_s32_lohemi DIFF moi_s32_rim)) /\
         open_in (subtopology euclidean
                   (IMAGE g moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim)))
                 (w UNION IMAGE g (moi_s32_hihemi DIFF moi_s32_rim)) /\
         DISJOINT (u UNION IMAGE g (moi_s32_lohemi DIFF moi_s32_rim))
                  (w UNION IMAGE g (moi_s32_hihemi DIFF moi_s32_rim)) /\
         (u UNION IMAGE g (moi_s32_lohemi DIFF moi_s32_rim)) UNION
         (w UNION IMAGE g (moi_s32_hihemi DIFF moi_s32_rim)) =
         IMAGE g moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `c:real^3->bool`] MOI_S3SS_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3GF_MODEL_OPEN) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g':real^3->real^3` o MATCH_MP MOI_S3GF_MODEL_HOMEO) THEN
  SUBGOAL_THEN `u SUBSET moi_s32_open (g:real^3->real^3) DIFF c /\
                w SUBSET moi_s32_open (g:real^3->real^3) DIFF c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `u UNION w = moi_s32_open (g:real^3->real^3) DIFF c` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `c:real^3->bool`; `u:real^3->bool`;
                 `w:real^3->bool`; `moi_s32_lohemi`; `moi_s32_hihemi`; `-- &1`]
    MOI_S3SS_HEMI_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qlo IN u` THEN REWRITE_TAC[moi_s32_qlo];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `c:real^3->bool`; `w:real^3->bool`;
                 `u:real^3->bool`; `moi_s32_hihemi`; `moi_s32_lohemi`; `&1`]
    MOI_S3SS_HEMI_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `DISJOINT (u:real^3->bool) w` THEN SET_TAC[];
      UNDISCH_TAC `u UNION w = moi_s32_open (g:real^3->real^3) DIFF c` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      UNDISCH_TAC `(g:real^3->real^3) moi_s32_qhi IN w` THEN REWRITE_TAC[moi_s32_qhi]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `moi_s32_rim SUBSET moi_s32_hihemi /\ moi_s32_rim SUBSET moi_s32_lohemi /\
                frontier moi_s32_cyl = moi_s32_lohemi UNION moi_s32_hihemi /\
                frontier moi_s32_cyl = moi_s32_hihemi UNION moi_s32_lohemi`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3GF_FRONTIER_CYL; GSYM MOI_S3GF_HEMI_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3SS_W_OPEN THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `moi_s32_hihemi`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim) =
                 (moi_s32_open g DIFF c) UNION IMAGE g (moi_s32_lohemi DIFF moi_s32_rim) UNION
                 IMAGE g (moi_s32_hihemi DIFF moi_s32_rim)` THEN
    UNDISCH_TAC `u SUBSET moi_s32_open (g:real^3->real^3) DIFF c` THEN SET_TAC[];
    MATCH_MP_TAC MOI_S3SS_W_OPEN THEN
    MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `moi_s32_lohemi`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim) =
                 (moi_s32_open g DIFF c) UNION IMAGE g (moi_s32_lohemi DIFF moi_s32_rim) UNION
                 IMAGE g (moi_s32_hihemi DIFF moi_s32_rim)` THEN
    UNDISCH_TAC `w SUBSET moi_s32_open (g:real^3->real^3) DIFF c` THEN SET_TAC[];
    UNDISCH_TAC `DISJOINT (moi_s32_open (g:real^3->real^3))
                   (IMAGE g (moi_s32_lohemi DIFF moi_s32_rim))` THEN
    UNDISCH_TAC `DISJOINT (moi_s32_open (g:real^3->real^3))
                   (IMAGE g (moi_s32_hihemi DIFF moi_s32_rim))` THEN
    UNDISCH_TAC `DISJOINT (IMAGE (g:real^3->real^3) (moi_s32_lohemi DIFF moi_s32_rim))
                   (IMAGE g (moi_s32_hihemi DIFF moi_s32_rim))` THEN
    UNDISCH_TAC `DISJOINT (u:real^3->bool) w` THEN
    UNDISCH_TAC `u SUBSET moi_s32_open (g:real^3->real^3) DIFF c` THEN
    UNDISCH_TAC `w SUBSET moi_s32_open (g:real^3->real^3) DIFF c` THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (g:real^3->real^3) moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim) =
                 (moi_s32_open g DIFF c) UNION IMAGE g (moi_s32_lohemi DIFF moi_s32_rim) UNION
                 IMAGE g (moi_s32_hihemi DIFF moi_s32_rim)` THEN
    UNDISCH_TAC `u UNION w = moi_s32_open (g:real^3->real^3) DIFF c` THEN
    SPEC_TAC(`IMAGE (g:real^3->real^3) moi_s32_cyl DIFF (c UNION IMAGE g moi_s32_rim)`,
             `z0:real^3->bool`) THEN
    SPEC_TAC(`IMAGE (g:real^3->real^3) (moi_s32_lohemi DIFF moi_s32_rim)`, `a0:real^3->bool`) THEN
    SPEC_TAC(`IMAGE (g:real^3->real^3) (moi_s32_hihemi DIFF moi_s32_rim)`, `b0:real^3->bool`) THEN
    SPEC_TAC(`moi_s32_open (g:real^3->real^3) DIFF c`, `o0:real^3->bool`) THEN
    SET_TAC[]]);;

(* A component of x whose closure contains q contains one of the two local *)
(* sides at q.                                                              *)

let MOI_S3SS_COMP_SIDE = prove
 (`!(x:real^3->bool) p k q r e1 e2.
     k IN components x /\ q IN closure k /\ &0 < r /\
     ball(q,r) DIFF p = e1 UNION e2 /\ connected e1 /\ connected e2 /\
     ball(q,r) SUBSET x UNION p /\ DISJOINT x p
     ==> e1 SUBSET k \/ e2 SUBSET k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET x` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^3. z IN k /\ z IN ball(q,r)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^3) IN closure k` THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[IN_BALL] THEN
    MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN e1 \/ z IN e2` MP_TAC THENL
   [UNDISCH_TAC `ball(q:real^3,r) DIFF p = e1 UNION e2` THEN
    UNDISCH_TAC `DISJOINT (x:real^3->bool) p` THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET x` THEN
    UNDISCH_TAC `(z:real^3) IN k` THEN UNDISCH_TAC `(z:real^3) IN ball(q,r)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e1:real^3->bool) SUBSET x /\ (e2:real^3->bool) SUBSET x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(q:real^3,r) DIFF p = e1 UNION e2` THEN
    UNDISCH_TAC `ball(q:real^3,r) SUBSET x UNION p` THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `x:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISJ2_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `x:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 9. The global argument.                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3SS_BASICS = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh /\
     pseudo_cell (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim)
                 (IMAGE g moi_s32_rim) (g (vec 0))
     ==> moi_s32_chainset g hh bb SUBSET moi_s32_open g /\
         moi_s32_chainset g hh bb SUBSET g (vec 0) INSERT IMAGE g v /\
         DISJOINT (moi_s32_chainset g hh bb) (IMAGE g moi_s32_rim) /\
         g (vec 0) IN moi_s32_chainset g hh bb /\
         closed (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim) /\
         closure (moi_s32_chainset g hh bb DELETE g (vec 0)) =
           moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim /\
         connected (moi_s32_chainset g hh bb DELETE g (vec 0)) /\
         ~(moi_s32_chainset g hh bb DELETE g (vec 0) = {}) /\
         open (moi_s32_open g DIFF moi_s32_chainset g hh bb) /\
         (?u w. open_in (subtopology euclidean (moi_s32_open g)) u /\
                open_in (subtopology euclidean (moi_s32_open g)) w /\ DISJOINT u w /\
                u UNION w = moi_s32_open g DIFF moi_s32_chainset g hh bb /\
                g moi_s32_qlo IN u /\ g moi_s32_qhi IN w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3GF_CHAIN_OPEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3GF_CHAIN_V) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[pseudo_cell] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "pseudo_cell" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_s32_chainset (g:real^3->real^3) hh bb`; `(g:real^3->real^3) (vec 0)`]
    MOI_S3SS_PUNCT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3GF_MODEL_OPEN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s32_chain] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_s32_chain" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `closure (moi_s32_chainset (g:real^3->real^3) hh bb) =
                          moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim`)) THEN
    REWRITE_TAC[CLOSED_CLOSURE];
    SUBST1_TAC(SYM(ASSUME `closure (moi_s32_chainset (g:real^3->real^3) hh bb) =
                          moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim`)) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
      MP_TAC(ISPEC `moi_s32_chainset (g:real^3->real^3) hh bb DELETE g (vec 0)`
        CLOSURE_SUBSET) THEN
      UNDISCH_TAC `(g:real^3->real^3) (vec 0) IN
                   closure (moi_s32_chainset g hh bb DELETE g (vec 0))` THEN
      SET_TAC[]];
    SUBGOAL_THEN `open_in (subtopology euclidean (moi_s32_open (g:real^3->real^3)))
                    (moi_s32_open g DIFF moi_s32_chainset g hh bb)` MP_TAC THENL
     [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_EQ];
    UNDISCH_TAC `separates_in (moi_s32_open (g:real^3->real^3)) (moi_s32_chainset g hh bb)
                   {g moi_s32_qlo} {g moi_s32_qhi}` THEN
    REWRITE_TAC[separates_in; SING_SUBSET] THEN ASM_REWRITE_TAC[]]);;

(* The closure of a component meets the punctured chain in an open set.    *)

let MOI_S3SS_AON_OPEN = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh k.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh /\
     k IN components (IMAGE g moi_s32_cyl DIFF
                      (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim))
     ==> open_in (subtopology euclidean (moi_s32_chainset g hh bb DELETE g (vec 0)))
                 ((moi_s32_chainset g hh bb DELETE g (vec 0)) INTER closure k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL; INTER_SUBSET] THEN
  X_GEN_TAC `q:real^3` THEN REWRITE_TAC[IN_INTER; IN_DELETE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`;
                 `q:real^3`] MOI_S3SS_LOCAL_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `e1:real^3->bool`
    (X_CHOOSE_THEN `e2:real^3->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) moi_s32_cyl DIFF
                   (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim)`;
                 `moi_s32_chainset (g:real^3->real^3) hh bb UNION IMAGE g moi_s32_rim`;
                 `k:real^3->bool`; `q:real^3`; `r:real`; `e1:real^3->bool`;
                 `e2:real^3->bool`] MOI_S3SS_COMP_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s32_open (g:real^3->real^3)` THEN
      ASM_REWRITE_TAC[moi_s32_open] THEN MP_TAC(ISPEC `IMAGE (g:real^3->real^3) moi_s32_cyl`
        INTERIOR_SUBSET) THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(moi_s32_chainset g hh bb UNION IMAGE (g:real^3->real^3) moi_s32_rim) INTER
                ball(q,r) SUBSET closure k` MP_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure e1:real^3->bool` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure e2:real^3->bool` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]]];
    SET_TAC[]]);;

(* Every component of the complement of p in the closed model ball meets    *)
(* the open model ball: a point on a hemisphere has a half-ball            *)
(* neighbourhood inside the component, and that half-ball contains          *)
(* interior points.                                                          *)

let MOI_S3SS_COMP_MEETS_OPEN = prove
 (`!(g:real^3->real^3) v p k.
     moi_s32_model g v /\ closed p /\
     p SUBSET moi_s32_open g UNION IMAGE g moi_s32_rim /\
     IMAGE g moi_s32_rim SUBSET p /\
     k IN components (IMAGE g moi_s32_cyl DIFF p)
     ==> ~(k INTER moi_s32_open g = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k:real^3->bool = {}) /\
                k SUBSET IMAGE (g:real^3->real^3) moi_s32_cyl DIFF p /\ connected k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_SUBSET; IN_COMPONENTS_CONNECTED];
    ALL_TAC] THEN
  UNDISCH_TAC `~(k:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x0:real^3`) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`] MOI_S3GF_MODEL_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  REWRITE_TAC[IN_INTER] THEN
  SUBGOAL_THEN `?y. y IN moi_s32_cyl /\ (g:real^3->real^3) y = x0` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^3->bool) SUBSET IMAGE (g:real^3->real^3) moi_s32_cyl DIFF p` THEN
    UNDISCH_TAC `(x0:real^3) IN k` THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(y:real^3) IN interior moi_s32_cyl` THENL
   [EXISTS_TAC `x0:real^3` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "x0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x0:real^3) IN p)` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^3->bool) SUBSET IMAGE (g:real^3->real^3) moi_s32_cyl DIFF p` THEN
    UNDISCH_TAC `(x0:real^3) IN k` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^3) IN moi_s32_rim)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((x0:real^3) IN p)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) moi_s32_rim SUBSET p` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "x0" THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN (moi_s32_lohemi DIFF moi_s32_rim) UNION
                              (moi_s32_hihemi DIFF moi_s32_rim)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN frontier moi_s32_cyl` MP_TAC THENL
     [REWRITE_TAC[frontier; IN_DIFF] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; MOI_S3GF_CYL_CLOSED];
      REWRITE_TAC[MOI_S3GF_FRONTIER_CYL] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `p:real^3->bool`; `y:real^3`]
    MOI_S3SS_HEMI_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) SUBSET k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `IMAGE (g:real^3->real^3) moi_s32_cyl DIFF p` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `moi_s32_cyl` THEN
        REWRITE_TAC[INTER_SUBSET] THEN UNDISCH_TAC `moi_s32_model (g:real^3->real^3) v` THEN
        SIMP_TAC[moi_s32_model];
        MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[MOI_S3SS_CYL_CONVEX; CONVEX_BALL]];
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) INTER p = {}` THEN
      SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x0:real^3` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "x0" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:real^3`; `d:real`] (CONJUNCT2 MOI_S3SS_CYL_CLOSURE)) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(g:real^3->real^3) z` THEN CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^3->real^3) (moi_s32_cyl INTER ball(y,d)) SUBSET k` THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `moi_s32_cyl` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* The closure of every component meets the punctured chain: otherwise the  *)
(* part of the component inside the open model ball would be open and       *)
(* closed in the connected punctured open ball, hence all of it, which is   *)
(* impossible because that set contains chain points.                       *)

let MOI_S3SS_AON_NONEMPTY = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh k.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh /\
     pseudo_cell (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim)
                 (IMAGE g moi_s32_rim) (g (vec 0)) /\
     k IN components (IMAGE g moi_s32_cyl DIFF
                      (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim))
     ==> ~((moi_s32_chainset g hh bb DELETE g (vec 0)) INTER closure k = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3SS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
                 `moi_s32_chainset (g:real^3->real^3) hh bb UNION IMAGE g moi_s32_rim`;
                 `k:real^3->bool`] MOI_S3SS_COMP_MEETS_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s32_chainset (g:real^3->real^3) hh bb SUBSET moi_s32_open g` THEN
    SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
                 `moi_s32_chainset (g:real^3->real^3) hh bb`] MOI_S3SS_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `!(xx:real^3->bool) oo c l h.
      xx = (oo DIFF c) UNION l UNION h /\ DISJOINT oo l /\ DISJOINT oo h /\ DISJOINT l h
      ==> xx INTER oo = oo DIFF c /\ oo DIFF c SUBSET xx`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `(g:real^3->real^3) (vec 0)`]
    MOI_S3SS_M_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
                 `moi_s32_chainset (g:real^3->real^3) hh bb UNION IMAGE g moi_s32_rim`;
                 `k:real^3->bool`] MOI_S3SS_COMPONENTS_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) moi_s32_cyl DIFF
                  (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim)`; `k:real^3->bool`]
    CLOSED_IN_COMPONENT) THEN
  ASM_REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN DISCH_TAC THEN
  ABBREV_TAC `cc = moi_s32_chainset (g:real^3->real^3) hh bb` THEN
  ABBREV_TAC `xx = IMAGE (g:real^3->real^3) moi_s32_cyl DIFF (cc UNION IMAGE g moi_s32_rim)` THEN
  ABBREV_TAC `mm = moi_s32_open (g:real^3->real^3)` THEN
  DISCH_TAC THEN
  ABBREV_TAC `aa = (k:real^3->bool) INTER mm` THEN
  SUBGOAL_THEN `open (aa:real^3->bool) /\ aa SUBSET mm DIFF cc` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean xx) (k:real^3->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o1:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `aa = (mm DIFF cc) INTER (o1:real^3->bool)` SUBST1_TAC THENL
     [EXPAND_TAC "aa" THEN
      UNDISCH_TAC `(k:real^3->bool) = xx INTER o1` THEN
      UNDISCH_TAC `xx INTER mm = mm DIFF (cc:real^3->bool)` THEN SET_TAC[];
      ASM_SIMP_TAC[OPEN_INTER] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean (mm DELETE (g:real^3->real^3) (vec 0))) aa`
  ASSUME_TAC THENL
   [REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_DELETE] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN closure k` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`aa:real^3->bool`; `k:real^3->bool`] SUBSET_CLOSURE) THEN
        ANTS_TAC THENL
         [EXPAND_TAC "aa" THEN SET_TAC[];
          UNDISCH_TAC `(z:real^3) IN closure aa` THEN SET_TAC[]];
        ALL_TAC] THEN
      ASM_CASES_TAC `(z:real^3) IN cc` THENL
       [UNDISCH_TAC `(cc DELETE (g:real^3->real^3) (vec 0)) INTER closure k = {}` THEN
        REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_DELETE] THEN
        DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN k` ASSUME_TAC THENL
       [UNDISCH_TAC `xx INTER closure k = (k:real^3->bool)` THEN
        UNDISCH_TAC `mm DIFF cc SUBSET (xx:real^3->bool)` THEN
        UNDISCH_TAC `(z:real^3) IN mm` THEN UNDISCH_TAC `~((z:real^3) IN cc)` THEN
        UNDISCH_TAC `(z:real^3) IN closure k` THEN SET_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "aa" THEN REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `aa:real^3->bool` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `aa SUBSET mm DIFF (cc:real^3->bool)` THEN
      UNDISCH_TAC `(g:real^3->real^3) (vec 0) IN cc` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `mm DELETE (g:real^3->real^3) (vec 0)` CONNECTED_CLOPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `aa:real^3->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aa SUBSET mm DIFF (cc:real^3->bool)` THEN
    UNDISCH_TAC `(g:real^3->real^3) (vec 0) IN cc` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~(cc DELETE (g:real^3->real^3) (vec 0) = {})` THEN
  UNDISCH_TAC `cc SUBSET (mm:real^3->bool)` THEN
  UNDISCH_TAC `aa SUBSET mm DIFF (cc:real^3->bool)` THEN
  UNDISCH_TAC `aa = mm DELETE (g:real^3->real^3) (vec 0)` THEN
  SET_TAC[]);;

(* All or none: the closure of every component contains the chain and the   *)
(* rim (the trace of the closure on the punctured chain is open, closed and *)
(* nonempty in the connected punctured chain).                              *)

let MOI_S3SS_ALL_OR_NONE = prove
 (`!(g:real^3->real^3) v pp dd s2 hh bb jl jh k.
     moi_s32_model g v /\ moi_s32_tower g v pp dd s2 /\
     moi_s32_chain g dd s2 hh bb jl jh /\
     pseudo_cell (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim)
                 (IMAGE g moi_s32_rim) (g (vec 0)) /\
     k IN components (IMAGE g moi_s32_cyl DIFF
                      (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim))
     ==> moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim SUBSET closure k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3SS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`;
                 `k:real^3->bool`] MOI_S3SS_AON_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`;
                 `k:real^3->bool`] MOI_S3SS_AON_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `moi_s32_chainset (g:real^3->real^3) hh bb DELETE g (vec 0)`
    CONNECTED_CLOPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
   `(moi_s32_chainset (g:real^3->real^3) hh bb DELETE g (vec 0)) INTER closure k`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSED_IN_CLOSED_INTER; CLOSED_CLOSURE];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `moi_s32_chainset (g:real^3->real^3) hh bb DELETE g (vec 0) SUBSET closure k`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(moi_s32_chainset (g:real^3->real^3) hh bb DELETE g (vec 0)) INTER
                 closure k = moi_s32_chainset g hh bb DELETE g (vec 0)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `closure (moi_s32_chainset (g:real^3->real^3) hh bb DELETE g (vec 0))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL];
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[CLOSED_CLOSURE]]);;

(* At most two components: if the closure of every component of x contains *)
(* q and near q the complement of p consists of two connected local sides, *)
(* then two distinct components are all of them.                           *)

let MOI_S3SS_TWO_COMPONENTS = prove
 (`!(x:real^3->bool) p k1 k2 q r e1 e2.
     k1 IN components x /\ k2 IN components x /\ ~(k1 = k2) /\
     (!k. k IN components x ==> q IN closure k) /\
     &0 < r /\ ball(q,r) DIFF p = e1 UNION e2 /\ connected e1 /\ connected e2 /\
     ~(e1 = {}) /\ ~(e2 = {}) /\
     ball(q,r) SUBSET x UNION p /\ DISJOINT x p
     ==> components x = {k1,k2}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. k IN components x ==> (e1:real^3->bool) SUBSET k \/ e2 SUBSET k`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^3->bool`; `p:real^3->bool`; `k:real^3->bool`; `q:real^3`; `r:real`;
                   `e1:real^3->bool`; `e2:real^3->bool`] MOI_S3SS_COMP_SIDE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k1:real^3->bool) INTER k2 = {}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `k:real^3->bool` THEN
  EQ_TAC THENL [DISCH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`e1:real^3->bool`; `e2:real^3->bool`; `k1:real^3->bool`;
                 `k2:real^3->bool`; `k:real^3->bool`]
    (SET_RULE `!(e1:real^3->bool) e2 k1 k2 k.
        ~(e1 = {}) /\ ~(e2 = {}) /\ k1 INTER k2 = {} /\
        (e1 SUBSET k1 \/ e2 SUBSET k1) /\ (e1 SUBSET k2 \/ e2 SUBSET k2) /\
        (e1 SUBSET k \/ e2 SUBSET k)
        ==> ~(k INTER k1 = {}) \/ ~(k INTER k2 = {})`)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `k:real^3->bool`; `k1:real^3->bool`]
    COMPONENTS_NONOVERLAP) THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `k:real^3->bool`; `k2:real^3->bool`]
    COMPONENTS_NONOVERLAP) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* A frontier criterion used for the two hemispheres.                        *)

let MOI_S3SS_FRONTIER_HEMI = prove
 (`!(a:real^3->bool) l r k m.
     a SUBSET l UNION r /\ r SUBSET frontier k /\ l SUBSET k /\
     interior k SUBSET m /\ DISJOINT m l
     ==> a SUBSET frontier k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `k:real^3->bool` CLOSURE_SUBSET) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The headline (Moise, the two sides of the pseudo-cell, p.226).             *)
(* ------------------------------------------------------------------------- *)

let SIDES = prove
 (MOI_S32_SIDES,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`]
    MOI_S3SS_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
                 `moi_s32_chainset (g:real^3->real^3) hh bb`;
                 `u:real^3->bool`; `w:real^3->bool`] MOI_S3SS_W_SEP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`;
                 `moi_s32_chainset (g:real^3->real^3) hh bb`] MOI_S3SS_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!k. k IN components (IMAGE (g:real^3->real^3) moi_s32_cyl DIFF
                         (moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim))
        ==> moi_s32_chainset g hh bb UNION IMAGE g moi_s32_rim SUBSET closure k`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                   `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                   `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`;
                   `k:real^3->bool`] MOI_S3SS_ALL_OR_NONE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cc = moi_s32_chainset (g:real^3->real^3) hh bb` THEN
  SUBGOAL_THEN
   `IMAGE (g:real^3->real^3) moi_s32_cyl DIFF (cc UNION IMAGE g moi_s32_rim) SUBSET
      IMAGE g moi_s32_cyl /\
    DISJOINT (IMAGE (g:real^3->real^3) moi_s32_cyl DIFF (cc UNION IMAGE g moi_s32_rim))
             (cc UNION IMAGE g moi_s32_rim) /\
    IMAGE (g:real^3->real^3) moi_s32_cyl SUBSET
      (IMAGE g moi_s32_cyl DIFF (cc UNION IMAGE g moi_s32_rim)) UNION
      (cc UNION IMAGE g moi_s32_rim) /\
    moi_s32_open g SUBSET IMAGE g moi_s32_cyl`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s32_open; INTERIOR_SUBSET] THEN
    REWRITE_TAC[SET_RULE `!(y:real^3->bool) p.
      y DIFF p SUBSET y /\ DISJOINT (y DIFF p) p /\ y SUBSET (y DIFF p) UNION p`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u:real^3->bool) SUBSET u UNION IMAGE (g:real^3->real^3) (moi_s32_lohemi DIFF moi_s32_rim) /\
    IMAGE (g:real^3->real^3) (moi_s32_lohemi DIFF moi_s32_rim) SUBSET
      u UNION IMAGE g (moi_s32_lohemi DIFF moi_s32_rim) /\
    (w:real^3->bool) SUBSET w UNION IMAGE (g:real^3->real^3) (moi_s32_hihemi DIFF moi_s32_rim) /\
    IMAGE (g:real^3->real^3) (moi_s32_hihemi DIFF moi_s32_rim) SUBSET
      w UNION IMAGE g (moi_s32_hihemi DIFF moi_s32_rim) /\
    IMAGE (g:real^3->real^3) moi_s32_lohemi SUBSET
      IMAGE g (moi_s32_lohemi DIFF moi_s32_rim) UNION IMAGE g moi_s32_rim /\
    IMAGE (g:real^3->real^3) moi_s32_hihemi SUBSET
      IMAGE g (moi_s32_hihemi DIFF moi_s32_rim) UNION IMAGE g moi_s32_rim`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_UNION] THEN
    REWRITE_TAC[SET_RULE `!(f:real^3->real^3) s r.
      IMAGE f s SUBSET IMAGE f (s DIFF r) UNION IMAGE f r`];
    ALL_TAC] THEN
  ABBREV_TAC `xx = IMAGE (g:real^3->real^3) moi_s32_cyl DIFF (cc UNION IMAGE g moi_s32_rim)` THEN
  ABBREV_TAC `w1 = (u:real^3->bool) UNION
                   IMAGE (g:real^3->real^3) (moi_s32_lohemi DIFF moi_s32_rim)` THEN
  ABBREV_TAC `w2 = (w:real^3->bool) UNION
                   IMAGE (g:real^3->real^3) (moi_s32_hihemi DIFF moi_s32_rim)` THEN
  SUBGOAL_THEN `(g:real^3->real^3) moi_s32_qlo IN w1 /\ g moi_s32_qhi IN w2 /\
                g moi_s32_qlo IN xx /\ g moi_s32_qhi IN xx`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w1:real^3->bool) UNION w2 = xx` THEN
    UNDISCH_TAC `(u:real^3->bool) SUBSET w1` THEN UNDISCH_TAC `(w:real^3->bool) SUBSET w2` THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qlo IN u` THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qhi IN w` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component xx ((g:real^3->real^3) moi_s32_qlo) IN components xx /\
    connected_component xx ((g:real^3->real^3) moi_s32_qhi) IN components xx /\
    (g:real^3->real^3) moi_s32_qlo IN connected_component xx (g moi_s32_qlo) /\
    (g:real^3->real^3) moi_s32_qhi IN connected_component xx (g moi_s32_qhi) /\
    connected (connected_component xx ((g:real^3->real^3) moi_s32_qlo)) /\
    connected (connected_component xx ((g:real^3->real^3) moi_s32_qhi)) /\
    connected_component xx ((g:real^3->real^3) moi_s32_qlo) SUBSET xx /\
    connected_component xx ((g:real^3->real^3) moi_s32_qhi) SUBSET xx`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS; CONNECTED_CONNECTED_COMPONENT;
                    CONNECTED_COMPONENT_SUBSET] THEN
    REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `k1 = connected_component xx ((g:real^3->real^3) moi_s32_qlo)` THEN
  ABBREV_TAC `k2 = connected_component xx ((g:real^3->real^3) moi_s32_qhi)` THEN
  SUBGOAL_THEN `(k1:real^3->bool) SUBSET w1 /\ (k2:real^3->bool) SUBSET w2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`xx:real^3->bool`; `w1:real^3->bool`; `w2:real^3->bool`;
                     `k1:real^3->bool`] MOI_S3SS_CONN_SPLIT) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (w1:real^3->bool) w2` THEN
      UNDISCH_TAC `(g:real^3->real^3) moi_s32_qlo IN w1` THEN
      UNDISCH_TAC `(g:real^3->real^3) moi_s32_qlo IN k1` THEN SET_TAC[];
      MP_TAC(ISPECL [`xx:real^3->bool`; `w1:real^3->bool`; `w2:real^3->bool`;
                     `k2:real^3->bool`] MOI_S3SS_CONN_SPLIT) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (w1:real^3->bool) w2` THEN
      UNDISCH_TAC `(g:real^3->real^3) moi_s32_qhi IN w2` THEN
      UNDISCH_TAC `(g:real^3->real^3) moi_s32_qhi IN k2` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k1:real^3->bool = k2)` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (w1:real^3->bool) w2` THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qlo IN w1` THEN
    UNDISCH_TAC `(g:real^3->real^3) moi_s32_qlo IN k1` THEN
    UNDISCH_TAC `(k2:real^3->bool) SUBSET w2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?q0. q0 IN cc /\ ~(q0 = (g:real^3->real^3) (vec 0))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(cc DELETE (g:real^3->real^3) (vec 0) = {})` THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `v:real^3->bool`; `pp:int->real^3`;
                 `dd:int->real^3->bool`; `s2:int->real^3->bool`; `hh:int->real^3->bool`;
                 `bb:int->real^3->bool`; `jl:int->real^3->bool`; `jh:int->real^3->bool`;
                 `q0:real^3`] MOI_S3SS_LOCAL_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `e1:real^3->bool`
    (X_CHOOSE_THEN `e2:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!k. k IN components xx ==> (q0:real^3) IN closure k` ASSUME_TAC THENL
   [X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `cc UNION IMAGE (g:real^3->real^3) moi_s32_rim SUBSET closure k` MP_TAC THENL
     [ASM_SIMP_TAC[]; UNDISCH_TAC `(q0:real^3) IN cc` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`xx:real^3->bool`; `cc UNION IMAGE (g:real^3->real^3) moi_s32_rim`;
                 `k1:real^3->bool`; `k2:real^3->bool`; `q0:real^3`; `r:real`;
                 `e1:real^3->bool`; `e2:real^3->bool`] MOI_S3SS_TWO_COMPONENTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (g:real^3->real^3) moi_s32_cyl SUBSET
                 xx UNION (cc UNION IMAGE g moi_s32_rim)` THEN
    UNDISCH_TAC `moi_s32_open (g:real^3->real^3) SUBSET IMAGE g moi_s32_cyl` THEN
    UNDISCH_TAC `ball(q0:real^3,r) SUBSET moi_s32_open g` THEN
    MESON_TAC[SUBSET_TRANS];
    DISCH_TAC] THEN
  SUBGOAL_THEN `(w1:real^3->bool) = k1 /\ (w2:real^3->bool) = k2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `xx:real^3->bool` UNIONS_COMPONENTS) THEN
    ASM_REWRITE_TAC[UNIONS_2] THEN DISCH_TAC THEN
    UNDISCH_TAC `(w1:real^3->bool) UNION w2 = xx` THEN
    UNDISCH_TAC `DISJOINT (w1:real^3->bool) w2` THEN
    UNDISCH_TAC `(k1:real^3->bool) SUBSET w1` THEN UNDISCH_TAC `(k2:real^3->bool) SUBSET w2` THEN
    UNDISCH_TAC `xx = (k1:real^3->bool) UNION k2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k IN components xx
                    ==> cc UNION IMAGE (g:real^3->real^3) moi_s32_rim SUBSET frontier k`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `cc UNION IMAGE (g:real^3->real^3) moi_s32_rim SUBSET closure k` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(k:real^3->bool) SUBSET xx` MP_TAC THENL
     [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `DISJOINT xx (cc UNION IMAGE (g:real^3->real^3) moi_s32_rim)` THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k SUBSET xx ==> interior k SUBSET moi_s32_open (g:real^3->real^3)`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN REWRITE_TAC[moi_s32_open] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `xx:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cc UNION IMAGE (g:real^3->real^3) moi_s32_rim SUBSET frontier k1 /\
    cc UNION IMAGE (g:real^3->real^3) moi_s32_rim SUBSET frontier k2 /\
    IMAGE (g:real^3->real^3) moi_s32_rim SUBSET frontier k1 /\
    IMAGE (g:real^3->real^3) moi_s32_rim SUBSET frontier k2 /\
    interior k1 SUBSET moi_s32_open (g:real^3->real^3) /\
    interior k2 SUBSET moi_s32_open (g:real^3->real^3) /\
    IMAGE (g:real^3->real^3) (moi_s32_lohemi DIFF moi_s32_rim) SUBSET k1 /\
    IMAGE (g:real^3->real^3) (moi_s32_hihemi DIFF moi_s32_rim) SUBSET k2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_MESON_TAC[SUBSET_UNION; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) moi_s32_lohemi SUBSET frontier k1 /\
                IMAGE (g:real^3->real^3) moi_s32_hihemi SUBSET frontier k2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) moi_s32_lohemi`;
                     `IMAGE (g:real^3->real^3) (moi_s32_lohemi DIFF moi_s32_rim)`;
                     `IMAGE (g:real^3->real^3) moi_s32_rim`; `k1:real^3->bool`;
                     `moi_s32_open (g:real^3->real^3)`] MOI_S3SS_FRONTIER_HEMI) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) moi_s32_hihemi`;
                     `IMAGE (g:real^3->real^3) (moi_s32_hihemi DIFF moi_s32_rim)`;
                     `IMAGE (g:real^3->real^3) moi_s32_rim`; `k2:real^3->bool`;
                     `moi_s32_open (g:real^3->real^3)`] MOI_S3SS_FRONTIER_HEMI) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k1:real^3->bool`; `k2:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

