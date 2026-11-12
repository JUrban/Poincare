(* ========================================================================= *)
(* pc_moi_pd2_glob (step M8 of route M): the 2D assembly                     *)
(* MOI_SMO_PD2_FROM_LEAVES, i.e. the implication MOI_SMO_PD2_TERM from the   *)
(* leaves D1-D5 and C1.                                                      *)
(* Proof structure: STAGE1 (vertex smoothing, the creased map is a         *)
(* homeomorphism by D5), STAGE2 (crease smoothing by D3 along finitely     *)
(* many straight segments), FINAL (a map that is a smooth immersion near   *)
(* every point is one in every chart, and a homeomorphism by D5).          *)
(* ========================================================================= *)

needs "src/pc_moi_smo_defs.ml";;
needs "src/pc_mfd_base.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Helper definitions.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Charts, their inverses chart_inv (U,phi) and transition maps come from    *)
(* pc_mfd_base.ml (which needs only poincare_statement.ml and                *)
(* ns_smooth_elem.ml, both already loaded with pc_moi_smo_defs.ml).          *)

(* A map into real^3 is a smooth immersion near x: in some chart at x it    *)
(* agrees, on a neighbourhood of the image of x, with a smooth map whose    *)
(* derivative is injective.                                                 *)

let moi_pdg_imm_at = new_definition
 `moi_pdg_imm_at (sigma:((real^N->bool)#(real^N->real^2))->bool)
                 (f:real^N->real^3) (x:real^N) <=>
    ?U phi W g. (U,phi) IN sigma /\ x IN U /\ open W /\ phi x IN W /\
                W SUBSET IMAGE phi U /\ smooth_map_on W (g:real^2->real^3) /\
                (!z. z IN U /\ phi z IN W ==> g(phi z) = f z) /\
                (!y v. y IN W /\ frechet_derivative g (at y) v = vec 0
                       ==> v = vec 0)`;;

(* A crease datum: in the chart (U,phi), along the straight segment          *)
(* z0 + c * [a,b] (norm c = 1), the map f has smooth one-sided extensions   *)
(* with injective derivative from both sides, and is smooth across the      *)
(* segment near both ends.                                                  *)

let moi_pdg_crease = new_definition
 `moi_pdg_crease (sigma:((real^N->bool)#(real^N->real^2))->bool)
                 (f:real^N->real^3) (U:real^N->bool) (phi:real^N->real^2)
                 (z0:complex) (c:complex) (a:real) (b:real) (e:real) <=>
    (U,phi) IN sigma /\ norm c = &1 /\ a < b /\ &0 < e /\ &4 * e < b - a /\
    (!t. a <= t /\ t <= b
         ==> (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                    (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phi U) /\
                    (!x. x IN ball(Cx t,r) /\ &0 <= Im x
                         ==> g x = f(chart_inv (U,phi) (z0 + c * x))) /\
                    (!x v. x IN ball(Cx t,r) /\ &0 <= Im x /\
                           frechet_derivative g (at x) v = vec 0
                           ==> v = vec 0)) /\
             (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                    (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phi U) /\
                    (!x. x IN ball(Cx t,r) /\ Im x <= &0
                         ==> g x = f(chart_inv (U,phi) (z0 + c * x))) /\
                    (!x v. x IN ball(Cx t,r) /\ Im x <= &0 /\
                           frechet_derivative g (at x) v = vec 0
                           ==> v = vec 0))) /\
    (!t. a <= t /\ t <= a + e \/ b - e <= t /\ t <= b
         ==> ?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                   (!x. x IN ball(Cx t,r)
                        ==> z0 + c * x IN IMAGE phi U /\
                            g x = f(chart_inv (U,phi) (z0 + c * x))))`;;

(* Stereographic projection from the pole adjoint f (basis 3), for an       *)
(* orthogonal transformation f, and its inverse (defined on all of real^2). *)

let moi_pdg_st = new_definition
 `moi_pdg_st (f:real^3->real^3) (y:real^3) =
    inv(&1 - (f y)$3) % (vector[(f y)$1; (f y)$2]:real^2)`;;

let moi_pdg_sti = new_definition
 `moi_pdg_sti (f:real^3->real^3) (u:real^2) =
    adjoint f (inv(&1 + norm u pow 2) %
               (vector[&2 * u$1; &2 * u$2; norm u pow 2 - &1]:real^3))`;;

(* ------------------------------------------------------------------------- *)
(* Stereographic charts of S^2 and small smooth-calculus helpers.           *)
(* ------------------------------------------------------------------------- *)

let MOI_PDG_ORTH_INV = prove
 (`!(f:real^3->real^3) x.
      orthogonal_transformation f
      ==> f(adjoint f x) = x /\ adjoint f (f x) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ORTHOGONAL_TRANSFORMATION_EQ_ADJOINT] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN MESON_TAC[]);;

let MOI_PDG_STD_STI_COMPONENTS = prove
 (`!u:real^2.
      (inv(&1 + norm u pow 2) %
       (vector[&2 * u$1; &2 * u$2; norm u pow 2 - &1]:real^3))$1 =
        &2 * u$1 / (&1 + u$1 pow 2 + u$2 pow 2) /\
      (inv(&1 + norm u pow 2) %
       (vector[&2 * u$1; &2 * u$2; norm u pow 2 - &1]:real^3))$2 =
        &2 * u$2 / (&1 + u$1 pow 2 + u$2 pow 2) /\
      (inv(&1 + norm u pow 2) %
       (vector[&2 * u$1; &2 * u$2; norm u pow 2 - &1]:real^3))$3 =
        (u$1 pow 2 + u$2 pow 2 - &1) / (&1 + u$1 pow 2 + u$2 pow 2)`,
  GEN_TAC THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_3; NORM_POW_2; DOT_2] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let MOI_PDG_ST_STI = prove
 (`!(f:real^3->real^3) u.
      orthogonal_transformation f ==> moi_pdg_st f (moi_pdg_sti f u) = u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_st; moi_pdg_sti] THEN
  ASM_SIMP_TAC[MOI_PDG_ORTH_INV] THEN
  REWRITE_TAC[MOI_PDG_STD_STI_COMPONENTS] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  SUBGOAL_THEN `&0 < &1 + (u:real^2)$1 pow 2 + u$2 pow 2` MP_TAC THENL
   [MP_TAC(SPEC `(u:real^2)$1` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `(u:real^2)$2` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    CONV_TAC REAL_FIELD]);;

let MOI_PDG_STI_SPHERE = prove
 (`!(f:real^3->real^3) u.
      orthogonal_transformation f
      ==> moi_pdg_sti f u IN sphere(vec 0,&1) /\
          ~((f(moi_pdg_sti f u))$3 = &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[moi_pdg_sti] THEN ASM_SIMP_TAC[MOI_PDG_ORTH_INV] THEN
  REWRITE_TAC[IN_SPHERE_0] THEN
  SUBGOAL_THEN `!v:real^3. norm(adjoint (f:real^3->real^3) v) = norm v`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION; ORTHOGONAL_TRANSFORMATION_ADJOINT];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_PDG_STD_STI_COMPONENTS] THEN
  SUBGOAL_THEN `&0 < &1 + (u:real^2)$1 pow 2 + u$2 pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `(u:real^2)$1` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `(u:real^2)$2` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NORM_EQ_1; DOT_3] THEN
    REWRITE_TAC[MOI_PDG_STD_STI_COMPONENTS] THEN
    UNDISCH_TAC `&0 < &1 + (u:real^2)$1 pow 2 + u$2 pow 2` THEN
    CONV_TAC REAL_FIELD;
    UNDISCH_TAC `&0 < &1 + (u:real^2)$1 pow 2 + u$2 pow 2` THEN
    CONV_TAC REAL_FIELD]);;

let MOI_PDG_STI_ST = prove
 (`!(f:real^3->real^3) y.
      orthogonal_transformation f /\ y IN sphere(vec 0,&1) /\ ~((f y)$3 = &1)
      ==> moi_pdg_sti f (moi_pdg_st f y) = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_sti; moi_pdg_st] THEN
  SUBGOAL_THEN `(f:real^3->real^3) y IN sphere(vec 0,&1)` MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_SPHERE_0]) THEN
    ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION; IN_SPHERE_0];
    ALL_TAC] THEN
  ABBREV_TAC `z = (f:real^3->real^3) y` THEN
  REWRITE_TAC[IN_SPHERE_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^3)$1 pow 2 + z$2 pow 2 + z$3 pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `norm(z:real^3) = &1` THEN
    REWRITE_TAC[NORM_EQ_1; DOT_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(&1 + norm(inv(&1 - (z:real^3)$3) % (vector[z$1; z$2]:real^2)) pow 2) %
    (vector[&2 * (inv(&1 - z$3) % (vector[z$1; z$2]:real^2))$1;
            &2 * (inv(&1 - z$3) % (vector[z$1; z$2]:real^2))$2;
            norm(inv(&1 - z$3) % (vector[z$1; z$2]:real^2)) pow 2 - &1]:real^3) = z`
  SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT; VECTOR_3;
                VECTOR_2; NORM_POW_2; DOT_2] THEN
    REPEAT CONJ_TAC THEN
    UNDISCH_TAC `(z:real^3)$1 pow 2 + z$2 pow 2 + z$3 pow 2 = &1` THEN
    UNDISCH_TAC `~((z:real^3)$3 = &1)` THEN CONV_TAC REAL_FIELD;
    EXPAND_TAC "z" THEN ASM_SIMP_TAC[MOI_PDG_ORTH_INV]]);;

let MOI_PDG_SMOOTH_VECTOR2 = prove
 (`!s (a:real^M->real) b.
      open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s (\x. lift(b x))
      ==> smooth_map_on s (\x. vector[a x; b x]:real^2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE th]) THEN
  REWRITE_TAC[DIMINDEX_2; ARITH_RULE `1 <= k /\ k <= 2 <=> k = 1 \/ k = 2`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_2; ETA_AX]);;

let MOI_PDG_SMOOTH_VECTOR3 = prove
 (`!s (a:real^M->real) b c.
      open s /\ smooth_map_on s (\x. lift(a x)) /\ smooth_map_on s (\x. lift(b x)) /\
      smooth_map_on s (\x. lift(c x))
      ==> smooth_map_on s (\x. vector[a x; b x; c x]:real^3)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [MATCH_MP SMOOTH_MAP_ON_COMPONENTWISE th]) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH_RULE `1 <= k /\ k <= 3 <=> k = 1 \/ k = 2 \/ k = 3`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3; ETA_AX]);;

let MOI_PDG_SMOOTH_COMPONENT_LINEAR = prove
 (`!s (f:real^M->real^N) k.
      open s /\ linear f ==> smooth_map_on s (\x. lift((f x)$k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
  ASM_SIMP_TAC[MOI_SMB_SMOOTH_LINEAR]);;

let MOI_PDG_ST_OPEN = prove
 (`!f:real^3->real^3. linear f ==> open {y | ~((f y)$3 = &1)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{y | ~(((f:real^3->real^3) y)$3 = &1)} =
                {y | (\y. lift((f y)$3)) y IN ((:real^1) DELETE lift(&1))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE; IN_UNIV; LIFT_EQ];
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN GEN_TAC THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[linear] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; LIFT_ADD; LIFT_CMUL]]);;

let MOI_PDG_ST_SMOOTH = prove
 (`!f:real^3->real^3.
      linear f ==> smooth_map_on {y | ~((f y)$3 = &1)} (moi_pdg_st f)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_PDG_ST_OPEN) THEN
  ABBREV_TAC `S = {y | ~(((f:real^3->real^3) y)$3 = &1)}` THEN
  SUBGOAL_THEN `moi_pdg_st (f:real^3->real^3) =
                (\y. inv(&1 - (f y)$3) % vector[(f y)$1; (f y)$2])`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_pdg_st]; ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `\y. lift(inv(&1 - ((f:real^3->real^3) y)$3))`;
                 `\y. vector[((f:real^3->real^3) y)$1; (f y)$2]:real^2`]
         SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `\y. lift(&1 - ((f:real^3->real^3) y)$3)`]
           SMOOTH_MAP_ON_LIFT_INV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; MOI_PDG_SMOOTH_COMPONENT_LINEAR];
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC MOI_PDG_SMOOTH_VECTOR2 THEN
    ASM_SIMP_TAC[MOI_PDG_SMOOTH_COMPONENT_LINEAR]]);;

let MOI_PDG_STI_SMOOTH = prove
 (`!f:real^3->real^3 s. linear f /\ open s ==> smooth_map_on s (moi_pdg_sti f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_pdg_sti (f:real^3->real^3) =
                (\u. adjoint f (inv(&1 + norm u pow 2) %
                  (vector[&2 * u$1; &2 * u$2; norm u pow 2 - &1]:real^3)))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_pdg_sti]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`;
     `\u:real^2. inv(&1 + norm u pow 2) %
                 (vector[&2 * u$1; &2 * u$2; norm u pow 2 - &1]:real^3)`;
     `adjoint(f:real^3->real^3)`] SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_SIMP_TAC[ADJOINT_LINEAR; o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `\u:real^2. lift(inv(&1 + norm u pow 2))`;
                 `\u:real^2. vector[&2 * u$1; &2 * u$2; norm u pow 2 - &1]:real^3`]
         SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `smooth_map_on s (\u:real^2. lift(norm u pow 2))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `\u:real^2. u`] SMOOTH_MAP_ON_NORM_POW2_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `\u:real^2. lift(&1 + norm u pow 2)`]
           SMOOTH_MAP_ON_LIFT_INV) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST];
      GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> ~(&1 + x = &0)`) THEN
      REWRITE_TAC[REAL_LE_POW_2]];
    MATCH_MP_TAC MOI_PDG_SMOOTH_VECTOR3 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_CMUL; LIFT_SUB] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
      ASM_SIMP_TAC[MOI_PDG_SMOOTH_COMPONENT_LINEAR; LINEAR_ID];
      MATCH_MP_TAC SMOOTH_MAP_ON_CMUL_OPEN THEN
      ASM_SIMP_TAC[MOI_PDG_SMOOTH_COMPONENT_LINEAR; LINEAR_ID];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST]]]);;

let MOI_PDG_STI_DERIV_INJ = prove
 (`!(f:real^3->real^3) u v.
      orthogonal_transformation f /\
      frechet_derivative (moi_pdg_sti f) (at u) v = vec 0
      ==> v = vec 0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  MP_TAC(ISPECL [`(:real^2)`; `moi_pdg_sti (f:real^3->real^3)`]
         SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_SIMP_TAC[OPEN_UNIV; MOI_PDG_STI_SMOOTH; IN_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^2`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{y | ~(((f:real^3->real^3) y)$3 = &1)}`; `moi_pdg_st (f:real^3->real^3)`]
         SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_SIMP_TAC[MOI_PDG_ST_OPEN; MOI_PDG_ST_SMOOTH] THEN
  DISCH_THEN(MP_TAC o SPEC `moi_pdg_sti (f:real^3->real^3) u`) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; MOI_PDG_STI_SPHERE] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_pdg_sti (f:real^3->real^3)`; `moi_pdg_st (f:real^3->real^3)`;
                 `frechet_derivative (moi_pdg_sti (f:real^3->real^3)) (at u)`;
                 `frechet_derivative (moi_pdg_st (f:real^3->real^3))
                     (at (moi_pdg_sti f u))`; `u:real^2`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_pdg_st (f:real^3->real^3) o moi_pdg_sti f = I` SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; o_THM; I_THM; MOI_PDG_ST_STI]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`I:real^2->real^2`; `I:real^2->real^2`;
       `frechet_derivative (moi_pdg_st (f:real^3->real^3)) (at (moi_pdg_sti f u)) o
        frechet_derivative (moi_pdg_sti f) (at u)`; `u:real^2`]
     FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] HAS_DERIVATIVE_ID] THEN
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (moi_pdg_st (f:real^3->real^3))
                         (at (moi_pdg_sti f u)))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_MESON_TAC[differentiable];
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP LINEAR_0)]);;

(* ------------------------------------------------------------------------- *)
(* FINAL: a map into S^2 that is a smooth immersion near every point is a   *)
(* smooth immersion in every chart and (by D5) a homeomorphism onto S^2.   *)
(* ------------------------------------------------------------------------- *)

(* Smoothness is local on open sets (copied from SMOOTH_MAP_ON_LOCAL of      *)
(* pc_mfd_maps.ml, which is not loaded here).                                *)

let MOI_PDG_SMOOTH_LOCAL = prove
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

let MOI_PDG_ATLAS_SUBSET = prove
 (`!(X:real^N->bool) sigma U (phi:real^N->real^2).
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (U,phi) IN sigma
      ==> U SUBSET X`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[OPEN_IN_IMP_SUBSET]);;

let MOI_PDG_DERIV_COMPOSE_INJ = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) x.
      f differentiable at x /\ g differentiable at (f x) /\
      (!v. frechet_derivative f (at x) v = vec 0 ==> v = vec 0) /\
      (!w. frechet_derivative g (at (f x)) w = vec 0 ==> w = vec 0)
      ==> !v. frechet_derivative (g o f) (at x) v = vec 0 ==> v = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `frechet_derivative ((g:real^N->real^P) o (f:real^M->real^N)) (at x) =
                frechet_derivative g (at (f x)) o frechet_derivative f (at x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[]]);;

let MOI_PDG_IMM_AT_CHART = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) U phi x.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      moi_pdg_imm_at sigma M x /\ (U,phi) IN sigma /\ x IN U
      ==> ?t. open t /\ phi x IN t /\ t SUBSET IMAGE phi U /\
              smooth_map_on t (\y. M(chart_inv (U,phi) y)) /\
              (!v. frechet_derivative (\y. M(chart_inv (U,phi) y)) (at (phi x)) v = vec 0
                   ==> v = vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_imm_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:real^N->bool`; `chi:real^N->real^2`;
                       `W:real^2->bool`; `g:real^2->real^3`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `tau = chart_trans (U:real^N->bool,phi:real^N->real^2) (V,chi)` THEN
  ABBREV_TAC `O = IMAGE (phi:real^N->real^2) (U INTER V)` THEN
  SUBGOAL_THEN `open(O:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (tau:real^2->real^2)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["O"; "tau"] THEN MATCH_MP_TAC CHART_TRANS_SMOOTH THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. z IN U ==> (tau:real^2->real^2) (phi z) = chi z`
  ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC CHART_TRANS_AT THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{y | y IN O /\ (tau:real^2->real^2) y IN W}` THEN
  SUBGOAL_THEN `(phi:real^N->real^2) x IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `O SUBSET IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN {y | y IN O /\ (tau:real^2->real^2) y IN W}
        ==> (M:real^N->real^3)(chart_inv (U,phi) y) = (g o tau) y`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^2) IN O` THEN EXPAND_TAC "O" THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(tau:real^2->real^2) y IN W` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open {y | y IN O /\ (tau:real^2->real^2) y IN W}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^N->real^2) x IN {y | y IN O /\ (tau:real^2->real^2) y IN W}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(g:real^2->real^3) o (tau:real^2->real^2)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `W:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:real^N->real^2) x`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `frechet_derivative (\y. (M:real^N->real^3)(chart_inv (U,phi) y)) (at (phi x)) =
    frechet_derivative ((g:real^2->real^3) o (tau:real^2->real^2)) (at (phi x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ball((phi:real^N->real^2) x,d) SUBSET
                 {y | y IN O /\ (tau:real^2->real^2) y IN W}` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_DERIV_COMPOSE_INJ THEN
  SUBGOAL_THEN `(tau:real^2->real^2) (phi(x:real^N)) = chi x` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN ASM_MESON_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN ASM_MESON_TAC[];
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                   `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `U:real^N->bool`; `phi:real^N->real^2`;
                   `V:real^N->bool`; `chi:real^N->real^2`; `x:real^N`]
                  CHART_JAC_INVERSE) THEN
    ASM_REWRITE_TAC[IN_INTER; chart_jac; FUN_EQ_THM; o_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `linear(frechet_derivative (chart_trans (V:real^N->bool,chi:real^N->real^2) (U,phi))
                           (at (chi(x:real^N))))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `IMAGE (chi:real^N->real^2) (V INTER U)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CHART_OVERLAP_IMAGE_OPEN THEN ASM_MESON_TAC[];
        CONJ_TAC THENL
         [MATCH_MP_TAC CHART_TRANS_SMOOTH THEN ASM_MESON_TAC[];
          REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[]]];
      FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP LINEAR_0)];
    ASM_MESON_TAC[]]);;

let MOI_PDG_IMM_GLOBAL = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3).
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      (!x. x IN X ==> moi_pdg_imm_at sigma M x)
      ==> smooth_immersion_into sigma M`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_immersion_into] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^2`] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN U
        ==> ?t. open t /\ (phi:real^N->real^2) x IN t /\ t SUBSET IMAGE phi U /\
                smooth_map_on t (\y. (M:real^N->real^3)(chart_inv (U,phi) y)) /\
                (!v. frechet_derivative (\y. M(chart_inv (U,phi) y)) (at (phi x)) v =
                     vec 0 ==> v = vec 0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_IMM_AT_CHART THEN
    EXISTS_TAC `X:real^N->bool` THEN EXISTS_TAC `sigma:((real^N->bool)#(real^N->real^2))->bool` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\y:real^2. (M:real^N->real^3)(chart_inv (U:real^N->bool,phi:real^N->real^2) y)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PDG_SMOOTH_LOCAL THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ASM_SIMP_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]]);;

let MOI_PDG_CHART_HOMEO = prove
 (`!(X:real^N->bool) sigma U (phi:real^N->real^2).
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (U,phi) IN sigma
      ==> homeomorphism (U,IMAGE phi U) (phi,chart_inv (U,phi))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
  ASM_SIMP_TAC[SUBTOPOLOGY_SUBTOPOLOGY; SET_RULE `(u:real^N->bool) SUBSET x ==> x INTER u = u`] THEN
  REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_EUCLIDEAN2;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y. y IN IMAGE (phi:real^N->real^2) U ==> chart_inv (U,phi) y = g y`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `g:real^2->real^N` THEN
    ASM_SIMP_TAC[]]);;

let MOI_PDG_IMM_LOCAL_HOMEO = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) x.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      IMAGE M X SUBSET sphere(vec 0,&1) /\ x IN X /\ moi_pdg_imm_at sigma M x
      ==> ?A B g. x IN A /\ open_in (subtopology euclidean X) A /\
                  open_in (subtopology euclidean (sphere(vec 0,&1))) B /\
                  homeomorphism (A,B) (M,g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_imm_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^2`;
                       `W:real^2->bool`; `k:real^2->real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN W ==> (k:real^2->real^3) y IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^2) IN IMAGE (phi:real^N->real^2) U` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((M:real^N->real^3) x) = norm(--basis 3:real^3)` MP_TAC THENL
   [REWRITE_TAC[NORM_NEG] THEN SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[GSYM IN_SPHERE_0] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  ABBREV_TAC `S = {p | ~(((f:real^3->real^3) p)$3 = &1)}` THEN
  SUBGOAL_THEN `open(S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[MOI_PDG_ST_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (moi_pdg_st (f:real^3->real^3))` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[MOI_PDG_ST_SMOOTH]; ALL_TAC] THEN
  ABBREV_TAC `W' = {y | y IN W /\ (k:real^2->real^3) y IN S}` THEN
  SUBGOAL_THEN `open(W':real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "W'" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^N->real^2) x IN W'` ASSUME_TAC THENL
   [EXPAND_TAC "W'" THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[] THEN
    SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Fs = moi_pdg_st (f:real^3->real^3) o (k:real^2->real^3)` THEN
  SUBGOAL_THEN `smooth_map_on W' (Fs:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "Fs" THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `S:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [EXPAND_TAC "W'" THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "W'" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN W' ==> (k:real^2->real^3) y = moi_pdg_sti f (Fs y)`
  ASSUME_TAC THENL
   [EXPAND_TAC "W'" THEN EXPAND_TAC "Fs" THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PDG_STI_ST THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. frechet_derivative (Fs:real^2->real^2) (at (phi(x:real^N))) v = vec 0
        ==> v = vec 0`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `(phi:real^N->real^2) x`) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `(phi:real^N->real^2) x`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `frechet_derivative (k:real^2->real^3) (at (phi(x:real^N))) =
      frechet_derivative (moi_pdg_sti f o (Fs:real^2->real^2)) (at (phi x))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC FRECHET_DERIVATIVE_LOCAL THEN EXISTS_TAC `d:real` THEN
      ASM_REWRITE_TAC[o_THM] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `ball((phi:real^N->real^2) x,d) SUBSET W'` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `frechet_derivative (moi_pdg_sti f o (Fs:real^2->real^2)) (at (phi(x:real^N))) =
      frechet_derivative (moi_pdg_sti f) (at (Fs(phi x))) o
      frechet_derivative Fs (at (phi x))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
       [EXISTS_TAC `W':real^2->bool` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `(:real^2)` THEN
        ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `linear(frechet_derivative (moi_pdg_sti (f:real^3->real^3))
                           (at ((Fs:real^2->real^2)(phi(x:real^N)))))` ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH];
      FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP LINEAR_0)];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(det(matrix(frechet_derivative (Fs:real^2->real^2) (at (phi(x:real^N))))) = &0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
    SUBGOAL_THEN `linear(frechet_derivative (Fs:real^2->real^2) (at (phi(x:real^N))))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `W':real^2->bool` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Fs:real^2->real^2`; `W':real^2->bool`; `(phi:real^N->real^2) x`]
         SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (X_CHOOSE_THEN `u:real^2->bool`
    (X_CHOOSE_THEN `G:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] MOI_PDG_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `{z | z IN U /\ (phi:real^N->real^2) z IN t}` THEN
  EXISTS_TAC `IMAGE (moi_pdg_sti (f:real^3->real^3)) u` THEN
  EXISTS_TAC `chart_inv (U:real^N->bool,phi:real^N->real^2) o (G:real^2->real^2) o
              moi_pdg_st (f:real^3->real^3)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM];
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `U:real^N->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `homeomorphism (U,IMAGE (phi:real^N->real^2) U) (phi,chart_inv (U,phi))` THEN
      SIMP_TAC[homeomorphism];
      MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `U:real^N->bool`; `phi:real^N->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[]];
    SUBGOAL_THEN
     `IMAGE (moi_pdg_sti (f:real^3->real^3)) u =
      sphere(vec 0,&1) INTER {p | p IN S /\ moi_pdg_st f p IN u}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `p:real^3` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
        ASM_SIMP_TAC[MOI_PDG_STI_SPHERE; MOI_PDG_ST_STI] THEN
        EXPAND_TAC "S" THEN ASM_SIMP_TAC[IN_ELIM_THM; MOI_PDG_STI_SPHERE];
        STRIP_TAC THEN EXISTS_TAC `moi_pdg_st (f:real^3->real^3) p` THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MOI_PDG_STI_ST THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(p:real^3) IN S` THEN EXPAND_TAC "S" THEN
        REWRITE_TAC[IN_ELIM_THM]];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t SUBSET IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(t:real^2->bool) SUBSET W'`;
                          `(W:real^2->bool) SUBSET IMAGE (phi:real^N->real^2) U`] THEN
    EXPAND_TAC "W'" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism ({z | z IN U /\ (phi:real^N->real^2) z IN t},t)
                  (phi,chart_inv (U,phi))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `IMAGE (phi:real^N->real^2) U`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (t,u) (Fs:real^2->real^2,G)` ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on t u (Fs:real^2->real^2) G` THEN
    REWRITE_TAC[diffeomorphism_on; homeomorphism] THEN
    MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism (u,IMAGE (moi_pdg_sti (f:real^3->real^3)) u)
                  (moi_pdg_sti f,moi_pdg_st f)`
  ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[MOI_PDG_ST_STI] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC MOI_PDG_STI_SMOOTH THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[MOI_PDG_ST_STI];
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_SIMP_TAC[MOI_PDG_ST_STI] THEN
      REWRITE_TAC[IMAGE_ID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^3->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "S" THEN
      ASM_SIMP_TAC[IN_ELIM_THM; MOI_PDG_STI_SPHERE]];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`moi_pdg_sti (f:real^3->real^3) o (Fs:real^2->real^2) o (phi:real^N->real^2)`;
    `(chart_inv (U:real^N->bool,phi:real^N->real^2) o (G:real^2->real^2)) o
     moi_pdg_st (f:real^3->real^3)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `u:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `t:real^2->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[o_THM; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(phi:real^N->real^2) z IN W'` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(phi:real^N->real^2) z IN W` ASSUME_TAC THENL
     [UNDISCH_TAC `(phi:real^N->real^2) z IN W'` THEN EXPAND_TAC "W'" THEN
      SIMP_TAC[IN_ELIM_THM];
      ASM_MESON_TAC[]]]);;

let MOI_PDG_FINAL = prove
 (`!(u:N->bool) (X:real^N->bool) sigma (M:real^N->real^3).
      MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT u /\
      compact X /\ connected X /\ locally path_connected X /\ ~(X = {}) /\
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      IMAGE M X SUBSET sphere(vec 0,&1) /\
      (!x. x IN X ==> moi_pdg_imm_at sigma M x)
      ==> ?M'. homeomorphism (X,sphere(vec 0,&1)) (M,M') /\
               smooth_immersion_into sigma M`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`X:real^N->bool`; `M:real^N->real^3`] o
                GEN_REWRITE_RULE I [MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_PDG_IMM_LOCAL_HOMEO THEN
    EXISTS_TAC `sigma:((real^N->bool)#(real^N->real^2))->bool` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[MOI_PDG_IMM_GLOBAL]]);;

(* ------------------------------------------------------------------------- *)
(* Gluing one-sided smooth extensions along a segment (1D partition of     *)
(* unity by smooth steps): input of the crease smoothing D3.              *)
(* ------------------------------------------------------------------------- *)

let MOI_PDG_HALF_BASIS = prove
 (`!c r (x:complex) i e.
      x IN ball(c,r) /\ &0 <= Im x /\ 1 <= i /\ i <= 2 /\ &0 < e
      ==> ?d. &0 < abs d /\ abs d < e /\ x + d % basis i IN ball(c,r) /\
              &0 <= Im(x + d % basis i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_BALL] THEN
  UNDISCH_TAC `(x:complex) IN ball(c,r)` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
  EXISTS_TAC `min (e / &2) ((r - dist(c:complex,x)) / &2)` THEN
  SUBGOAL_THEN `norm(basis i:complex) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC NORM_BASIS THEN ASM_REWRITE_TAC[DIMINDEX_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (basis i:complex)$2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH_RULE `1 <= 2 /\ 2 <= 2`] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(REAL_ARITH `&0 < e /\ dist(c:complex,x) < r
     ==> &0 < abs (min (e / &2) ((r - dist (c,x)) / &2)) /\
         abs (min (e / &2) ((r - dist (c,x)) / &2)) < e /\
         abs (min (e / &2) ((r - dist (c,x)) / &2)) < r - dist(c,x) /\
         &0 <= min (e / &2) ((r - dist (c,x)) / &2)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
      `norm(y:complex) < r - dist(c,x) ==> dist(c,x + y) < r`) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID];
    REWRITE_TAC[IM_ADD; IM_DEF; VECTOR_MUL_COMPONENT] THEN
    UNDISCH_TAC `&0 <= Im x` THEN REWRITE_TAC[IM_DEF] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a * b ==> &0 <= x ==> &0 <= x + a * b`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_DERIV_HALF = prove
 (`!(f:complex->real^M) g c r x.
      f differentiable at x /\ g differentiable at x /\
      x IN ball(c,r) /\ &0 <= Im x /\
      (!y. y IN ball(c,r) /\ &0 <= Im y ==> f y = g y)
      ==> frechet_derivative f (at x) = frechet_derivative g (at x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {y | y IN ball(c:complex,r) /\ &0 <= Im y}` THEN
  SUBGOAL_THEN `(x:complex) IN s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. (f:complex->real^M) y - g y) has_derivative
     (\h. frechet_derivative f (at x) h - frechet_derivative g (at x) h))
    (at x within s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. (f:complex->real^M) y - g y) has_derivative (\h. vec 0)) (at x within s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
    EXISTS_TAC `\y:complex. vec 0:real^M` THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[REAL_LT_01; HAS_DERIVATIVE_CONST] THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[VECTOR_SUB_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. (f:complex->real^M) y - g y`;
                 `\h. frechet_derivative (f:complex->real^M) (at x) h -
                      frechet_derivative g (at x) h`;
                 `\h:complex. vec 0:real^M`; `x:complex`; `s:complex->bool`]
         FRECHET_DERIVATIVE_UNIQUE_WITHIN) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_2] THEN MAP_EVERY X_GEN_TAC [`i:num`; `e:real`] THEN
    STRIP_TAC THEN EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MOI_PDG_HALF_BASIS THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_EQ] THEN REWRITE_TAC[ETA_AX] THEN MESON_TAC[]]);;

let MOI_PDG_JAC_DET_2 = prove
 (`!(f:real^2->real^2) x.
      det(jacobian f (at x)) =
      (partial_derivative 1 f x)$1 * (partial_derivative 2 f x)$2 -
      (partial_derivative 2 f x)$1 * (partial_derivative 1 f x)$2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DET_2; jacobian; partial_derivative] THEN
  SIMP_TAC[MATRIX_COMPONENT; DIMINDEX_2; ARITH]);;

let MOI_PDG_JAC_DET_SMOOTH = prove
 (`!s (f:real^2->real^2).
      open s /\ smooth_map_on s f
      ==> smooth_map_on s (\x. lift(det(jacobian f (at x))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_PDG_JAC_DET_2] THEN
  MATCH_MP_TAC MOI_SMB_SL_SUB THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i k. smooth_map_on s (\x. lift((partial_derivative i (f:real^2->real^2) x)$k))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `partial_derivative i (f:real^2->real^2)`; `k:num`]
           SMOOTH_MAP_ON_LIFT_COMPONENT) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_PARTIAL_DERIVATIVE];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_SMB_SL_MUL THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_JAC_DET_CONT = prove
 (`!s (f:real^2->real^2).
      open s /\ smooth_map_on s f
      ==> (\x. lift(det(jacobian f (at x)))) continuous_on s`,
  MESON_TAC[MOI_PDG_JAC_DET_SMOOTH; SMOOTH_MAP_ON_CONTINUOUS_ON]);;

let MOI_PDG_SEG_COMPACT = prove
 (`!a b. compact {Cx t | a <= t /\ t <= b}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{Cx t | a <= t /\ t <= b} = IMAGE (\x. Cx(drop x)) (interval[lift a,lift b])`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTERVAL_1] THEN
    MESON_TAC[LIFT_DROP];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL]]);;

let MOI_PDG_STRIP_THIN = prove
 (`!V a b. open V /\ (!t. a <= t /\ t <= b ==> Cx t IN V)
           ==> ?d. &0 < d /\
                   !x. a <= Re x /\ Re x <= b /\ abs(Im x) <= d ==> x IN V`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(:complex) DIFF V = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `{Cx t | a <= t /\ t <= b} = {}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `{Cx t | a <= t /\ t <= b} = {}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `Cx(Re x)`) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K = {Cx t | a <= t /\ t <= b}` THEN
  SUBGOAL_THEN `&0 < setdist(K,(:complex) DIFF V)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
    REWRITE_TAC[SETDIST_POS_LE] THEN
    MP_TAC(ISPECL [`K:complex->bool`; `(:complex) DIFF V`] SETDIST_EQ_0_COMPACT_CLOSED) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[MOI_PDG_SEG_COMPACT] THEN
      ASM_REWRITE_TAC[GSYM OPEN_CLOSED];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "K" THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `setdist(K,(:complex) DIFF V) / &2` THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:complex) IN V` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:complex->bool`; `(:complex) DIFF V`; `Cx(Re x)`; `x:complex`]
         SETDIST_LE_DIST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `Re x` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(Cx(Re x),x) = abs(Im x)` SUBST1_TAC THENL
   [REWRITE_TAC[dist; COMPLEX_NORM_GE_RE_IM] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
    REWRITE_TAC[COMPLEX_RING `Cx a - (Cx a + ii * Cx b) = --(ii * Cx b)`] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_MUL; COMPLEX_NORM_II; COMPLEX_NORM_CX] THEN
    REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let MOI_PDG_FINITE_POS_MIN = prove
 (`!(f:A->real) s. FINITE s /\ (!x. x IN s ==> &0 < f x)
                   ==> ?d. &0 < d /\ !x. x IN s ==> d <= f x`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01];
    MAP_EVERY X_GEN_TAC [`y:A`; `s:A->bool`] THEN REWRITE_TAC[IN_INSERT] THEN
    STRIP_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d ((f:A->real) y)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_LT_MIN] THEN ASM_MESON_TAC[];
      X_GEN_TAC `x:A` THEN STRIP_TAC THENL
       [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `d <= z ==> min d y <= z`) THEN ASM_MESON_TAC[]]]]);;

let MOI_PDG_UNIFORM_RADIUS = prove
 (`!(K:complex->bool) (Q:complex->real->bool).
      compact K /\
      (!z r z' r'. Q z r /\ ball(z',r') SUBSET ball(z,r) ==> Q z' r') /\
      (!z. z IN K ==> ?r. &0 < r /\ Q z r)
      ==> ?d. &0 < d /\ !z. z IN K ==> Q z d`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:complex->real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_HEINE_BOREL) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\z. ball(z:complex,rr z / &2)) K`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:complex` THEN DISCH_TAC THEN EXISTS_TAC `z:complex` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_HALF] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:(complex->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\z. ball(z:complex,rr z / &2)`; `K:complex->bool`;
                 `ff:(complex->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:complex->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `K SUBSET UNIONS (ff:(complex->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\z:complex. rr z / &2`; `F0:complex->bool`] MOI_PDG_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_HALF] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z':complex` THEN DISCH_TAC THEN
  UNDISCH_TAC `K SUBSET UNIONS (IMAGE (\z. ball(z:complex,rr z / &2)) F0)` THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `z':complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o
    SPECL [`z:complex`; `(rr:complex->real) z`; `z':complex`; `d:real`]) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET];
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `w:complex` THEN
    UNDISCH_TAC `(z':complex) IN ball(z,rr z / &2)` THEN REWRITE_TAC[IN_BALL] THEN
    SUBGOAL_THEN `d <= (rr:complex->real) z / &2` MP_TAC THENL
     [RULE_ASSUM_TAC BETA_RULE THEN ASM_SIMP_TAC[]; CONV_TAC NORM_ARITH]]);;

let MOI_PDG_STEP_SMOOTH = prove
 (`!c eta s. open s ==> smooth_map_on s (\x:complex. lift(smooth_step((Re x - c) / eta)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:complex->bool`; `\x:complex. lift((Re x - c) / eta)`]
         SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC MOI_SMB_SL_MUL THEN ASM_REWRITE_TAC[MOI_SMB_SL_CONST] THEN
  MATCH_MP_TAC MOI_SMB_SL_SUB THEN ASM_REWRITE_TAC[MOI_SMB_SL_CONST; RE_DEF] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_COMPONENT THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID]);;

let MOI_PDG_STEP_0 = prove
 (`!c eta x. &0 < eta /\ Re x <= c ==> smooth_step((Re x - c) / eta) = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_STEP_1 = prove
 (`!c eta x. &0 < eta /\ c + eta <= Re x ==> smooth_step((Re x - c) / eta) = &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_PIECE_SMOOTH = prove
 (`!(G:complex->real^M) c1 c2 eta u z0 r.
      &0 < eta /\ c1 < c2 /\ open u /\ smooth_map_on (ball(z0,r)) G /\
      (!x. x IN u /\ c1 <= Re x /\ Re x <= c2 + eta ==> x IN ball(z0,r))
      ==> smooth_map_on u
            (\x. (smooth_step((Re x - c1) / eta) - smooth_step((Re x - c2) / eta)) % G x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_SMOOTH_LOCAL THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
  ASM_CASES_TAC `c1 <= Re y /\ Re y <= c2 + eta` THENL
   [EXISTS_TAC `u INTER ball(z0:complex,r)` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER] THEN
    MP_TAC(ISPECL [`u INTER ball(z0:complex,r)`;
       `\x:complex. lift(smooth_step((Re x - c1) / eta) - smooth_step((Re x - c2) / eta))`;
       `G:complex->real^M`] SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
    REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SMB_SL_SUB THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; MOI_PDG_STEP_SMOOTH];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:complex,r)` THEN
      ASM_REWRITE_TAC[INTER_SUBSET]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o REWRITE_RULE[DE_MORGAN_THM; REAL_NOT_LE]) THENL
   [EXISTS_TAC `u INTER {x:complex | Re x < c1}` THEN
    SUBGOAL_THEN `open(u INTER {x:complex | Re x < c1})` ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER; OPEN_HALFSPACE_RE_LT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\x:complex. vec 0:real^M` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_INTER; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `smooth_step((Re x - c1) / eta) = &0 /\ smooth_step((Re x - c2) / eta) = &0`
     (fun th -> REWRITE_TAC[th; REAL_SUB_REFL; VECTOR_MUL_LZERO]) THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_STEP_0 THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `u INTER {x:complex | c2 + eta < Re x}` THEN
    SUBGOAL_THEN `open(u INTER {x:complex | c2 + eta < Re x})` ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_RE_GT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\x:complex. vec 0:real^M` THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_CONST; IN_INTER; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `smooth_step((Re x - c1) / eta) = &1 /\ smooth_step((Re x - c2) / eta) = &1`
     (fun th -> REWRITE_TAC[th; REAL_SUB_REFL; VECTOR_MUL_LZERO]) THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_STEP_1 THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_ARCH_STEP = prove
 (`!L c. &0 < c ==> ?N. 1 <= N /\ L / &N <= c`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `L / c` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n + 1` THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(n + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  UNDISCH_TAC `L / c <= &n` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `c * (&n + &1) = &n * c + c` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let MOI_PDG_GLUE = prove
 (`!(F0:complex->real^2) (H:complex->real^2) a b e.
      a < b /\ &0 < e /\ &2 * e < b - a /\
      (!t. a <= t /\ t <= b
           ==> ?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:complex->real^2) /\
                     (!x. x IN ball(Cx t,r) /\ &0 <= Im x ==> g x = F0 x) /\
                     ~(det(jacobian g (at (Cx t))) = &0)) /\
      (!t. a <= t /\ t <= a + e \/ b - e <= t /\ t <= b
           ==> ?r. &0 < r /\ smooth_map_on (ball(Cx t,r)) H /\
                   (!x. x IN ball(Cx t,r) /\ &0 <= Im x ==> H x = F0 x))
      ==> ?d u Fp. &0 < d /\ open u /\
                   {x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d} SUBSET u /\
                   smooth_map_on u (Fp:complex->real^2) /\
                   (!x. a <= Re x /\ Re x <= b /\ &0 <= Im x /\ Im x <= d
                        ==> Fp x = F0 x) /\
                   (!x. (a <= Re x /\ Re x <= a + e / &2 \/
                         b - e / &2 <= Re x /\ Re x <= b) /\ abs(Im x) <= d
                        ==> Fp x = H x) /\
                   (!x. a <= Re x /\ Re x <= b /\ abs(Im x) <= d
                        ==> ~(det(jacobian Fp (at x)) = &0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gen") (LABEL_TAC "end"))))) THEN
  (* uniform radii *)
  MP_TAC(ISPECL [`{Cx t | a <= t /\ t <= b}`;
     `\z r. ?g. smooth_map_on (ball(z,r)) (g:complex->real^2) /\
                (!x. x IN ball(z,r) /\ &0 <= Im x ==> g x = F0 x)`]
     MOI_PDG_UNIFORM_RADIUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_PDG_SEG_COMPACT; FORALL_IN_GSPEC] THEN BETA_TAC THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN ASM_MESON_TAC[]; ASM SET_TAC[]];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      REMOVE_THEN "gen" (MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[]];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "u1")))] THEN
  MP_TAC(ISPECL [`{Cx t | a <= t /\ t <= a + e}`;
     `\z r. smooth_map_on (ball(z,r)) (H:complex->real^2) /\
            (!x. x IN ball(z,r) /\ &0 <= Im x ==> H x = F0 x)`]
     MOI_PDG_UNIFORM_RADIUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_PDG_SEG_COMPACT; FORALL_IN_GSPEC] THEN BETA_TAC THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN ASM_MESON_TAC[]; ASM SET_TAC[]];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "end" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "u2")))] THEN
  MP_TAC(ISPECL [`{Cx t | b - e <= t /\ t <= b}`;
     `\z r. smooth_map_on (ball(z,r)) (H:complex->real^2) /\
            (!x. x IN ball(z,r) /\ &0 <= Im x ==> H x = F0 x)`]
     MOI_PDG_UNIFORM_RADIUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_PDG_SEG_COMPACT; FORALL_IN_GSPEC] THEN BETA_TAC THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN ASM_MESON_TAC[]; ASM SET_TAC[]];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "end" (MP_TAC o SPEC `t:real`) THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN BETA_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `d3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "u3")))] THEN
  ABBREV_TAC `del = min d1 (min d2 d3)` THEN
  SUBGOAL_THEN `&0 < del /\ del <= d1 /\ del <= d2 /\ del <= d3` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "del" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "u1" (MP_TAC o GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `gg:real->complex->real^2` (LABEL_TAC "gg")) THEN
  MP_TAC(ISPECL [`b - a:real`; `min (del / &4) (e / &4)`] MOI_PDG_ARCH_STEP) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < (b - a) / &N /\ (b - a) / &N <= del / &4 /\
                (b - a) / &N <= e / &4 /\ &N * (b - a) / &N = b - a`
  MP_TAC THENL
   [SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `h = (b - a) / &N` THEN STRIP_TAC THEN
  ABBREV_TAC `G = \k. if a + &k * h <= a + e \/ b - e <= a + &k * h then H
                      else (gg:real->complex->real^2) (a + &k * h)` THEN
  ABBREV_TAC `sig = \k x. smooth_step((Re x - (a - h / &2 + &k * h)) / (h / &4))` THEN
  ABBREV_TAC `Fp = \x. vsum (0..N) (\k. ((sig:num->complex->real) k x - sig (k + 1) x) %
                                         (G:num->complex->real^2) k x)` THEN
  ABBREV_TAC `u = {x:complex | abs(Im x) < del / &2}` THEN
  SUBGOAL_THEN `open(u:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    REWRITE_TAC[REAL_ARITH `abs x < d <=> x < d /\ x > --d`] THEN
    REWRITE_TAC[SET_RULE `{x:complex | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_HALFSPACE_IM_LT; OPEN_HALFSPACE_IM_GT];
    ALL_TAC] THEN
  (* G k: smooth on the ball of radius del around the k-th grid point *)
  SUBGOAL_THEN
   `!k. k <= N
        ==> smooth_map_on (ball(Cx(a + &k * h),del)) ((G:num->complex->real^2) k) /\
            (!x. x IN ball(Cx(a + &k * h),del) /\ &0 <= Im x ==> G k x = F0 x)`
  (LABEL_TAC "G") THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `a <= a + &k * h /\ a + &k * h <= b` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> a <= a + x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `x <= b - a ==> a + x <= b`) THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `&N * h = b - a`)) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `ball(Cx(a + &k * h),del) SUBSET ball(Cx(a + &k * h),d1) /\
                  ball(Cx(a + &k * h),del) SUBSET ball(Cx(a + &k * h),d2) /\
                  ball(Cx(a + &k * h),del) SUBSET ball(Cx(a + &k * h),d3)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "G" THEN BETA_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC) THENL
       [USE_THEN "u2" (MP_TAC o SPEC `a + &k * h`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
          EXISTS_TAC `ball(Cx(a + &k * h),d2)` THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]];
        USE_THEN "u3" (MP_TAC o SPEC `a + &k * h`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
          EXISTS_TAC `ball(Cx(a + &k * h),d3)` THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]]];
      USE_THEN "gg" (MP_TAC o SPEC `a + &k * h`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `ball(Cx(a + &k * h),d1)` THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  (* support of the k-th cut-off and the geometry of the pieces *)
  SUBGOAL_THEN
   `!k x. ~((sig:num->complex->real) k x - sig (k + 1) x = &0)
          ==> a - h / &2 + &k * h < Re x /\ Re x < a + &k * h + &3 * h / &4`
  (LABEL_TAC "supp") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "sig" THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LT] THEN STRIP_TAC THENL
     [SUBGOAL_THEN
       `smooth_step ((Re x - (a - h / &2 + &k * h)) / (h / &4)) = &0 /\
        smooth_step ((Re x - (a - h / &2 + (&k + &1) * h)) / (h / &4)) = &0`
       (fun th -> REWRITE_TAC[th; REAL_SUB_REFL]) THEN
      CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_STEP_0 THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN
       `smooth_step ((Re x - (a - h / &2 + &k * h)) / (h / &4)) = &1 /\
        smooth_step ((Re x - (a - h / &2 + (&k + &1) * h)) / (h / &4)) = &1`
       (fun th -> REWRITE_TAC[th; REAL_SUB_REFL]) THEN
      CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_STEP_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k x. x IN u /\ a - h / &2 + &k * h <= Re x /\
          Re x <= (a - h / &2 + &(k + 1) * h) + h / &4
          ==> x IN ball(Cx(a + &k * h),del)`
  (LABEL_TAC "geo") THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "u" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_BALL; GSYM REAL_OF_NUM_ADD] THEN STRIP_TAC THEN
    REWRITE_TAC[dist] THEN
    MP_TAC(SPEC `Cx(a + &k * h) - x` COMPLEX_NORM_LE_RE_IM) THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on u (Fp:complex->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "Fp" THEN
    MP_TAC(ISPECL [`u:complex->bool`;
                   `\k x. ((sig:num->complex->real) k x - sig (k + 1) x) %
                          (G:num->complex->real^2) k x`;
                   `0..N`] SMOOTH_MAP_ON_VSUM_OPEN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN EXPAND_TAC "sig" THEN BETA_TAC THEN
    MATCH_MP_TAC MOI_PDG_PIECE_SMOOTH THEN
    MAP_EVERY EXISTS_TAC [`Cx(a + &k * h)`; `del:real`] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < h` THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN UNDISCH_TAC `&0 < h` THEN REAL_ARITH_TAC;
      ASM_REWRITE_TAC[];
      USE_THEN "G" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; SIMP_TAC[ETA_AX]];
      USE_THEN "geo" (MATCH_ACCEPT_TAC o SPEC `k:num`)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. a - h / &4 <= Re x /\ Re x <= b + h / &4
        ==> sum(0..N) (\k. (sig:num->complex->real) k x - sig (k + 1) x) = &1`
  (LABEL_TAC "sum1") THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`0`; `N:num`]
      (INST [`\k. (sig:num->complex->real) k x`,`f:num->real`] SUM_DIFFS)) THEN
    BETA_TAC THEN REWRITE_TAC[LE_0] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "sig" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `smooth_step ((Re x - (a - h / &2 + &0 * h)) / (h / &4)) = &1 /\
      smooth_step ((Re x - (a - h / &2 + &(N + 1) * h)) / (h / &4)) = &0`
     (fun th -> REWRITE_TAC[th] THEN REAL_ARITH_TAC) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PDG_STEP_1 THEN
      UNDISCH_TAC `&0 < h` THEN UNDISCH_TAC `a - h / &4 <= Re x` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_PDG_STEP_0 THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      UNDISCH_TAC `&0 < h` THEN UNDISCH_TAC `Re x <= b + h / &4` THEN
      UNDISCH_TAC `&N * h = b - a` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN u /\ a - h / &4 <= Re x /\ Re x <= b + h / &4 /\ &0 <= Im x
        ==> (Fp:complex->real^2) x = F0 x`
  (LABEL_TAC "val") THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN EXPAND_TAC "Fp" THEN BETA_TAC THEN
    TRANS_TAC EQ_TRANS
     `vsum (0..N) (\k. ((sig:num->complex->real) k x - sig (k + 1) x) %
                       (F0:complex->real^2) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(sig:num->complex->real) k x - sig (k + 1) x = &0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN AP_TERM_TAC THEN
      USE_THEN "supp" (MP_TAC o SPECL [`k:num`; `x:complex`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "G" (MP_TAC o SPEC `k:num`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_THEN(MATCH_MP_TAC o CONJUNCT2)] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "geo" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      MAP_EVERY UNDISCH_TAC
       [`a - h / &2 + &k * h < Re x`; `Re x < a + &k * h + &3 * h / &4`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[VSUM_RMUL] THEN USE_THEN "sum1" (MP_TAC o SPEC `x:complex`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[VECTOR_MUL_LID]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. (a <= Re x /\ Re x <= a + e / &2 \/ b - e / &2 <= Re x /\ Re x <= b)
        ==> (Fp:complex->real^2) x = H x`
  (LABEL_TAC "ends") THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN EXPAND_TAC "Fp" THEN BETA_TAC THEN
    TRANS_TAC EQ_TRANS
     `vsum (0..N) (\k. ((sig:num->complex->real) k x - sig (k + 1) x) %
                       (H:complex->real^2) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(sig:num->complex->real) k x - sig (k + 1) x = &0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN AP_TERM_TAC THEN
      USE_THEN "supp" (MP_TAC o SPECL [`k:num`; `x:complex`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      EXPAND_TAC "G" THEN BETA_TAC THEN
      SUBGOAL_THEN `a + &k * h <= a + e \/ b - e <= a + &k * h`
        (fun th -> REWRITE_TAC[th]) THEN
      MAP_EVERY UNDISCH_TAC
       [`a - h / &2 + &k * h < Re x`; `Re x < a + &k * h + &3 * h / &4`;
        `h <= e / &4`;
        `a <= Re x /\ Re x <= a + e / &2 \/ b - e / &2 <= Re x /\ Re x <= b`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[VSUM_RMUL] THEN USE_THEN "sum1" (MP_TAC o SPEC `x:complex`) THEN
      ANTS_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`&0 < h`; `a < b`;
          `a <= Re x /\ Re x <= a + e / &2 \/ b - e / &2 <= Re x /\ Re x <= b`;
          `&2 * e < b - a`] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[VECTOR_MUL_LID]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN u ==> (Fp:complex->real^2) differentiable at x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `u:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. Cx t IN u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM; IM_CX] THEN
    UNDISCH_TAC `&0 < del` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b ==> ~(det(jacobian (Fp:complex->real^2) (at (Cx t))) = &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "gen" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `g:complex->real^2`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `frechet_derivative (Fp:complex->real^2) (at (Cx t)) =
      frechet_derivative g (at (Cx t))`
     (fun th -> UNDISCH_TAC `~(det(jacobian (g:complex->real^2) (at (Cx t))) = &0)` THEN
                REWRITE_TAC[jacobian; th]) THEN
    MATCH_MP_TAC MOI_PDG_DERIV_HALF THEN
    MAP_EVERY EXISTS_TAC [`Cx t`; `min r (min (h / &4) (del / &4))`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(Cx t,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
      REWRITE_TAC[CENTRE_IN_BALL] THEN
      MAP_EVERY UNDISCH_TAC [`&0 < r`; `&0 < h`; `&0 < del`] THEN REAL_ARITH_TAC;
      REWRITE_TAC[IM_CX; REAL_LE_REFL];
      X_GEN_TAC `y:complex` THEN REWRITE_TAC[IN_BALL] THEN STRIP_TAC THEN
      TRANS_TAC EQ_TRANS `(F0:complex->real^2) y` THEN CONJ_TAC THENL
       [USE_THEN "val" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `Cx t - y` COMPLEX_NORM_GE_RE_IM) THEN
        UNDISCH_TAC `dist(Cx t,y) < min r (min (h / &4) (del / &4))` THEN
        EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM; dist; RE_SUB; IM_SUB; RE_CX; IM_CX] THEN
        MAP_EVERY UNDISCH_TAC [`a <= t`; `t <= b`; `&0 < h`; `&0 < del`] THEN
        REAL_ARITH_TAC;
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_BALL] THEN
        UNDISCH_TAC `dist(Cx t,y) < min r (min (h / &4) (del / &4))` THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{x | x IN u /\ (\x. lift(det(jacobian (Fp:complex->real^2) (at x)))) x IN
                                 ((:real^1) DELETE (vec 0))}`; `a:real`; `b:real`]
         MOI_PDG_STRIP_THIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[MOI_PDG_JAC_DET_CONT; OPEN_DELETE; OPEN_UNIV];
      REWRITE_TAC[IN_ELIM_THM; IN_DELETE; IN_UNIV; GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_DELETE; IN_UNIV; GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`min d0 (del / &4)`; `u:complex->bool`; `Fp:complex->real^2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < d0`; `&0 < del`] THEN REAL_ARITH_TAC;
    EXPAND_TAC "u" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    UNDISCH_TAC `&0 < del` THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "val" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "u" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < h`; `&0 <= Im x`; `Im x <= min d0 (del / &4)`;
                          `&0 < del`; `a <= Re x`; `Re x <= b`] THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "ends" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (is_forall o concl)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `abs(Im x) <= min d0 (del / &4)` THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Single crease: reflections, rigid motions, the stereographic pole, and  *)
(* one-sided extensions in stereographic coordinates.                       *)
(* ------------------------------------------------------------------------- *)

let MOI_PDG_OPEN_CNJ_IMAGE = prove
 (`!u. open u ==> open (IMAGE cnj u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cnj`; `u:complex->bool`] OPEN_BIJECTIVE_LINEAR_IMAGE_EQ) THEN
  ASM_REWRITE_TAC[LINEAR_CNJ] THEN DISCH_THEN MATCH_MP_TAC THEN
  MESON_TAC[CNJ_CNJ]);;

let MOI_PDG_DET_MATRIX_CNJ = prove
 (`det(matrix cnj) = -- &1`,
  REWRITE_TAC[DET_2] THEN SIMP_TAC[MATRIX_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[COMPLEX_BASIS; CNJ_II; CNJ_CX] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_CX; IM_CX; RE_NEG; IM_NEG; RE_II; IM_II] THEN
  REAL_ARITH_TAC);;

let MOI_PDG_JAC_CNJ = prove
 (`!(g:complex->real^2) x.
      g differentiable at (cnj x)
      ==> det(jacobian (g o cnj) (at x)) = --det(jacobian g (at (cnj x)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN
  SUBGOAL_THEN `frechet_derivative ((g:complex->real^2) o cnj) (at x) =
                frechet_derivative g (at (cnj x)) o cnj`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_CNJ; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (g:complex->real^2) (at (cnj x)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_CNJ; DET_MUL; MOI_PDG_DET_MATRIX_CNJ] THEN
  REAL_ARITH_TAC);;

let MOI_PDG_CNJ_BALL = prove
 (`!t r z. cnj z IN ball(Cx t,r) <=> z IN ball(Cx t,r)`,
  REWRITE_TAC[IN_BALL; dist] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `Cx t - cnj z = cnj(Cx t - z)` SUBST1_TAC THENL
   [REWRITE_TAC[CNJ_SUB; CNJ_CX]; REWRITE_TAC[COMPLEX_NORM_CNJ]]);;

let MOI_PDG_SMOOTH_CNJ_COMPOSE = prove
 (`!(g:complex->real^M) s.
      open s /\ smooth_map_on s g /\ (!z. cnj z IN s <=> z IN s)
      ==> smooth_map_on s (g o cnj)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `s:complex->bool` THEN
  ASM_SIMP_TAC[MOI_SMB_SMOOTH_LINEAR; LINEAR_CNJ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_DERIV_HALF_LOWER = prove
 (`!(f:complex->real^M) g c r x.
      f differentiable at x /\ g differentiable at x /\
      x IN ball(Cx c,r) /\ Im x <= &0 /\
      (!y. y IN ball(Cx c,r) /\ Im y <= &0 ==> f y = g y)
      ==> frechet_derivative f (at x) = frechet_derivative g (at x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `frechet_derivative ((f:complex->real^M) o cnj) (at (cnj x)) =
                frechet_derivative (g o cnj) (at (cnj x))`
  MP_TAC THENL
   [MATCH_MP_TAC MOI_PDG_DERIV_HALF THEN
    MAP_EVERY EXISTS_TAC [`Cx c`; `r:real`] THEN
    ASM_REWRITE_TAC[MOI_PDG_CNJ_BALL; IM_CNJ] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
      ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_CNJ; CNJ_CNJ];
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
      ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_CNJ; CNJ_CNJ];
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[MOI_PDG_CNJ_BALL; IM_CNJ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:complex->real^M. h differentiable at x
        ==> frechet_derivative (h o cnj) (at (cnj x)) = frechet_derivative h (at x) o cnj`
  (fun th -> ASM_SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_CNJ; CNJ_CNJ; GSYM FRECHET_DERIVATIVE_WORKS];
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN DISCH_TAC THEN X_GEN_TAC `v:complex` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `cnj v`) THEN REWRITE_TAC[CNJ_CNJ]]);;

let MOI_PDG_GLUE_LOWER = prove
 (`!(F0:complex->real^2) (H:complex->real^2) a b e.
      a < b /\ &0 < e /\ &2 * e < b - a /\
      (!t. a <= t /\ t <= b
           ==> ?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:complex->real^2) /\
                     (!x. x IN ball(Cx t,r) /\ Im x <= &0 ==> g x = F0 x) /\
                     ~(det(jacobian g (at (Cx t))) = &0)) /\
      (!t. a <= t /\ t <= a + e \/ b - e <= t /\ t <= b
           ==> ?r. &0 < r /\ smooth_map_on (ball(Cx t,r)) H /\
                   (!x. x IN ball(Cx t,r) /\ Im x <= &0 ==> H x = F0 x))
      ==> ?d u Fm. &0 < d /\ open u /\
                   {x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d} SUBSET u /\
                   smooth_map_on u (Fm:complex->real^2) /\
                   (!x. a <= Re x /\ Re x <= b /\ --d <= Im x /\ Im x <= &0
                        ==> Fm x = F0 x) /\
                   (!x. (a <= Re x /\ Re x <= a + e / &2 \/
                         b - e / &2 <= Re x /\ Re x <= b) /\ abs(Im x) <= d
                        ==> Fm x = H x) /\
                   (!x. a <= Re x /\ Re x <= b /\ abs(Im x) <= d
                        ==> ~(det(jacobian Fm (at x)) = &0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gen") (LABEL_TAC "end"))))) THEN
  MP_TAC(ISPECL [`(F0:complex->real^2) o cnj`; `(H:complex->real^2) o cnj`;
                 `a:real`; `b:real`; `e:real`] MOI_PDG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "gen" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `g:complex->real^2`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`r:real`; `(g:complex->real^2) o cnj`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_PDG_SMOOTH_CNJ_COMPOSE THEN
        ASM_REWRITE_TAC[OPEN_BALL; MOI_PDG_CNJ_BALL];
        REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[MOI_PDG_CNJ_BALL; IM_CNJ] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`g:complex->real^2`; `Cx t`] MOI_PDG_JAC_CNJ) THEN
        REWRITE_TAC[CNJ_CX] THEN ANTS_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
          EXISTS_TAC `ball(Cx t,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
          DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[REAL_NEG_EQ_0]]];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN
      USE_THEN "end" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_PDG_SMOOTH_CNJ_COMPOSE THEN
        ASM_REWRITE_TAC[OPEN_BALL; MOI_PDG_CNJ_BALL];
        REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[MOI_PDG_CNJ_BALL; IM_CNJ] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `u:complex->bool`
    (X_CHOOSE_THEN `Fp:complex->real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `IMAGE cnj (u:complex->bool)`;
                        `(Fp:complex->real^2) o cnj`] THEN
  SUBGOAL_THEN `!z. z IN IMAGE cnj (u:complex->bool) <=> cnj z IN u` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[CNJ_CNJ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_PDG_OPEN_CNJ_IMAGE];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d} SUBSET u` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[RE_CNJ; IM_CNJ; REAL_ABS_NEG];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_SIMP_TAC[MOI_SMB_SMOOTH_LINEAR; LINEAR_CNJ] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_PDG_OPEN_CNJ_IMAGE];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[CNJ_CNJ];
      MATCH_MP_TAC MOI_SMB_SMOOTH_LINEAR THEN
      ASM_SIMP_TAC[MOI_PDG_OPEN_CNJ_IMAGE; LINEAR_CNJ]];
    REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(F0:complex->real^2) x = (F0 o cnj) (cnj x)` SUBST1_TAC THENL
     [REWRITE_TAC[o_THM; CNJ_CNJ]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[RE_CNJ; IM_CNJ] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(H:complex->real^2) x = (H o cnj) (cnj x)` SUBST1_TAC THENL
     [REWRITE_TAC[o_THM; CNJ_CNJ]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[RE_CNJ; IM_CNJ; REAL_ABS_NEG];
    X_GEN_TAC `x:complex` THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    MP_TAC(ISPECL [`Fp:complex->real^2`; `x:complex`] MOI_PDG_JAC_CNJ) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `u:complex->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `{x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d} SUBSET u` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[RE_CNJ; IM_CNJ; REAL_ABS_NEG];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_NEG_EQ_0] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[RE_CNJ; IM_CNJ; REAL_ABS_NEG]]]);;

let MOI_PDG_UNIT_CNJ = prove
 (`!c:complex. norm c = &1 ==> c * cnj c = Cx(&1) /\ cnj c * c = Cx(&1)`,
  SIMP_TAC[COMPLEX_MUL_CNJ; COMPLEX_POW_ONE]);;

let MOI_PDG_RIGID_INV = prove
 (`!z0 c:complex x y.
      norm c = &1
      ==> z0 + c * (cnj c * (y - z0)) = y /\ cnj c * ((z0 + c * x) - z0) = x`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_PDG_UNIT_CNJ) THEN
  CONV_TAC COMPLEX_RING);;

let MOI_PDG_RIGID_INJ = prove
 (`!z0 c:complex x y. norm c = &1 /\ z0 + c * x = z0 + c * y ==> x = y`,
  MESON_TAC[MOI_PDG_RIGID_INV]);;

let MOI_PDG_UNIT3 = prove
 (`!v:real^3. norm v = &1 /\ v$3 = &1 ==> v = basis 3`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `norm(v:real^3) = &1` THEN REWRITE_TAC[NORM_EQ_1; DOT_3] THEN
  ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^3)$1 * v$1 + v$2 * v$2 = &0` MP_TAC THENL
   [UNDISCH_TAC `(v:real^3)$1 * v$1 + v$2 * v$2 + &1 * &1 = &1` THEN REAL_ARITH_TAC;
    SIMP_TAC[REAL_LE_SQUARE; REAL_ARITH
      `&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)`] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN SIMP_TAC[]]);;

let MOI_PDG_HOMEO_INJ = prove
 (`!(X:real^N->bool) (M:real^N->real^3) M' x y.
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\ x IN X /\ y IN X /\ M x = M y
      ==> x = y`,
  REWRITE_TAC[homeomorphism] THEN MESON_TAC[]);;

let MOI_PDG_CR_POLE = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) M' U phi z0 c a b e.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\
      moi_pdg_crease sigma M U phi z0 c a b e
      ==> ?f. orthogonal_transformation f /\
              !t. a <= t /\ t <= b
                  ==> ~((f(M(chart_inv (U,phi) (z0 + c * Cx t))))$3 = &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_crease] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:real` o check (fun th ->
    can (find_term ((=) `a + e:real`)) (concl th) = false && is_forall (concl th) &&
    can (find_term (fun t -> t = `&0 <= Im x`)) (concl th))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `g:complex->real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `ys = z0 + c * (Cx a + ii * Cx(r / &2))` THEN
  SUBGOAL_THEN `(ys:complex) IN IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
   [EXPAND_TAC "ys" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_BALL; dist; COMPLEX_RING `Cx a - (Cx a + ii * Cx(r / &2)) = --(ii * Cx(r / &2))`] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_MUL; COMPLEX_NORM_II; COMPLEX_NORM_CX] THEN
    UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `xs = chart_inv (U:real^N->bool,phi:real^N->real^2) ys` THEN
  SUBGOAL_THEN `(xs:real^N) IN X /\ (phi:real^N->real^2) xs = ys` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "xs" THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `norm((M:real^N->real^3) xs) = norm(basis 3:real^3)` MP_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN REWRITE_TAC[GSYM IN_SPHERE_0] THEN
    UNDISCH_TAC `homeomorphism (X,sphere(vec 0,&1)) (M:real^N->real^3,M')` THEN
    REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^3->real^3` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `z0 + c * Cx t IN IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&0 <= Im x`)) (concl th) &&
      can (find_term (fun t -> t = `a + e:real`)) (concl th) = false)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r':real` (X_CHOOSE_THEN `g':complex->real^3`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `xt = chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * Cx t)` THEN
  SUBGOAL_THEN `(xt:real^N) IN X /\ (phi:real^N->real^2) xt = z0 + c * Cx t`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "xt" THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^N->real^3) xt = M xs` ASSUME_TAC THENL
   [MATCH_MP_TAC(MATCH_MP ORTHOGONAL_TRANSFORMATION_INJECTIVE
      (ASSUME `orthogonal_transformation (f:real^3->real^3)`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PDG_UNIT3 THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `norm((M:real^N->real^3) xt) = &1` MP_TAC THENL
     [REWRITE_TAC[GSYM IN_SPHERE_0] THEN
      UNDISCH_TAC `homeomorphism (X,sphere(vec 0,&1)) (M:real^N->real^3,M')` THEN
      REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(xt:real^N) = xs` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_HOMEO_INJ THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `M:real^N->real^3`; `M':real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx t = Cx a + ii * Cx(r / &2)` MP_TAC THENL
   [MATCH_MP_TAC MOI_PDG_RIGID_INJ THEN
    MAP_EVERY EXISTS_TAC [`z0:complex`; `c:complex`] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN
    REWRITE_TAC[IM_ADD; IM_CX; IM_MUL_II; RE_CX] THEN
    UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC]);;

let MOI_PDG_DET_NZ_INJ = prove
 (`!(FF:real^2->real^2) x.
      FF differentiable at x /\
      (!v. frechet_derivative FF (at x) v = vec 0 ==> v = vec 0)
      ==> ~(det(jacobian FF (at x)) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[jacobian; GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  SUBGOAL_THEN `linear(frechet_derivative (FF:real^2->real^2) (at x))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN ASM_MESON_TAC[]);;

let MOI_PDG_ST_EXT_UP = prove
 (`!(f:real^3->real^3) (gu:complex->real^3) (Phi:complex->real^3) t r.
      orthogonal_transformation f /\ &0 < r /\ smooth_map_on (ball(Cx t,r)) gu /\
      (!x. x IN ball(Cx t,r) /\ &0 <= Im x
           ==> gu x = Phi x /\ Phi x IN sphere(vec 0,&1)) /\
      ~((f(gu(Cx t)))$3 = &1) /\
      (!v. frechet_derivative gu (at (Cx t)) v = vec 0 ==> v = vec 0)
      ==> ?r' g. &0 < r' /\ smooth_map_on (ball(Cx t,r')) (g:complex->real^2) /\
                 (!x. x IN ball(Cx t,r') /\ &0 <= Im x ==> g x = moi_pdg_st f (Phi x)) /\
                 ~(det(jacobian g (at (Cx t))) = &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  ABBREV_TAC `S = {p:real^3 | ~(((f:real^3->real^3) p)$3 = &1)}` THEN
  SUBGOAL_THEN `open(S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[MOI_PDG_ST_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (moi_pdg_st (f:real^3->real^3))` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[MOI_PDG_ST_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x | x IN ball(Cx t,r) /\ (gu:complex->real^3) x IN S}`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `Cx t`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(Cx t,r') SUBSET ball(Cx t,r)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `r':real` THEN
  EXISTS_TAC `moi_pdg_st (f:real^3->real^3) o (gu:complex->real^3)` THEN
  SUBGOAL_THEN `smooth_map_on (ball(Cx t,r')) (moi_pdg_st (f:real^3->real^3) o gu)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_DET_NZ_INJ THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(Cx t,r')` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (gu:complex->real^3) (at (Cx t)) =
    frechet_derivative (moi_pdg_sti f o (moi_pdg_st (f:real^3->real^3) o gu)) (at (Cx t))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_PDG_DERIV_HALF THEN
    MAP_EVERY EXISTS_TAC [`Cx t`; `r':real`] THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; IM_CX; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(Cx t,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(Cx t,r')` THEN
        ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
        ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH]];
      X_GEN_TAC `y:complex` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PDG_STI_ST THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        SUBGOAL_THEN `(y:complex) IN {x | x IN ball(Cx t,r) /\ (gu:complex->real^3) x IN S}`
        MP_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (moi_pdg_sti f o (moi_pdg_st (f:real^3->real^3) o gu)) (at (Cx t)) =
    frechet_derivative (moi_pdg_sti f) (at ((moi_pdg_st f o gu) (Cx t))) o
    frechet_derivative (moi_pdg_st f o gu) (at (Cx t))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `ball(Cx t,r')` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
      EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `linear(frechet_derivative (moi_pdg_sti (f:real^3->real^3))
                         (at (moi_pdg_st f ((gu:complex->real^3) (Cx t)))))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH];
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP LINEAR_0)]);;

let MOI_PDG_ST_EXT_LO = prove
 (`!(f:real^3->real^3) (gu:complex->real^3) (Phi:complex->real^3) t r.
      orthogonal_transformation f /\ &0 < r /\ smooth_map_on (ball(Cx t,r)) gu /\
      (!x. x IN ball(Cx t,r) /\ Im x <= &0
           ==> gu x = Phi x /\ Phi x IN sphere(vec 0,&1)) /\
      ~((f(gu(Cx t)))$3 = &1) /\
      (!v. frechet_derivative gu (at (Cx t)) v = vec 0 ==> v = vec 0)
      ==> ?r' g. &0 < r' /\ smooth_map_on (ball(Cx t,r')) (g:complex->real^2) /\
                 (!x. x IN ball(Cx t,r') /\ Im x <= &0 ==> g x = moi_pdg_st f (Phi x)) /\
                 ~(det(jacobian g (at (Cx t))) = &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  ABBREV_TAC `S = {p:real^3 | ~(((f:real^3->real^3) p)$3 = &1)}` THEN
  SUBGOAL_THEN `open(S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[MOI_PDG_ST_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (moi_pdg_st (f:real^3->real^3))` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[MOI_PDG_ST_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x | x IN ball(Cx t,r) /\ (gu:complex->real^3) x IN S}`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `Cx t`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(Cx t,r') SUBSET ball(Cx t,r)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `r':real` THEN
  EXISTS_TAC `moi_pdg_st (f:real^3->real^3) o (gu:complex->real^3)` THEN
  SUBGOAL_THEN `smooth_map_on (ball(Cx t,r')) (moi_pdg_st (f:real^3->real^3) o gu)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_DET_NZ_INJ THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(Cx t,r')` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (gu:complex->real^3) (at (Cx t)) =
    frechet_derivative (moi_pdg_sti f o (moi_pdg_st (f:real^3->real^3) o gu)) (at (Cx t))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_PDG_DERIV_HALF_LOWER THEN
    MAP_EVERY EXISTS_TAC [`t:real`; `r':real`] THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; IM_CX; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(Cx t,r)` THEN
      ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(Cx t,r')` THEN
        ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
        ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH]];
      X_GEN_TAC `y:complex` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PDG_STI_ST THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        SUBGOAL_THEN `(y:complex) IN {x | x IN ball(Cx t,r) /\ (gu:complex->real^3) x IN S}`
        MP_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (moi_pdg_sti f o (moi_pdg_st (f:real^3->real^3) o gu)) (at (Cx t)) =
    frechet_derivative (moi_pdg_sti f) (at ((moi_pdg_st f o gu) (Cx t))) o
    frechet_derivative (moi_pdg_st f o gu) (at (Cx t))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `ball(Cx t,r')` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
      EXISTS_TAC `(:real^2)` THEN ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `linear(frechet_derivative (moi_pdg_sti (f:real^3->real^3))
                         (at (moi_pdg_st f ((gu:complex->real^3) (Cx t)))))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH];
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP LINEAR_0)]);;

let MOI_PDG_ST_SMOOTH_TWO = prove
 (`!(f:real^3->real^3) (g2:complex->real^3) (Phi:complex->real^3) t r.
      orthogonal_transformation f /\ &0 < r /\ smooth_map_on (ball(Cx t,r)) g2 /\
      (!x. x IN ball(Cx t,r) ==> g2 x = Phi x) /\ ~((f(g2(Cx t)))$3 = &1)
      ==> ?r'. &0 < r' /\ smooth_map_on (ball(Cx t,r')) (\x. moi_pdg_st f (Phi x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  ABBREV_TAC `S = {p:real^3 | ~(((f:real^3->real^3) p)$3 = &1)}` THEN
  SUBGOAL_THEN `open(S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[MOI_PDG_ST_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (moi_pdg_st (f:real^3->real^3))` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[MOI_PDG_ST_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x | x IN ball(Cx t,r) /\ (g2:complex->real^3) x IN S}`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `Cx t`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r':real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `moi_pdg_st (f:real^3->real^3) o (g2:complex->real^3)` THEN
  REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `S:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]]);;

let MOI_PDG_CR_LOCAL = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) M' U phi z0 c a b e (f:real^3->real^3).
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\
      moi_pdg_crease sigma M U phi z0 c a b e /\ orthogonal_transformation f /\
      (!t. a <= t /\ t <= b ==> ~((f(M(chart_inv (U,phi) (z0 + c * Cx t))))$3 = &1))
      ==> (!t. a <= t /\ t <= b
               ==> ?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:complex->real^2) /\
                         (!x. x IN ball(Cx t,r) /\ &0 <= Im x
                              ==> g x = moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x)))) /\
                         ~(det(jacobian g (at (Cx t))) = &0)) /\
          (!t. a <= t /\ t <= b
               ==> ?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:complex->real^2) /\
                         (!x. x IN ball(Cx t,r) /\ Im x <= &0
                              ==> g x = moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x)))) /\
                         ~(det(jacobian g (at (Cx t))) = &0)) /\
          (!t. a <= t /\ t <= a + e \/ b - e <= t /\ t <= b
               ==> ?r. &0 < r /\
                       smooth_map_on (ball(Cx t,r))
                         (\x. moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x)))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_crease] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. z0 + c * x IN IMAGE (phi:real^N->real^2) U
        ==> (M:real^N->real^3)(chart_inv (U,phi) (z0 + c * x)) IN sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `homeomorphism (X,sphere(vec 0,&1)) (M:real^N->real^3,M')` THEN
    REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&0 <= Im x`)) (concl th) &&
      can (find_term (fun t -> t = `a + e:real`)) (concl th) = false)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `gu:complex->real^3`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `gu:complex->real^3`;
                   `\x:complex. (M:real^N->real^3)(chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * x))`;
                   `t:real`; `r:real`] MOI_PDG_ST_EXT_UP) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      SUBGOAL_THEN `(gu:complex->real^3) (Cx t) = (M:real^N->real^3)(chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * Cx t))`
       (fun th -> ASM_SIMP_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL; IM_CX; REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `v:complex` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `Cx t`) THEN
      REWRITE_TAC[CENTRE_IN_BALL; IM_CX; REAL_LE_REFL] THEN ASM_REWRITE_TAC[]];
X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&0 <= Im x`)) (concl th) &&
      can (find_term (fun t -> t = `a + e:real`)) (concl th) = false)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `gu:complex->real^3`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `gu:complex->real^3`;
                   `\x:complex. (M:real^N->real^3)(chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * x))`;
                   `t:real`; `r:real`] MOI_PDG_ST_EXT_LO) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      SUBGOAL_THEN `(gu:complex->real^3) (Cx t) = (M:real^N->real^3)(chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * Cx t))`
       (fun th -> ASM_SIMP_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL; IM_CX; REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `v:complex` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `Cx t`) THEN
      REWRITE_TAC[CENTRE_IN_BALL; IM_CX; REAL_LE_REFL] THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `a <= t /\ t <= b` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `a + e:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `g2:complex->real^3`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_PDG_ST_SMOOTH_TWO THEN
    MAP_EVERY EXISTS_TAC [`g2:complex->real^3`; `r:real`] THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(g2:complex->real^3) (Cx t) = (M:real^N->real^3)(chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * Cx t))`
     (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL]]);;
let MOI_PDG_GOOD_OPEN = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) M' U phi (z0:complex) c (f:real^3->real^3) G0.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (U,phi) IN sigma /\
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\ orthogonal_transformation f /\
      open_in (subtopology euclidean X) G0
      ==> open {x | z0 + c * x IN IMAGE phi U /\
                    chart_inv (U,phi) (z0 + c * x) IN G0 /\
                    ~((f(M(chart_inv (U,phi) (z0 + c * x))))$3 = &1)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `Wx = U INTER G0 INTER
                   {z | z IN X /\ (M:real^N->real^3) z IN
                                  {y | ~(((f:real^3->real^3) y)$3 = &1)}}` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (X:real^N->bool)) Wx` ASSUME_TAC THENL
   [EXPAND_TAC "Wx" THEN MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `U:real^N->bool`; `phi:real^N->real^2`]
                    SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_SIMP_TAC[MOI_PDG_ST_OPEN; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
    UNDISCH_TAC `homeomorphism (X,sphere(vec 0,&1)) (M:real^N->real^3,M')` THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (phi:real^N->real^2) Wx)` ASSUME_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (X:real^N->bool)`;
                          `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Wx" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | z0 + c * x IN IMAGE phi U /\
         chart_inv (U,phi) (z0 + c * x) IN G0 /\
         ~(((f:real^3->real^3)((M:real^N->real^3)(chart_inv (U,phi) (z0 + c * x))))$3 = &1)} =
    {x | (\x. z0 + c * x) x IN IMAGE (phi:real^N->real^2) Wx}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:complex` THEN
    EXPAND_TAC "Wx" THEN REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)
                                 STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y:real^N` THEN
      SUBGOAL_THEN `chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * x) = y`
        (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * x) = z`
        SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_LMUL THEN REWRITE_TAC[CONTINUOUS_AT_ID]]);;

let MOI_PDG_CR_FPM = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) M' U phi z0 c a b e
    (f:real^3->real^3) (G0:real^N->bool).
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\
      moi_pdg_crease sigma M U phi z0 c a b e /\ orthogonal_transformation f /\
      (!t. a <= t /\ t <= b ==> ~((f(M(chart_inv (U,phi) (z0 + c * Cx t))))$3 = &1)) /\
      open_in (subtopology euclidean X) G0 /\
      (!t. a <= t /\ t <= b ==> chart_inv (U,phi) (z0 + c * Cx t) IN G0)
      ==> ?d u Fp Fm.
            &0 < d /\ open u /\ {x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d} SUBSET u /\
            smooth_map_on u (Fp:complex->real^2) /\ smooth_map_on u (Fm:complex->real^2) /\
            (!x. a <= Re x /\ Re x <= b /\ abs(Im x) <= d
                 ==> z0 + c * x IN IMAGE phi U /\
                     chart_inv (U,phi) (z0 + c * x) IN G0 /\
                     ~((f(M(chart_inv (U,phi) (z0 + c * x))))$3 = &1)) /\
            (!x. a <= Re x /\ Re x <= b /\ &0 <= Im x /\ Im x <= d
                 ==> Fp x = moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x)))) /\
            (!x. a <= Re x /\ Re x <= b /\ --d <= Im x /\ Im x <= &0
                 ==> Fm x = moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x)))) /\
            (!x. (a <= Re x /\ Re x <= a + e / &2 \/ b - e / &2 <= Re x /\ Re x <= b) /\
                 abs(Im x) <= d ==> Fp x = Fm x) /\
            (!x. a <= Re x /\ Re x <= b /\ abs(Im x) <= d
                 ==> ~(det(jacobian Fp (at x)) = &0) /\ ~(det(jacobian Fm (at x)) = &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `M:real^N->real^3`; `M':real^3->real^N`; `U:real^N->bool`;
                 `phi:real^N->real^2`; `z0:complex`; `c:complex`; `a:real`; `b:real`;
                 `e:real`; `f:real^3->real^3`] MOI_PDG_CR_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "up") (CONJUNCTS_THEN2 (LABEL_TAC "lo")
    (LABEL_TAC "ends"))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_pdg_crease]) THEN STRIP_TAC THEN
  ABBREV_TAC `Fs = \x. moi_pdg_st (f:real^3->real^3)
                         ((M:real^N->real^3)(chart_inv (U,phi) (z0 + c * x)))` THEN
  SUBGOAL_THEN `!x. (Fs:complex->real^2) x =
                    moi_pdg_st f ((M:real^N->real^3)(chart_inv (U,phi) (z0 + c * x)))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]) THENL
   [EXPAND_TAC "Fs" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Fs:complex->real^2`; `Fs:complex->real^2`; `a:real`; `b:real`;
                 `e:real`] MOI_PDG_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (X_CHOOSE_THEN `u1:complex->bool`
    (X_CHOOSE_THEN `Fp:complex->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`Fs:complex->real^2`; `Fs:complex->real^2`; `a:real`; `b:real`;
                 `e:real`] MOI_PDG_GLUE_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` (X_CHOOSE_THEN `u2:complex->bool`
    (X_CHOOSE_THEN `Fm:complex->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`{x | z0 + c * x IN IMAGE (phi:real^N->real^2) U /\
                       chart_inv (U,phi) (z0 + c * x) IN G0 /\
                       ~(((f:real^3->real^3)((M:real^N->real^3)
                            (chart_inv (U,phi) (z0 + c * x))))$3 = &1)}`;
                 `a:real`; `b:real`] MOI_PDG_STRIP_THIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PDG_GOOD_OPEN THEN
      MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                            `M':real^3->real^N`] THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_SIMP_TAC[] THEN
      USE_THEN "up" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `&0 <= Im x`)) (concl th) &&
        can (find_term (fun t -> t = `a + e:real`)) (concl th) = false &&
        can (find_term (fun t -> t = `moi_pdg_st`)) (concl th) = false)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `r':real` (X_CHOOSE_THEN `gu:complex->real^3`
        STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d3:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`min d1 (min d2 d3)`; `u1 INTER u2:complex->bool`;
                        `Fp:complex->real^2`; `Fm:complex->real^2`] THEN
  SUBGOAL_THEN `&0 < min d1 (min d2 d3) /\ min d1 (min d2 d3) <= d1 /\
                min d1 (min d2 d3) <= d2 /\ min d1 (min d2 d3) <= d3`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `d = min d1 (min d2 d3)` THEN
  SUBGOAL_THEN `{x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d} SUBSET u1 INTER u2`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`{x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d1} SUBSET u1`;
      `{x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d2} SUBSET u2`] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
    MAP_EVERY UNDISCH_TAC [`d <= d1`; `d <= d2`] THEN
    MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u1:complex->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u2:complex->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `d3:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `Fp:complex->real^2`)) (concl th) &&
      can (find_term (fun t -> t = `&0 <= Im x`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `Fm:complex->real^2`)) (concl th) &&
      can (find_term (fun t -> t = `Im x <= &0`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    TRANS_TAC EQ_TRANS `(Fs:complex->real^2) x` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `Fp:complex->real^2`)) (concl th) &&
        can (find_term (fun t -> t = `e / &2`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `Fm:complex->real^2`)) (concl th) &&
        can (find_term (fun t -> t = `e / &2`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `jacobian (Fp:complex->real^2)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `jacobian (Fm:complex->real^2)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let MOI_PDG_JAC_TRANSLATE = prove
 (`!(F1:complex->real^2) c y.
      F1 differentiable at (y + c)
      ==> jacobian (\z. F1(z + c)) (at y) = jacobian F1 (at (y + c))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSLATION THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let MOI_PDG_JAC_CNJ_LEFT = prove
 (`!(F1:complex->real^2) x.
      F1 differentiable at x
      ==> det(jacobian (cnj o F1) (at x)) = --det(jacobian F1 (at x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN
  SUBGOAL_THEN `frechet_derivative (cnj o (F1:complex->real^2)) (at x) =
                cnj o frechet_derivative F1 (at x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; LINEAR_CNJ; GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (F1:complex->real^2) (at x))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_CNJ; DET_MUL; MOI_PDG_DET_MATRIX_CNJ] THEN
  REAL_ARITH_TAC);;

let MOI_PDG_SIGN_CONST = prove
 (`!s (g:complex->real) x y.
      connected s /\ (\x. lift(g x)) continuous_on s /\ (!z. z IN s ==> ~(g z = &0)) /\
      x IN s /\ y IN s
      ==> &0 < g x * g y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift((g:complex->real) x)`; `s:complex->bool`]
         CONNECTED_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_1] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_POS_LT] THEN
  SUBGOAL_THEN `~((g:complex->real) x = &0) /\ ~(g y = &0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?p q. p IN s /\ q IN s /\ (g:complex->real) p < &0 /\ &0 < g q`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `&0 < (g:complex->real) x` THENL
     [MAP_EVERY EXISTS_TAC [`y:complex`; `x:complex`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`x:complex`; `y:complex`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`lift((g:complex->real) p)`; `lift((g:complex->real) q)`;
                                `lift(&0)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[LIFT_DROP; IN_IMAGE] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    REWRITE_TAC[LIFT_DROP; IN_IMAGE; LIFT_EQ] THEN ASM_MESON_TAC[]]);;

let MOI_PDG_STRIP_CONVEX = prove
 (`!a b d. convex {x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[convex; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`; `u:real`; `v:real`] THEN
  STRIP_TAC THEN REWRITE_TAC[RE_ADD; IM_ADD; RE_CMUL; IM_CMUL] THEN
  SUBGOAL_THEN `u * a <= u * Re x /\ u * Re x <= u * b /\ v * a <= v * Re y /\
                v * Re y <= v * b /\ abs(u * Im x) <= u * d /\ abs(v * Im y) <= v * d`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL; REAL_ABS_MUL; REAL_ARITH `&0 <= u ==> abs u = u`];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u * a + v * a = a /\ u * b + v * b = b /\ u * d + v * d = d`
    MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_LID];
      REAL_ARITH_TAC]]);;

let MOI_PDG_STRIP_CONNECTED = prove
 (`!a b d. connected {x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d}`,
  SIMP_TAC[CONVEX_CONNECTED; MOI_PDG_STRIP_CONVEX]);;

let MOI_PDG_CX_VECTOR = prove
 (`!t. vector[t; &0]:complex = Cx t`,
  REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX; RE_DEF; IM_DEF; VECTOR_2]);;

let MOI_PDG_SMOOTH_TRANSLATE = prove
 (`!(F1:complex->real^M) u v c.
      open u /\ open v /\ smooth_map_on v F1 /\ (!x. x IN u ==> x + c IN v)
      ==> smooth_map_on u (\x. F1(x + c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (F1:complex->real^M)(x + c)) = F1 o (\x. x + c)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `v:complex->bool` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]);;

let MOI_PDG_FS_CONT = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) M' U phi z0 c (f:real^3->real^3) s.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (U,phi) IN sigma /\
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\ orthogonal_transformation f /\
      (!x. x IN s ==> z0 + c * x IN IMAGE phi U /\
                      ~((f(M(chart_inv (U,phi) (z0 + c * x))))$3 = &1))
      ==> (\x. moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x)))) continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] MOI_PDG_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. moi_pdg_st f ((M:real^N->real^3)(chart_inv (U,phi) (z0 + c * x)))) =
    moi_pdg_st f o M o chart_inv (U:real^N->bool,phi:real^N->real^2) o (\x. z0 + c * x)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{p:real^3 | ~(((f:real^3->real^3) p)$3 = &1)}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[MOI_PDG_ST_SMOOTH; ORTHOGONAL_TRANSFORMATION_LINEAR];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; IN_ELIM_THM] THEN ASM_SIMP_TAC[]]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `X:real^N->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
    MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                   `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:real^N->real^2) U` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[homeomorphism]; ASM SET_TAC[]]]);;

let MOI_PDG_CR_D4A = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) M' U phi z0 c a b (f:real^3->real^3)
    d u Fp Fm.
      MOI_SMO_CREASE_ORIENT_STATEMENT /\
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (U,phi) IN sigma /\
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\ orthogonal_transformation f /\
      norm c = &1 /\ a < b /\ &0 < d /\ open u /\
      {x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d} SUBSET u /\
      smooth_map_on u (Fp:complex->real^2) /\ smooth_map_on u (Fm:complex->real^2) /\
      (!x. a <= Re x /\ Re x <= b /\ abs(Im x) <= d
           ==> z0 + c * x IN IMAGE phi U /\
               ~((f(M(chart_inv (U,phi) (z0 + c * x))))$3 = &1)) /\
      (!x. a <= Re x /\ Re x <= b /\ &0 <= Im x /\ Im x <= d
           ==> Fp x = moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x)))) /\
      (!x. a <= Re x /\ Re x <= b /\ --d <= Im x /\ Im x <= &0
           ==> Fm x = moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x)))) /\
      ~(det(jacobian Fp (at (Cx((a + b) / &2)))) = &0) /\
      ~(det(jacobian Fm (at (Cx((a + b) / &2)))) = &0)
      ==> &0 < det(jacobian Fp (at (Cx((a + b) / &2)))) *
               det(jacobian Fm (at (Cx((a + b) / &2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `c0 = Cx((a + b) / &2)` THEN
  ABBREV_TAC `rho = min d ((b - a) / &2)` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(vec 0,rho)
        ==> a <= Re(x + c0) /\ Re(x + c0) <= b /\ abs(Im(x + c0)) <= d`
  (LABEL_TAC "ballf") THENL
   [X_GEN_TAC `x:complex` THEN REWRITE_TAC[IN_BALL_0] THEN DISCH_TAC THEN
    MP_TAC(SPEC `x:complex` COMPLEX_NORM_GE_RE_IM) THEN
    EXPAND_TAC "c0" THEN REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX] THEN
    MAP_EVERY UNDISCH_TAC [`norm(x:complex) < rho`; `min d ((b - a) / &2) = rho`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_SMO_CREASE_ORIENT_STATEMENT] o
    check (fun th -> concl th = `MOI_SMO_CREASE_ORIENT_STATEMENT`)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`\x. moi_pdg_st (f:real^3->real^3)
           ((M:real^N->real^3)(chart_inv (U,phi) (z0 + c * (x + c0))))`;
    `\x. (Fp:complex->real^2)(x + c0)`; `\x. (Fm:complex->real^2)(x + c0)`;
    `ball(vec 0:complex,rho)`]) THEN
  SUBGOAL_THEN `(c0:complex) IN u` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `u:complex->bool`)) (concl th) &&
      can (find_term (fun t -> t = `d:real`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXPAND_TAC "c0" THEN
    REWRITE_TAC[RE_CX; IM_CX; REAL_ABS_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `jacobian (\x. (Fp:complex->real^2)(x + c0)) (at (vec 0)) = jacobian Fp (at c0) /\
    jacobian (\x. (Fm:complex->real^2)(x + c0)) (at (vec 0)) = jacobian Fm (at c0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM VECTOR_ADD_LID] THEN
    MATCH_MP_TAC MOI_PDG_JAC_TRANSLATE THEN REWRITE_TAC[VECTOR_ADD_LID] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(vec 0,rho)
        ==> z0 + c * (x + c0) IN IMAGE (phi:real^N->real^2) U /\
            ~(((f:real^3->real^3)((M:real^N->real^3)
                 (chart_inv (U,phi) (z0 + c * (x + c0)))))$3 = &1)`
  (LABEL_TAC "goodb") THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `abs(Im x) <= d`)) (concl th) &&
      can (find_term (fun t -> t = `moi_pdg_st`)) (concl th) = false)) THEN
    USE_THEN "ballf" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\x. moi_pdg_st (f:real^3->real^3)
             ((M:real^N->real^3)(chart_inv (U,phi) (z0 + c * (x + c0))))) =
      (\w. moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * w)))) o (\x. x + c0)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC MOI_PDG_FS_CONT THEN
      MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                            `M':real^3->real^N`] THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN USE_THEN "goodb" ACCEPT_TAC];
    MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(VECTOR_ARITH `x + c0:complex = y + c0 ==> x = y`) THEN
    MATCH_MP_TAC MOI_PDG_RIGID_INJ THEN
    MAP_EVERY EXISTS_TAC [`z0:complex`; `c:complex`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `z0 + c * (x + c0) IN IMAGE (phi:real^N->real^2) U /\
                  ~(((f:real^3->real^3)((M:real^N->real^3)
                       (chart_inv (U,phi) (z0 + c * (x + c0)))))$3 = &1) /\
                  z0 + c * (y + c0) IN IMAGE (phi:real^N->real^2) U /\
                  ~(((f:real^3->real^3)((M:real^N->real^3)
                       (chart_inv (U,phi) (z0 + c * (y + c0)))))$3 = &1)`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "goodb" (MP_TAC o SPEC `x:complex`) THEN
      USE_THEN "goodb" (MP_TAC o SPEC `y:complex`) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `moi_pdg_st (f:real^3->real^3) ((M:real^N->real^3)
        (chart_inv (U,phi) (z0 + c * (x + c0)))) =
      moi_pdg_st f (M (chart_inv (U,phi) (z0 + c * (y + c0))))` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `moi_pdg_sti (f:real^3->real^3)`) THEN
    SUBGOAL_THEN
     `!w. w IN IMAGE (phi:real^N->real^2) U /\
          ~(((f:real^3->real^3)((M:real^N->real^3)(chart_inv (U,phi) w)))$3 = &1)
          ==> moi_pdg_sti f (moi_pdg_st f (M(chart_inv (U,phi) w))) =
              M(chart_inv (U,phi) w)`
    (fun th -> ASM_SIMP_TAC[th]) THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_STI_ST THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `homeomorphism (X,sphere(vec 0,&1)) (M:real^N->real^3,M')` THEN
      REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * (x + c0)) =
                  chart_inv (U,phi) (z0 + c * (y + c0))` MP_TAC THENL
     [MATCH_MP_TAC MOI_PDG_HOMEO_INJ THEN
      MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `M:real^N->real^3`; `M':real^3->real^N`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN(MP_TAC o AP_TERM `phi:real^N->real^2`) THEN ASM_SIMP_TAC[] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_PDG_SMOOTH_TRANSLATE THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `u:complex->bool`)) (concl th) &&
      can (find_term (fun t -> t = `d:real`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC MOI_PDG_SMOOTH_TRANSLATE THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `u:complex->bool`)) (concl th) &&
      can (find_term (fun t -> t = `d:real`)) (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN BETA_TAC THEN
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `Fp:complex->real^2`)) (concl th) &&
      is_forall (concl th))) THEN
    USE_THEN "ballf" (MP_TAC o SPEC `x:complex`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IM_ADD] THEN EXPAND_TAC "c0" THEN REWRITE_TAC[IM_CX] THEN
    UNDISCH_TAC `&0 <= (x:complex)$2` THEN REWRITE_TAC[GSYM IM_DEF] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN BETA_TAC THEN
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `Fm:complex->real^2`)) (concl th) &&
      is_forall (concl th))) THEN
    USE_THEN "ballf" (MP_TAC o SPEC `x:complex`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IM_ADD] THEN EXPAND_TAC "c0" THEN REWRITE_TAC[IM_CX] THEN
    UNDISCH_TAC `(x:complex)$2 <= &0` THEN REWRITE_TAC[GSYM IM_DEF] THEN
    REAL_ARITH_TAC]);;

let MOI_PDG_CR_KAPPA = prove
 (`!(Fp:complex->real^2) Fm u d a b.
      open u /\ &0 < d /\ a < b /\
      {x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d} SUBSET u /\
      smooth_map_on u Fp /\ smooth_map_on u Fm /\
      (!x. a <= Re x /\ Re x <= b /\ abs(Im x) <= d
           ==> ~(det(jacobian Fp (at x)) = &0) /\ ~(det(jacobian Fm (at x)) = &0)) /\
      &0 < det(jacobian Fp (at (Cx((a + b) / &2)))) *
           det(jacobian Fm (at (Cx((a + b) / &2))))
      ==> ?kap. linear kap /\ (!z:complex. kap(kap z) = z) /\
                (!x. a <= Re x /\ Re x <= b /\ abs(Im x) <= d
                     ==> &0 < det(jacobian (kap o Fp) (at x)) /\
                         &0 < det(jacobian (kap o Fm) (at x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = {x | a <= Re x /\ Re x <= b /\ abs(Im x) <= d}` THEN
  ABBREV_TAC `c0 = Cx((a + b) / &2)` THEN
  SUBGOAL_THEN `(c0:complex) IN S` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S"; "c0"] THEN
    REWRITE_TAC[IN_ELIM_THM; RE_CX; IM_CX; REAL_ABS_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN S
        ==> &0 < det(jacobian (Fp:complex->real^2) (at x)) * det(jacobian Fp (at c0)) /\
            &0 < det(jacobian (Fm:complex->real^2) (at x)) * det(jacobian Fm (at c0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:complex->bool`; `\x. det(jacobian (Fp:complex->real^2) (at x))`;
                     `x:complex`; `c0:complex`] MOI_PDG_SIGN_CONST);
      MP_TAC(ISPECL [`S:complex->bool`; `\x. det(jacobian (Fm:complex->real^2) (at x))`;
                     `x:complex`; `c0:complex`] MOI_PDG_SIGN_CONST)] THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [EXPAND_TAC "S" THEN REWRITE_TAC[MOI_PDG_STRIP_CONNECTED]; ALL_TAC]) THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:complex->bool` THEN
       ASM_SIMP_TAC[MOI_PDG_JAC_DET_CONT];
       EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN S ==> (Fp:complex->real^2) differentiable at x /\
                               (Fm:complex->real^2) differentiable at x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `u:complex->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < det(jacobian (Fp:complex->real^2) (at c0))` THENL
   [EXISTS_TAC `\z:complex. z` THEN REWRITE_TAC[LINEAR_ID] THEN
    SUBGOAL_THEN `(\z:complex. z) o (Fp:complex->real^2) = Fp /\
                  (\z:complex. z) o (Fm:complex->real^2) = Fm`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < det(jacobian (Fm:complex->real^2) (at c0))` ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < det(jacobian (Fp:complex->real^2) (at c0)) *
                        det(jacobian (Fm:complex->real^2) (at c0))` THEN
      ASM_REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `c0:complex`)) (concl th))) THEN
    ANTS_TAC THENL [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `cnj` THEN REWRITE_TAC[LINEAR_CNJ; CNJ_CNJ] THEN
    SUBGOAL_THEN `det(jacobian (Fp:complex->real^2) (at c0)) < &0 /\
                  det(jacobian (Fm:complex->real^2) (at c0)) < &0` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `~(det(jacobian (Fp:complex->real^2) (at c0)) = &0)` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `c0:complex` o check (fun th ->
          is_forall (concl th) && can (find_term (fun t -> t = `d:real`)) (concl th) &&
          can (find_term (fun t -> t = `c0:complex`)) (concl th) = false)) THEN
        ANTS_TAC THENL
         [EXPAND_TAC "c0" THEN REWRITE_TAC[RE_CX; IM_CX; REAL_ABS_0] THEN
          ASM_REAL_ARITH_TAC;
          SIMP_TAC[]];
        UNDISCH_TAC `&0 < det(jacobian (Fp:complex->real^2) (at c0)) *
                          det(jacobian (Fm:complex->real^2) (at c0))` THEN
        ASM_REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN S` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_PDG_JAC_CNJ_LEFT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `c0:complex`)) (concl th) &&
      can (find_term (fun t -> t = `differentiable`)) (concl th) = false)) THEN
    ASM_REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_OPEN_STRIP = prove
 (`!a b d. open {x:complex | a < Re x /\ Re x < b /\ abs(Im x) < d}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x:complex | a < Re x /\ Re x < b /\ abs(Im x) < d} =
                {x | Re x > a} INTER {x | Re x < b} INTER {x | Im x < d} INTER
                {x | Im x > --d}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[OPEN_HALFSPACE_RE_GT; OPEN_HALFSPACE_RE_LT; OPEN_HALFSPACE_IM_LT;
                OPEN_HALFSPACE_IM_GT]]);;

let MOI_PDG_BOX_COMPACT = prove
 (`!p q r. compact {x:complex | p <= Re x /\ Re x <= q /\ abs(Im x) <= r}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [REWRITE_TAC[bounded; IN_ELIM_THM] THEN EXISTS_TAC `abs p + abs q + abs r` THEN
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    MP_TAC(SPEC `x:complex` COMPLEX_NORM_LE_RE_IM) THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `{x:complex | p <= Re x /\ Re x <= q /\ abs(Im x) <= r} =
                  {x | Re x >= p} INTER {x | Re x <= q} INTER {x | Im x <= r} INTER
                  {x | Im x >= --r}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC) THEN
      REWRITE_TAC[CLOSED_HALFSPACE_RE_GE; CLOSED_HALFSPACE_RE_LE; CLOSED_HALFSPACE_IM_LE;
                  CLOSED_HALFSPACE_IM_GE]]]);;

let MOI_PDG_AFFINV_SMOOTH = prove
 (`!s c z0:complex. open s ==> smooth_map_on s (\y. cnj c * (y - z0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:complex. cnj c * (y - z0)) = (\y. cnj c * y) o (\y. y - z0)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING;
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; SMOOTH_MAP_ON_CONST]]);;

let MOI_PDG_AFFINV_DERIV = prove
 (`!c z0:complex y.
      ((\y. cnj c * (y - z0)) has_derivative (\h. cnj c * h)) (at y)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\y:complex. cnj c * (y - z0)`; `\h:complex. cnj c * h`; `y:complex`]
         FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `(\y:complex. cnj c * (y - z0)) = (\y. cnj c * y - cnj c * z0)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(\h:complex. cnj c * h) = (\h. cnj c * h - vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_SUB_RZERO]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING);;

let MOI_PDG_DET_POS_INJ = prove
 (`!(F1:real^2->real^2) x.
      F1 differentiable at x /\ ~(det(jacobian F1 (at x)) = &0)
      ==> !v. frechet_derivative F1 (at x) v = vec 0 ==> v = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~(det(jacobian (F1:real^2->real^2) (at x)) = &0)` THEN
  REWRITE_TAC[jacobian; GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  EXISTS_TAC `v:real^2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linear(frechet_derivative (F1:real^2->real^2) (at x))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ASM_SIMP_TAC[MATRIX_WORKS]]);;

let MOI_PDG_CR_BUILD = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) M' U phi (z0:complex) c a b e
    (f:real^3->real^3) (G0:real^N->bool) d d' (kap:complex->complex)
    (Fpk:complex->real^2) Fmk (F2:complex->real^2).
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (U,phi) IN sigma /\
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\ orthogonal_transformation f /\
      norm c = &1 /\ a < b /\ &0 < e /\ &4 * e < b - a /\ &0 < d' /\ d' < d /\
      linear kap /\ (!z. kap(kap z) = z) /\
      (!x. a <= Re x /\ Re x <= b /\ abs(Im x) <= d
           ==> z0 + c * x IN IMAGE phi U /\ chart_inv (U,phi) (z0 + c * x) IN G0 /\
               ~((f(M(chart_inv (U,phi) (z0 + c * x))))$3 = &1)) /\
      (!x. a <= Re x /\ Re x <= b /\ &0 <= Im x /\ Im x <= d
           ==> Fpk x = kap(moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x))))) /\
      (!x. a <= Re x /\ Re x <= b /\ --d <= Im x /\ Im x <= &0
           ==> Fmk x = kap(moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x))))) /\
      smooth_map_on {x | a < Re x /\ Re x < b /\ abs(Im x) < d} F2 /\
      (!x. a < Re x /\ Re x < b /\ abs(Im x) < d ==> &0 < det(jacobian F2 (at x))) /\
      (!x. a < Re x /\ Re x < b /\ abs(Im x) < d /\
           (d' <= abs(Im x) \/ Re x <= a + e / &4 \/ b - e / &4 <= Re x)
           ==> F2 x = (if &0 <= Im x then Fpk x else Fmk x))
      ==> ?R K (Nm:real^N->real^3).
            open_in (subtopology euclidean X) R /\ R SUBSET G0 /\
            compact K /\ K SUBSET R /\
            (!t. a + e < t /\ t < b - e ==> chart_inv (U,phi) (z0 + c * Cx t) IN R) /\
            (!x. x IN R /\ ~(x IN K) ==> Nm x = M x) /\
            (!x. x IN R ==> Nm x IN sphere(vec 0,&1)) /\
            (!x. x IN R ==> moi_pdg_imm_at sigma Nm x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "good")
   (CONJUNCTS_THEN2 (LABEL_TAC "vp") (CONJUNCTS_THEN2 (LABEL_TAC "vm")
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "det")
   (LABEL_TAC "out")))))))))))))))))) THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] MOI_PDG_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  ABBREV_TAC `Ost = {x:complex | a < Re x /\ Re x < b /\ abs(Im x) < d}` THEN
  SUBGOAL_THEN `open(Ost:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Ost" THEN REWRITE_TAC[MOI_PDG_OPEN_STRIP]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN Ost ==> a <= Re x /\ Re x <= b /\ abs(Im x) <= d`
  ASSUME_TAC THENL
   [EXPAND_TAC "Ost" THEN REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Tinv = \y:complex. cnj c * (y - z0)` THEN
  SUBGOAL_THEN `(!y. z0 + c * (Tinv:complex->complex) y = y) /\
                (!x. Tinv(z0 + c * x) = x)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Tinv" THEN ASM_SIMP_TAC[MOI_PDG_RIGID_INV]; ALL_TAC] THEN
  EXISTS_TAC `{z:real^N | z IN U /\ (Tinv:complex->complex) (phi z) IN Ost}` THEN
  EXISTS_TAC `IMAGE (\x. chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * x))
                    {x | a + e / &4 <= Re x /\ Re x <= b - e / &4 /\ abs(Im x) <= d'}` THEN
  EXISTS_TAC `\z:real^N. moi_pdg_sti f (kap((F2:complex->real^2)
                           ((Tinv:complex->complex) (phi z))))` THEN
  SUBGOAL_THEN `(Tinv:complex->complex) continuous_on (:complex)` ASSUME_TAC THENL
   [EXPAND_TAC "Tinv" THEN MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN Ost ==> chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * x) IN U /\
                                 phi(chart_inv (U,phi) (z0 + c * x)) = z0 + c * x`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    USE_THEN "good" (MP_TAC o SPEC `x:complex`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `U:real^N->bool` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\z:real^N. (Tinv:complex->complex) (phi z)`; `U:real^N->bool`;
                     `Ost:complex->bool`] CONTINUOUS_OPEN_IN_PREIMAGE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(\z:real^N. (Tinv:complex->complex) (phi z)) = Tinv o phi`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[homeomorphism];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `U:real^N->bool`; `phi:real^N->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    USE_THEN "good" (MP_TAC o SPEC `(Tinv:complex->complex)((phi:real^N->real^2) z)`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[MOI_PDG_BOX_COMPACT] THEN
    SUBGOAL_THEN `(\x. chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * x)) =
                  chart_inv (U,phi) o (\x. z0 + c * x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (phi:real^N->real^2) U` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:complex` THEN
      STRIP_TAC THEN USE_THEN "good" (MP_TAC o SPEC `x:complex`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:complex` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(x:complex) IN Ost` ASSUME_TAC THENL
     [EXPAND_TAC "Ost" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `Cx t IN Ost` ASSUME_TAC THENL
     [EXPAND_TAC "Ost" THEN REWRITE_TAC[IN_ELIM_THM; RE_CX; IM_CX; REAL_ABS_0] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[]];
    X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    ABBREV_TAC `x = (Tinv:complex->complex) ((phi:real^N->real^2) z)` THEN
    SUBGOAL_THEN `z0 + c * x = (phi:real^N->real^2) z` ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * x) = z`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(a + e / &4 <= Re x /\ Re x <= b - e / &4 /\ abs(Im x) <= d')`
    ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC
       `~((z:real^N) IN IMAGE (\x. chart_inv (U,phi) (z0 + c * x))
           {x | a + e / &4 <= Re x /\ Re x <= b - e / &4 /\ abs(Im x) <= d'})` THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EXISTS_TAC `x:complex` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `a < Re x /\ Re x < b /\ abs(Im x) < d` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:complex) IN Ost` THEN EXPAND_TAC "Ost" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "out" (MP_TAC o SPEC `x:complex`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "good" (MP_TAC o SPEC `x:complex`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(M:real^N->real^3) z IN sphere(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `homeomorphism (X,sphere(vec 0,&1)) (M:real^N->real^3,M')` THEN
      REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [USE_THEN "vp" (MP_TAC o SPEC `x:complex`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN DISCH_THEN SUBST1_TAC;
      USE_THEN "vm" (MP_TAC o SPEC `x:complex`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PDG_STI_ST THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_PDG_STI_SPHERE];
    X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[moi_pdg_imm_at] THEN
    MAP_EVERY EXISTS_TAC
     [`U:real^N->bool`; `phi:real^N->real^2`;
      `{y | y IN (:complex) /\ (Tinv:complex->complex) y IN Ost}`;
      `\y. moi_pdg_sti f (kap((F2:complex->real^2) ((Tinv:complex->complex) y)))`] THEN
    ASM_REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
    SUBGOAL_THEN `smooth_map_on Ost (F2:complex->real^2)` ASSUME_TAC THENL
     [EXPAND_TAC "Ost" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `open {y | (Tinv:complex->complex) y IN Ost}` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`Tinv:complex->complex`; `(:complex)`; `Ost:complex->bool`]
             CONTINUOUS_OPEN_PREIMAGE) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `y:complex` THEN
      DISCH_TAC THEN EXISTS_TAC `chart_inv (U:real^N->bool,phi:real^N->real^2) y` THEN
      SUBGOAL_THEN `y = z0 + c * (Tinv:complex->complex) y` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
      SUBGOAL_THEN
       `(\y. moi_pdg_sti f (kap((F2:complex->real^2) ((Tinv:complex->complex) y)))) =
        (\w. moi_pdg_sti (f:real^3->real^3) (kap w)) o (F2 o Tinv)`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:complex)` THEN
      ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `Ost:complex->bool` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        EXPAND_TAC "Tinv" THEN SIMP_TAC[MOI_PDG_AFFINV_SMOOTH] THEN
        UNDISCH_TAC `open {y | (Tinv:complex->complex) y IN Ost}` THEN
        EXPAND_TAC "Tinv" THEN SIMP_TAC[MOI_PDG_AFFINV_SMOOTH];
        SUBGOAL_THEN `(\w. moi_pdg_sti (f:real^3->real^3) ((kap:complex->complex) w)) =
                      moi_pdg_sti f o kap` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:complex)` THEN
        ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; MOI_SMB_SMOOTH_LINEAR; MOI_PDG_STI_SMOOTH]];
      X_GEN_TAC `y:complex` THEN X_GEN_TAC `v:complex` THEN STRIP_TAC THEN
      UNDISCH_TAC
       `frechet_derivative
          (\y. moi_pdg_sti f (kap((F2:complex->real^2) ((Tinv:complex->complex) y))))
          (at y) v = vec 0` THEN
      SUBGOAL_THEN
       `(\y. moi_pdg_sti f (kap((F2:complex->real^2) ((Tinv:complex->complex) y)))) =
        moi_pdg_sti (f:real^3->real^3) o (kap o (F2 o Tinv))`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      SUBGOAL_THEN `((Tinv:complex->complex) has_derivative (\h. cnj c * h)) (at y)`
      ASSUME_TAC THENL
       [EXPAND_TAC "Tinv" THEN REWRITE_TAC[MOI_PDG_AFFINV_DERIV]; ALL_TAC] THEN
      SUBGOAL_THEN `(Tinv:complex->complex) differentiable at y` ASSUME_TAC THENL
       [ASM_MESON_TAC[differentiable]; ALL_TAC] THEN
      SUBGOAL_THEN `frechet_derivative (Tinv:complex->complex) (at y) = (\h. cnj c * h)`
      ASSUME_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `!w. frechet_derivative (kap:complex->complex) (at w) = kap`
      ASSUME_TAC THENL
       [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
        ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR];
        ALL_TAC] THEN
      SUBGOAL_THEN `!w. (kap:complex->complex) differentiable at w` ASSUME_TAC THENL
       [ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR]; ALL_TAC] THEN
      SUBGOAL_THEN `(F2:complex->real^2) differentiable at ((Tinv:complex->complex) y)`
      ASSUME_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `Ost:complex->bool` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 < det(jacobian (F2:complex->real^2) (at ((Tinv:complex->complex) y)))`
      ASSUME_TAC THENL
       [USE_THEN "det" MATCH_MP_TAC THEN UNDISCH_TAC `(Tinv:complex->complex) y IN Ost` THEN
        EXPAND_TAC "Ost" THEN REWRITE_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      SPEC_TAC(`v:complex`,`v:complex`) THEN
      MATCH_MP_TAC MOI_PDG_DERIV_COMPOSE_INJ THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:complex)` THEN
        ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH];
        MATCH_MP_TAC MOI_PDG_DERIV_COMPOSE_INJ THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC MOI_PDG_DERIV_COMPOSE_INJ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [X_GEN_TAC `w:complex` THEN BETA_TAC THEN
            REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ENTIRE; CNJ_EQ_0] THEN
            STRIP_TAC THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `norm(c:complex) = &1` THEN
            ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN REAL_ARITH_TAC;
            MATCH_MP_TAC MOI_PDG_DET_POS_INJ THEN ASM_REWRITE_TAC[] THEN
            ASM_REAL_ARITH_TAC];
          X_GEN_TAC `w:complex` THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(MP_TAC o AP_TERM `kap:complex->complex`) THEN
          ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
          FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP LINEAR_0)];
        X_GEN_TAC `w:real^2` THEN
        MATCH_MP_TAC(MESON[MOI_PDG_STI_DERIV_INJ]
         `orthogonal_transformation (f:real^3->real^3)
          ==> frechet_derivative (moi_pdg_sti f) (at p) w = vec 0 ==> w = vec 0`) THEN
        ASM_REWRITE_TAC[]]]]);;

let MOI_PDG_FS_INJ = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) M' U phi (z0:complex) c
    (f:real^3->real^3) x y.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (U,phi) IN sigma /\
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\ orthogonal_transformation f /\
      norm c = &1 /\
      z0 + c * x IN IMAGE phi U /\ ~((f(M(chart_inv (U,phi) (z0 + c * x))))$3 = &1) /\
      z0 + c * y IN IMAGE phi U /\ ~((f(M(chart_inv (U,phi) (z0 + c * y))))$3 = &1) /\
      moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * x))) =
      moi_pdg_st f (M(chart_inv (U,phi) (z0 + c * y)))
      ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN IMAGE (phi:real^N->real^2) U /\
        ~(((f:real^3->real^3)((M:real^N->real^3)(chart_inv (U,phi) w)))$3 = &1)
        ==> moi_pdg_sti f (moi_pdg_st f (M(chart_inv (U,phi) w))) = M(chart_inv (U,phi) w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_STI_ST THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (X,sphere(vec 0,&1)) (M:real^N->real^3,M')` THEN
    REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(M:real^N->real^3)(chart_inv (U,phi) (z0 + c * x)) =
                M(chart_inv (U,phi) (z0 + c * y))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `moi_pdg_sti (f:real^3->real^3)` o check (fun th ->
      can (find_term (fun t -> t = `moi_pdg_st (f:real^3->real^3)`)) (concl th) &&
      is_eq (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * x) =
                chart_inv (U,phi) (z0 + c * y)` MP_TAC THENL
   [MATCH_MP_TAC MOI_PDG_HOMEO_INJ THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `M:real^N->real^3`; `M':real^3->real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN(MP_TAC o AP_TERM `phi:real^N->real^2`) THEN ASM_SIMP_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC MOI_PDG_RIGID_INJ THEN
    MAP_EVERY EXISTS_TAC [`z0:complex`; `c:complex`] THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_CREASE_ONE = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) M' U phi z0 c a b e (G0:real^N->bool).
      MOI_SMO_CREASE_STATEMENT /\ MOI_SMO_CREASE_ORIENT_STATEMENT /\
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\
      moi_pdg_crease sigma M U phi z0 c a b e /\
      open_in (subtopology euclidean X) G0 /\
      (!t. a <= t /\ t <= b ==> chart_inv (U,phi) (z0 + c * Cx t) IN G0)
      ==> ?R K (Nm:real^N->real^3).
            open_in (subtopology euclidean X) R /\ R SUBSET G0 /\
            compact K /\ K SUBSET R /\
            (!t. a + e < t /\ t < b - e ==> chart_inv (U,phi) (z0 + c * Cx t) IN R) /\
            (!x. x IN R /\ ~(x IN K) ==> Nm x = M x) /\
            (!x. x IN R ==> Nm x IN sphere(vec 0,&1)) /\
            (!x. x IN R ==> moi_pdg_imm_at sigma Nm x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `M:real^N->real^3`; `M':real^3->real^N`; `U:real^N->bool`;
                 `phi:real^N->real^2`; `z0:complex`; `c:complex`; `a:real`; `b:real`;
                 `e:real`] MOI_PDG_CR_POLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `M:real^N->real^3`; `M':real^3->real^N`; `U:real^N->bool`;
                 `phi:real^N->real^2`; `z0:complex`; `c:complex`; `a:real`; `b:real`;
                 `e:real`; `f:real^3->real^3`; `G0:real^N->bool`] MOI_PDG_CR_FPM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `u:complex->bool`
    (X_CHOOSE_THEN `Fp:complex->real^2` (X_CHOOSE_THEN `Fm:complex->real^2`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "good")
     (CONJUNCTS_THEN2 (LABEL_TAC "vp") (CONJUNCTS_THEN2 (LABEL_TAC "vm")
     (CONJUNCTS_THEN2 (LABEL_TAC "ends") (LABEL_TAC "dets")))))))))))))) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_pdg_crease]) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `M:real^N->real^3`; `M':real^3->real^N`; `U:real^N->bool`;
                 `phi:real^N->real^2`; `z0:complex`; `c:complex`; `a:real`; `b:real`;
                 `f:real^3->real^3`; `d:real`; `u:complex->bool`;
                 `Fp:complex->real^2`; `Fm:complex->real^2`] MOI_PDG_CR_D4A) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN USE_THEN "good" (MP_TAC o SPEC `x:complex`) THEN
      ASM_SIMP_TAC[];
      USE_THEN "dets" (MP_TAC o SPEC `Cx((a + b) / &2)`) THEN
      REWRITE_TAC[RE_CX; IM_CX; REAL_ABS_0] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "dets" (MP_TAC o SPEC `Cx((a + b) / &2)`) THEN
      REWRITE_TAC[RE_CX; IM_CX; REAL_ABS_0] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`Fp:complex->real^2`; `Fm:complex->real^2`; `u:complex->bool`;
                 `d:real`; `a:real`; `b:real`] MOI_PDG_CR_KAPPA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:complex->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `smooth_map_on (:complex) (kap:complex->complex)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_SMB_SMOOTH_LINEAR; OPEN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on u ((kap:complex->complex) o (Fp:complex->real^2)) /\
                smooth_map_on u ((kap:complex->complex) o (Fm:complex->real^2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `(:complex)` THEN ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_SMO_CREASE_STATEMENT] o
    check (fun th -> concl th = `MOI_SMO_CREASE_STATEMENT`)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`(kap:complex->complex) o (Fp:complex->real^2)`;
    `(kap:complex->complex) o (Fm:complex->real^2)`;
    `u:complex->bool`; `a:real`; `b:real`; `d:real`; `e / &2`]) THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; MOI_PDG_CX_VECTOR] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
      TRANS_TAC EQ_TRANS
       `moi_pdg_st (f:real^3->real^3)
          ((M:real^N->real^3)(chart_inv (U,phi) (z0 + c * Cx t)))` THEN
      CONJ_TAC THENL
       [USE_THEN "vp" MATCH_MP_TAC; CONV_TAC SYM_CONV THEN USE_THEN "vm" MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `Cx s = Cx t` (fun th -> REWRITE_TAC[GSYM CX_INJ; th]) THEN
      MATCH_MP_TAC MOI_PDG_FS_INJ THEN
      MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                            `M:real^N->real^3`; `M':real^3->real^N`; `U:real^N->bool`;
                            `phi:real^N->real^2`; `z0:complex`; `c:complex`;
                            `f:real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `!w. a <= w /\ w <= b
            ==> (Fm:complex->real^2) (Cx w) =
                moi_pdg_st (f:real^3->real^3)
                  ((M:real^N->real^3)(chart_inv (U,phi) (z0 + c * Cx w))) /\
                z0 + c * Cx w IN IMAGE (phi:real^N->real^2) U /\
                ~(((f:real^3->real^3)((M:real^N->real^3)
                     (chart_inv (U,phi) (z0 + c * Cx w))))$3 = &1)`
      ASSUME_TAC THENL
       [X_GEN_TAC `w:real` THEN STRIP_TAC THEN CONJ_TAC THENL
         [USE_THEN "vm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[RE_CX; IM_CX] THEN
          ASM_REAL_ARITH_TAC;
          USE_THEN "good" (MP_TAC o SPEC `Cx w`) THEN
          REWRITE_TAC[RE_CX; IM_CX; REAL_ABS_0] THEN
          ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `(kap:complex->complex) ((Fm:complex->real^2) (Cx s)) = kap (Fm (Cx t))` THEN
      DISCH_THEN(MP_TAC o AP_TERM `kap:complex->complex`) THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:complex` THEN STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
      USE_THEN "ends" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `F2:complex->real^2` (X_CHOOSE_THEN `d':real`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_PDG_CR_BUILD THEN
  MAP_EVERY EXISTS_TAC
   [`M':real^3->real^N`; `f:real^3->real^3`; `d:real`; `d':real`; `kap:complex->complex`;
    `(kap:complex->complex) o (Fp:complex->real^2)`;
    `(kap:complex->complex) o (Fm:complex->real^2)`; `F2:complex->real^2`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    USE_THEN "vp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
    USE_THEN "vm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* STAGE2: all creases are smoothed at once (disjoint neighbourhoods).      *)
(* ------------------------------------------------------------------------- *)

let MOI_PDG_IMM_AT_LOCAL = prove
 (`!(X:real^N->bool) sigma (f:real^N->real^3) f' O x.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      open_in (subtopology euclidean X) O /\ x IN O /\
      (!y. y IN O ==> f' y = f y) /\ moi_pdg_imm_at sigma f x
      ==> moi_pdg_imm_at sigma f' x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_imm_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^2`;
                       `W:real^2->bool`; `g:real^2->real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `phi:real^N->real^2`;
                        `W INTER IMAGE (phi:real^N->real^2) (U INTER O)`; `g:real^2->real^3`] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (X:real^N->bool)`;
                          `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SMOOTH_MANIFOLD_ATLAS_CHART];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^N) = x'` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_MESON_TAC[];
    ASM SET_TAC[]]);;

let MOI_PDG_SEG_X_COMPACT = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) U phi z0 c a b e.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      moi_pdg_crease sigma M U phi z0 c a b e
      ==> compact {chart_inv (U,phi) (z0 + c * Cx t) | a <= t /\ t <= b} /\
          {chart_inv (U,phi) (z0 + c * Cx t) | a <= t /\ t <= b} SUBSET X /\
          ~({chart_inv (U,phi) (z0 + c * Cx t) | a <= t /\ t <= b} = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_crease] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] MOI_PDG_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b ==> z0 + c * Cx t IN IMAGE (phi:real^N->real^2) U`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `&0 <= Im x`)) (concl th) &&
      can (find_term (fun t -> t = `a + e:real`)) (concl th) = false)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `g:complex->real^3`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `{chart_inv (U,phi) (z0 + c * Cx t) | a <= t /\ t <= b} =
      IMAGE (chart_inv (U:real^N->bool,phi:real^N->real^2) o (\x. z0 + c * Cx(drop x)))
            (interval[lift a,lift b])`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTERVAL_1; o_THM] THEN
      MESON_TAC[LIFT_DROP];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (phi:real^N->real^2) U` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
    EXISTS_TAC `chart_inv (U:real^N->bool,phi:real^N->real^2) (z0 + c * Cx a)` THEN
    EXISTS_TAC `a:real` THEN ASM_SIMP_TAC[REAL_LE_REFL; REAL_LT_IMP_LE]]);;

let MOI_PDG_DISJ_NBHDS = prove
 (`!(X:real^N->bool) (ix:A->bool) (S:A->real^N->bool).
      FINITE ix /\ (!i. i IN ix ==> compact(S i) /\ S i SUBSET X /\ ~(S i = {})) /\
      (!i j. i IN ix /\ j IN ix /\ ~(i = j) ==> S i INTER S j = {})
      ==> ?G. (!i. i IN ix ==> open_in (subtopology euclidean X) (G i) /\ S i SUBSET G i) /\
              (!i j. i IN ix /\ j IN ix /\ ~(i = j) ==> G i INTER G j = {})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\p:A#A. setdist((S:A->real^N->bool)(FST p),S(SND p))`;
                 `{p:A#A | FST p IN ix /\ SND p IN ix /\ ~(FST p = SND p)}`]
         MOI_PDG_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(ix:A->bool) CROSS ix` THEN
      ASM_SIMP_TAC[FINITE_CROSS] THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS] THEN SIMP_TAC[];
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
      REWRITE_TAC[SETDIST_POS_LE] THEN
      MP_TAC(ISPECL [`(S:A->real^N->bool) i`; `(S:A->real^N->bool) j`]
             SETDIST_EQ_0_COMPACT_CLOSED) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\i. X INTER {x:real^N | ?y. y IN (S:A->real^N->bool) i /\ dist(x,y) < d0 / &3}` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_CONTAINS_BALL; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `d0 / &3 - dist(x:real^N,y)` THEN
      ASM_REWRITE_TAC[REAL_SUB_LT; SUBSET; IN_BALL; IN_ELIM_THM] THEN
      X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN EXISTS_TAC `y:real^N` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `dist(x:real^N,w) < d0 / &3 - dist(x,y)` THEN
      CONV_TAC NORM_ARITH;
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC]];
    MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:A`; `j:A`] o check (fun th ->
      can (find_term (fun t -> t = `d0:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(S:A->real^N->bool) i`; `(S:A->real^N->bool) j`; `y1:real^N`; `y2:real^N`]
           SETDIST_LE_DIST) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < d0`; `dist(x:real^N,y1) < d0 / &3`;
                           `dist(x:real^N,y2) < d0 / &3`] THEN
    MP_TAC(NORM_ARITH `dist(y1:real^N,y2) <= dist(x,y1) + dist(x,y2)`) THEN
    REAL_ARITH_TAC]);;

let MOI_PDG_STAGE2 = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) M' (ix:A->bool) U phi z0 c a b e.
      MOI_SMO_CREASE_STATEMENT /\ MOI_SMO_CREASE_ORIENT_STATEMENT /\
      smooth_manifold_atlas (subtopology euclidean X) sigma /\
      homeomorphism (X,sphere(vec 0,&1)) (M,M') /\
      FINITE ix /\
      (!i. i IN ix
           ==> moi_pdg_crease sigma M (U i) (phi i) (z0 i) (c i) (a i) (b i) (e i)) /\
      (!i j s t. i IN ix /\ j IN ix /\ ~(i = j) /\
                 a i <= s /\ s <= b i /\ a j <= t /\ t <= b j
                 ==> ~(chart_inv (U i,phi i) (z0 i + c i * Cx s) =
                       chart_inv (U j,phi j) (z0 j + c j * Cx t))) /\
      (!x. x IN X /\
           ~(?i t. i IN ix /\ a i + e i < t /\ t < b i - e i /\
                   x = chart_inv (U i,phi i) (z0 i + c i * Cx t))
           ==> moi_pdg_imm_at sigma M x)
      ==> ?M2. IMAGE M2 X SUBSET sphere(vec 0,&1) /\
               !x. x IN X ==> moi_pdg_imm_at sigma M2 x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cr") (CONJUNCTS_THEN2 (LABEL_TAC "disj")
    (LABEL_TAC "off")))))))) THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `ix:A->bool`;
                 `\i:A. {chart_inv ((U:A->real^N->bool) i,(phi:A->real^N->real^2) i)
                           ((z0:A->complex) i + (c:A->complex) i * Cx t) | t |
                           (a:A->real) i <= t /\ t <= (b:A->real) i}`]
         MOI_PDG_DISJ_NBHDS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:A` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_PDG_SEG_X_COMPACT THEN
      MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                            `M:real^N->real^3`; `(e:A->real) i`] THEN
      ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
      USE_THEN "disj" (MP_TAC o SPECL [`i:A`; `j:A`; `s:real`; `t:real`]) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:A->real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. i IN ix
        ==> ?R Kc (Nm:real^N->real^3).
              open_in (subtopology euclidean X) R /\ R SUBSET (G:A->real^N->bool) i /\
              compact Kc /\ Kc SUBSET R /\
              (!t. (a:A->real) i + (e:A->real) i < t /\ t < (b:A->real) i - e i
                   ==> chart_inv ((U:A->real^N->bool) i,(phi:A->real^N->real^2) i)
                         ((z0:A->complex) i + (c:A->complex) i * Cx t) IN R) /\
              (!x. x IN R /\ ~(x IN Kc) ==> Nm x = M x) /\
              (!x. x IN R ==> Nm x IN sphere(vec 0,&1)) /\
              (!x. x IN R ==> moi_pdg_imm_at sigma Nm x)`
  MP_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_PDG_CREASE_ONE THEN
    EXISTS_TAC `M':real^3->real^N` THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:A` o check (fun th ->
      can (find_term (fun t -> t = `G:A->real^N->bool`)) (concl th) &&
      is_forall (concl th) &&
      can (find_term (fun t -> t = `ix:A->bool`)) (concl th) &&
      not (can (find_term (fun t -> t = `j:A`)) (concl th)))) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:A->real^N->bool` (X_CHOOSE_THEN `Kc:A->real^N->bool`
    (X_CHOOSE_THEN `Nm:A->real^N->real^3` (LABEL_TAC "one")))) THEN
  SUBGOAL_THEN `!i j x. i IN ix /\ j IN ix /\ x IN (R:A->real^N->bool) i /\ x IN R j
                        ==> i = j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:A`; `j:A`] o check (fun th ->
      can (find_term (fun t -> t = `G:A->real^N->bool`)) (concl th) &&
      can (find_term (fun t -> t = `j:A`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "one" (MP_TAC o SPEC `i:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "one" (MP_TAC o SPEC `j:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i x. i IN ix /\ x IN (R:A->real^N->bool) i
                      ==> (@i. i IN ix /\ x IN R i) = i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `\x. if ?i. i IN ix /\ x IN (R:A->real^N->bool) i
                  then (Nm:A->real^N->real^3) (@i. i IN ix /\ x IN R i) x else M x` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `i:A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(@i. i IN ix /\ (x:real^N) IN (R:A->real^N->bool) i) = i`
        SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "one" (MP_TAC o SPEC `i:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `homeomorphism (X,sphere(vec 0,&1)) (M:real^N->real^3,M')` THEN
      REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `?i. i IN ix /\ x IN (R:A->real^N->bool) i` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `i:A` STRIP_ASSUME_TAC) THEN
    USE_THEN "one" (MP_TAC o SPEC `i:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC MOI_PDG_IMM_AT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `(Nm:A->real^N->real^3) i`;
                          `(R:A->real^N->bool) i`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?j. j IN ix /\ (y:real^N) IN (R:A->real^N->bool) j`
        (fun th -> REWRITE_TAC[th]) THENL
       [EXISTS_TAC `i:A` THEN ASM_REWRITE_TAC[];
        AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_IMM_AT_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `M:real^N->real^3`;
                        `X DIFF UNIONS (IMAGE (Kc:A->real^N->bool) ix)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `X DIFF s = X INTER ((:real^N) DIFF s)`] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[GSYM closed] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN USE_THEN "one" (MP_TAC o SPEC `i:A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:A` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(?i. i IN ix /\ (x:real^N) IN (R:A->real^N->bool) i)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `i:A` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "one" (MP_TAC o SPEC `i:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    STRIP_TAC THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `j:A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(@i. i IN ix /\ (y:real^N) IN (R:A->real^N->bool) i) = j`
        SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "one" (MP_TAC o SPEC `j:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      REFL_TAC];
    USE_THEN "off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:A` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `~(?i. i IN ix /\ (x:real^N) IN (R:A->real^N->bool) i)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `i:A` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "one" (MP_TAC o SPEC `i:A`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Analytic and topological lemmas for the corner lemma at a vertex *)

let MOI_PDG_HOLO_SMOOTH = prove
 (`!f s. open s /\ f holomorphic_on s ==> smooth_map_on s f`,
  SUBGOAL_THEN
   `!n f s. open s /\ f holomorphic_on s ==> continuously_differentiable n s f`
   (fun th -> MESON_TAC[th; smooth_map_on]) THEN
  INDUCT_TAC THENL
   [SIMP_TAC[CONTINUOUSLY_DIFFERENTIABLE_0; HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUSLY_DIFFERENTIABLE_SUC] THEN
  EXISTS_TAC `\x h. complex_derivative f x * h` THEN CONJ_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    REWRITE_TAC[GSYM has_complex_derivative] THEN
    REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_OPEN; complex_differentiable];
    X_GEN_TAC `h:complex` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
    ASM_SIMP_TAC[HOLOMORPHIC_COMPLEX_DERIVATIVE; HOLOMORPHIC_ON_CONST; ETA_AX]]);;

let MOI_PDG_FIRST_ORDER_RE = prove
 (`!(g:complex->complex) D v.
      (g has_derivative D) (at (vec 0)) /\ g(vec 0) = vec 0 /\ &0 < Re(D v)
      ==> ?t0. &0 < t0 /\ !t. &0 < t /\ t < t0 ==> &0 < Re(g(t % v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(D:complex->complex)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN `~(v:complex = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&0 < Re((D:complex->complex) (vec 0))` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    REWRITE_TAC[COMPLEX_VEC_0; RE_CX; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(v:complex)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `((g:complex->complex) has_derivative D) (at (vec 0))` THEN
  REWRITE_TAC[HAS_DERIVATIVE_AT] THEN
  DISCH_THEN(MP_TAC o SPEC `(Re((D:complex->complex) v) / &2) / norm(v:complex)` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d / norm(v:complex)` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t % v:complex`) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN `norm(t % v:complex) = t * norm v` SUBST1_TAC THENL
   [REWRITE_TAC[NORM_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  SUBGOAL_THEN `&0 < t * norm(v:complex)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t * norm(v:complex) < d` ASSUME_TAC THENL
   [UNDISCH_TAC `t < d / norm(v:complex)` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `(Re((D:complex->complex) v) / &2) / norm(v:complex) * t * norm v =
                t * (Re(D v) / &2)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(v:complex)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `(g:complex->complex)(t % v) - t % D v` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB; RE_CMUL] THEN
  MP_TAC(SPECL [`t:real`; `Re((D:complex->complex) v)`] REAL_LT_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`norm((g:complex->complex)(t % v) - t % D v) < t * Re(D v) / &2`] THEN
  REAL_ARITH_TAC);;

let MOI_PDG_FIRST_ORDER = prove
 (`!(g:complex->complex) D v c.
      (g has_derivative D) (at (vec 0)) /\ g(vec 0) = vec 0 /\ &0 < Re(c * D v)
      ==> ?t0. &0 < t0 /\ !t. &0 < t /\ t < t0 ==> &0 < Re(c * g(t % v))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. c * (g:complex->complex) z`; `\h. c * (D:complex->complex) h`;
                 `v:complex`] MOI_PDG_FIRST_ORDER_RE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\z. c * (g:complex->complex) z) = (\w. c * w) o g /\
                  (\h. c * (D:complex->complex) h) = (\w. c * w) o D`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
    REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING;
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO];
    ASM_REWRITE_TAC[]]);;

let MOI_PDG_CLOSED_QUAD_LIMIT = prove
 (`!(g:complex->complex) y v s0.
      g continuous at y /\ &0 < s0 /\
      (!s. &0 < s /\ s < s0 ==> &0 <= Re(g(y + s % v)) /\ &0 <= Im(g(y + s % v)))
      ==> &0 <= Re(g y) /\ &0 <= Im(g y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) /\ (~q ==> F) ==> p /\ q`) THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [UNDISCH_TAC `(g:complex->complex) continuous at y` THEN
    REWRITE_TAC[continuous_at] THEN
    DISCH_THEN(MP_TAC o SPEC `--Re((g:complex->complex) y)`);
    UNDISCH_TAC `(g:complex->complex) continuous at y` THEN
    REWRITE_TAC[continuous_at] THEN
    DISCH_THEN(MP_TAC o SPEC `--Im((g:complex->complex) y)`)] THEN
  ((ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = min (s0 / &2) (d / (norm(v:complex) + &1) / &2)` THEN
  SUBGOAL_THEN `&0 < norm(v:complex) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `v:complex` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s /\ s < s0 /\ s * (norm(v:complex) + &1) < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    SUBGOAL_THEN `&0 < d / (norm(v:complex) + &1)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(d / (norm(v:complex) + &1) / &2) * (norm v + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(d / (norm(v:complex) + &1) / &2) * (norm v + &1) = d / &2`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < norm(v:complex) + &1` THEN CONV_TAC REAL_FIELD;
          ASM_REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Re((g:complex->complex)(y + s % v)) /\ &0 <= Im(g(y + s % v))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `s0:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(y + s % v:complex,y) < d` ASSUME_TAC THENL
   [REWRITE_TAC[dist; VECTOR_ARITH `(y + s % v) - y:complex = s % v`; NORM_MUL] THEN
    SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `v:complex` NORM_POS_LE) THEN
    MP_TAC(SPECL [`s:real`; `norm(v:complex)`] REAL_LE_MUL) THEN
    UNDISCH_TAC `s * (norm(v:complex) + &1) < d` THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y + s % v:complex` o check (fun th ->
    can (find_term (fun t -> t = `d:real`)) (concl th) && is_forall (concl th))) THEN
  ASM_REWRITE_TAC[dist] THEN DISCH_TAC THEN
  MP_TAC(SPEC `(g:complex->complex)(y + s % v) - g y` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB; IM_SUB] THEN ASM_REAL_ARITH_TAC));;

let MOI_PDG_CLOPEN_DICHOTOMY = prove
 (`!(W:complex->bool) P.
      connected W /\
      open_in (subtopology euclidean W) {y | y IN W /\ P y} /\
      closed_in (subtopology euclidean W) {y | y IN W /\ P y}
      ==> (!y. y IN W ==> P y) \/ (!y. y IN W ==> ~P y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `{y:complex | y IN W /\ P y}`) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let MOI_PDG_CORNER_TOP = prove
 (`!(g:complex->complex) (Linv:complex->complex) rho v.
      &0 < rho /\ g continuous_on ball(vec 0,rho) /\
      (g has_derivative Linv) (at (vec 0)) /\ g(vec 0) = vec 0 /\
      linear Linv /\ Linv v = Cx(&1) + ii /\
      (!y. y IN ball(vec 0,rho) /\ &0 <= Re(g y) /\ &0 <= Im(g y) /\ Im(g y) = &0
           ==> &0 <= Re(Linv y) /\ Im(Linv y) = &0) /\
      (!y. y IN ball(vec 0,rho) /\ &0 <= Re(g y) /\ &0 <= Im(g y) /\ Re(g y) = &0
           ==> Re(Linv y) = &0 /\ &0 <= Im(Linv y))
      ==> !y. y IN ball(vec 0,rho)
              ==> (&0 <= Re(g y) /\ &0 <= Im(g y) <=>
                   &0 <= Re(Linv y) /\ &0 <= Im(Linv y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "r1") (LABEL_TAC "r2")))))))) THEN
  (* points along v and --v *)
  SUBGOAL_THEN
   `?t1. &0 < t1 /\ t1 * norm(v:complex) < rho /\
         &0 < Re((g:complex->complex)(t1 % v)) /\ &0 < Im(g(t1 % v)) /\
         Re(g(t1 % --v)) < &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:complex->complex`; `Linv:complex->complex`; `v:complex`; `Cx(&1)`]
           MOI_PDG_FIRST_ORDER) THEN
    MP_TAC(ISPECL [`g:complex->complex`; `Linv:complex->complex`; `v:complex`; `--ii`]
           MOI_PDG_FIRST_ORDER) THEN
    MP_TAC(ISPECL [`g:complex->complex`; `Linv:complex->complex`; `--v:complex`; `--Cx(&1)`]
           MOI_PDG_FIRST_ORDER) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_NEG th]) THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN
    REWRITE_TAC[COMPLEX_RING `--Cx(&1) * --(Cx(&1) + ii) = Cx(&1) + ii`;
                COMPLEX_RING `--ii * (Cx(&1) + ii) = Cx(&1) - ii`;
                RE_ADD; RE_SUB; RE_CX; RE_II; IM_ADD; IM_CX; IM_II] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `ta:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `tb:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `tc:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `tau = min (min ta tb) (min tc (rho / (norm(v:complex) + &1))) / &2` THEN
    SUBGOAL_THEN `&0 < rho / (norm(v:complex) + &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `v:complex` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < tau /\ tau < ta /\ tau < tb /\ tau < tc /\
                  &2 * tau <= rho / (norm(v:complex) + &1)` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "tau" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `tau:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&2 * tau <= rho / (norm(v:complex) + &1)` THEN
      SUBGOAL_THEN `&0 < norm(v:complex) + &1` ASSUME_TAC THENL
       [MP_TAC(ISPEC `v:complex` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      MP_TAC(ISPEC `v:complex` NORM_POS_LE) THEN
      MP_TAC(SPECL [`tau:real`; `norm(v:complex)`] REAL_LE_MUL) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE] THEN
      UNDISCH_TAC `&0 < tau` THEN UNDISCH_TAC `&0 < rho` THEN
      REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th ->
        can (find_term (fun t -> t = `tc:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th ->
        can (find_term (fun t -> t = `tb:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_LNEG; RE_NEG; RE_MUL_II] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `tau:real` o check (fun th ->
        can (find_term (fun t -> t = `ta:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_MUL_LID; RE_NEG] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `B = ball(vec 0:complex,rho)` THEN
  SUBGOAL_THEN `open(B:complex->bool) /\ convex(B:complex->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[OPEN_BALL; CONVEX_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(t1 % v:complex) IN B /\ (t1 % --v:complex) IN B` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[IN_BALL_0; NORM_MUL; NORM_NEG] THEN
    SUBGOAL_THEN `abs t1 = t1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Linv:complex->complex)(t1 % v) = Cx t1 + ii * Cx t1 /\
                Linv(t1 % --v) = --(Cx t1 + ii * Cx t1)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th; MATCH_MP LINEAR_NEG th]) THEN
    ASM_REWRITE_TAC[COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:complex->complex) continuous_on B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open {z:complex | &0 < Re z /\ &0 < Im z} /\
                closed {z:complex | &0 <= Re z /\ &0 <= Im z}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE `{z:complex | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
      MATCH_MP_TAC OPEN_INTER THEN
      REWRITE_TAC[GSYM real_gt; OPEN_HALFSPACE_RE_GT; OPEN_HALFSPACE_IM_GT];
      REWRITE_TAC[SET_RULE `{z:complex | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
      MATCH_MP_TAC CLOSED_INTER THEN
      REWRITE_TAC[GSYM real_ge; CLOSED_HALFSPACE_RE_GE; CLOSED_HALFSPACE_IM_GE]];
    ALL_TAC] THEN
  (* the complement of the closed cone in B: no point of the quadrant *)
  ABBREV_TAC `W = {y | y IN B /\ (Linv:complex->complex) y IN {z | Re z < &0}} UNION
                  {y | y IN B /\ (Linv:complex->complex) y IN {z | Im z < &0}}` THEN
  SUBGOAL_THEN `!y. y IN W ==> ~(&0 <= Re((g:complex->complex) y) /\ &0 <= Im(g y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`W:complex->bool`;
                   `\y. &0 <= Re((g:complex->complex) y) /\ &0 <= Im(g y)`]
           MOI_PDG_CLOPEN_DICHOTOMY) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "W" THEN MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONVEX_CONNECTED THEN
          REWRITE_TAC[SET_RULE `{y:complex | y IN B /\ (f:complex->complex) y IN s} = B INTER {y | f y IN s}`] THEN
          MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC CONVEX_LINEAR_PREIMAGE THEN
          ASM_REWRITE_TAC[CONVEX_HALFSPACE_RE_LT];
          MATCH_MP_TAC CONVEX_CONNECTED THEN
          REWRITE_TAC[SET_RULE `{y:complex | y IN B /\ (f:complex->complex) y IN s} = B INTER {y | f y IN s}`] THEN
          MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC CONVEX_LINEAR_PREIMAGE THEN
          ASM_REWRITE_TAC[CONVEX_HALFSPACE_IM_LT];
          REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
          EXISTS_TAC `t1 % --v:complex` THEN
          ASM_REWRITE_TAC[RE_NEG; IM_NEG; RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_II;
                          IM_MUL_II] THEN
          ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN
         `{y | y IN W /\ &0 <= Re((g:complex->complex) y) /\ &0 <= Im(g y)} =
          {y | y IN W /\ g y IN {z | &0 < Re z /\ &0 < Im z}}`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:complex` THEN
          ASM_CASES_TAC `(y:complex) IN W` THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(y:complex) IN B /\
                        (Re((Linv:complex->complex) y) < &0 \/ Im(Linv y) < &0)`
          (CONJUNCTS_THEN ASSUME_TAC) THENL
           [UNDISCH_TAC `(y:complex) IN W` THEN EXPAND_TAC "W" THEN
            REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN MESON_TAC[];
            ALL_TAC] THEN
          EQ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN STRIP_TAC THEN
          CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
           [USE_THEN "r2" (MP_TAC o SPEC `y:complex`);
            USE_THEN "r1" (MP_TAC o SPEC `y:complex`)] THEN
          (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);
          MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:complex->bool` THEN
          ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN SET_TAC[]];
        SUBGOAL_THEN
         `{y | y IN W /\ &0 <= Re((g:complex->complex) y) /\ &0 <= Im(g y)} =
          {y | y IN W /\ g y IN {z | &0 <= Re z /\ &0 <= Im z}}`
        SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:complex->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "W" THEN SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
    DISCH_THEN(MP_TAC o SPEC `t1 % --v:complex`) THEN
    MATCH_MP_TAC(TAUT `p /\ ~q ==> (p ==> q) ==> F`) THEN CONJ_TAC THENL
     [EXPAND_TAC "W" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[RE_NEG; RE_ADD; RE_CX; RE_MUL_II; IM_CX] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the open cone maps into the quadrant *)
  ABBREV_TAC `C0 = {y | y IN B /\
                        (Linv:complex->complex) y IN {z | &0 < Re z /\ &0 < Im z}}` THEN
  SUBGOAL_THEN `!y. y IN C0 ==> &0 <= Re((g:complex->complex) y) /\ &0 <= Im(g y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`C0:complex->bool`;
                   `\y. &0 <= Re((g:complex->complex) y) /\ &0 <= Im(g y)`]
           MOI_PDG_CLOPEN_DICHOTOMY) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [EXPAND_TAC "C0" THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
        REWRITE_TAC[SET_RULE `{y:complex | y IN B /\ (f:complex->complex) y IN s} =
                              B INTER {y | f y IN s}`] THEN
        MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONVEX_LINEAR_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SET_RULE `{z:complex | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
        MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[GSYM real_gt; CONVEX_HALFSPACE_RE_GT; CONVEX_HALFSPACE_IM_GT];
        SUBGOAL_THEN
         `{y | y IN C0 /\ &0 <= Re((g:complex->complex) y) /\ &0 <= Im(g y)} =
          {y | y IN C0 /\ g y IN {z | &0 < Re z /\ &0 < Im z}}`
        SUBST1_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:complex` THEN
          ASM_CASES_TAC `(y:complex) IN C0` THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(y:complex) IN B /\ &0 < Re((Linv:complex->complex) y) /\
                        &0 < Im(Linv y)` STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `(y:complex) IN C0` THEN EXPAND_TAC "C0" THEN
            REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
            ALL_TAC] THEN
          EQ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN STRIP_TAC THEN
          CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
          ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
           [USE_THEN "r2" (MP_TAC o SPEC `y:complex`);
            USE_THEN "r1" (MP_TAC o SPEC `y:complex`)] THEN
          (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);
          MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:complex->bool` THEN
          ASM_REWRITE_TAC[] THEN EXPAND_TAC "C0" THEN SET_TAC[]];
        SUBGOAL_THEN
         `{y | y IN C0 /\ &0 <= Re((g:complex->complex) y) /\ &0 <= Im(g y)} =
          {y | y IN C0 /\ g y IN {z | &0 <= Re z /\ &0 <= Im z}}`
        SUBST1_TAC THENL [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `B:complex->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "C0" THEN SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
    DISCH_THEN(MP_TAC o SPEC `t1 % v:complex`) THEN
    MATCH_MP_TAC(TAUT `p /\ q ==> (p ==> ~q) ==> F`) THEN CONJ_TAC THENL
     [EXPAND_TAC "C0" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[RE_ADD; RE_CX; RE_MUL_II; IM_CX; IM_ADD; IM_MUL_II] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `y:complex` THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:complex) IN W` ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    STRIP_TAC THEN
    SUBGOAL_THEN `?e. &0 < e /\ ball(y:complex,e) SUBSET B` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(v:complex) + &1` ASSUME_TAC THENL
     [MP_TAC(ISPEC `v:complex` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_PDG_CLOSED_QUAD_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`v:complex`; `e / (norm(v:complex) + &1)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT];
      ASM_SIMP_TAC[REAL_LT_DIV];
      X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
         can (find_term (fun t -> t = `C0:complex->bool`)) (concl th) &&
         is_forall (concl th))) THEN
      EXPAND_TAC "C0" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [UNDISCH_TAC `ball(y:complex,e) SUBSET B` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
        REWRITE_TAC[dist; VECTOR_ARITH `y - (y + s % v):complex = --(s % v)`;
                    NORM_NEG; NORM_MUL] THEN
        SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `s < e / (norm(v:complex) + &1)` THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
        REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th;
                                          MATCH_MP LINEAR_CMUL th]) THEN
        ASM_REWRITE_TAC[RE_ADD; IM_ADD; RE_CMUL; IM_CMUL; RE_CX; IM_CX; RE_II; IM_II] THEN
        ASM_REAL_ARITH_TAC]]]);;

(* The vertex package (predicate moi_pdg_vp) *)

let moi_pdg_vp = new_definition
 `moi_pdg_vp (L:(real^N->bool)->bool)
             (sigma:((real^N->bool)#(real^N->real^2))->bool)
             (h:real^N->real^3) (w:real^N) (delta:real)
             (U:real^N->bool) (phi:real^N->real^2) (rho:real) (R1:real)
             (f:real^3->real^3) (V:complex->complex)
             (uedge:(real^N->bool)->complex) (uart:(real^N->bool)->complex) <=>
    (U,phi) IN sigma /\ w IN U /\ phi w = vec 0 /\ &0 < R1 /\ R1 < rho /\
    cball(vec 0,rho) SUBSET IMAGE phi U /\
    (!z. z IN cball(vec 0,rho) ==> chart_inv (U,phi) z IN ball(w,delta)) /\
    orthogonal_transformation f /\
    V continuous_on cball(vec 0,rho) /\
    (!z. z IN cball(vec 0,rho) /\ rho / &2 <= norm z
         ==> V z = moi_pdg_st f (h(chart_inv (U,phi) z)) /\
             ~((f(h(chart_inv (U,phi) z)))$3 = &1)) /\
    (?u0. open u0 /\ cball(vec 0,R1) SUBSET u0 /\ smooth_map_on u0 V /\
          !y. y IN u0 ==> &0 < det(jacobian V (at y))) /\
    (!e. e IN L /\ aff_dim e = &1 /\ w IN e
         ==> norm(uedge e) = &1 /\
             (!t. &0 <= t /\ t < rho ==> chart_inv (U,phi) (Cx t * uedge e) IN e) /\
             (!x. x IN e /\ x IN U /\ norm(phi x) < rho
                  ==> ?t. &0 <= t /\ phi x = Cx t * uedge e)) /\
    (!s. s IN L /\ aff_dim s = &2 /\ w IN s
         ==> norm(uart s) = &1 /\
             (!t. &0 < t /\ t < rho
                  ==> chart_inv (U,phi) (Cx t * uart s) IN relative_interior s)) /\
    (!z. z IN ball(vec 0,rho) /\ ~(z = vec 0) /\
         (!e t. e IN L /\ aff_dim e = &1 /\ w IN e /\ &0 < t ==> ~(z = Cx t * uedge e)) /\
         (!s t. s IN L /\ aff_dim s = &2 /\ w IN s /\ &0 < t ==> ~(z = Cx t * uart s))
         ==> ?r. &0 < r /\ ball(z,r) SUBSET ball(vec 0,rho) /\
                 smooth_map_on (ball(z,r)) V /\
                 !y. y IN ball(z,r) ==> &0 < det(jacobian V (at y))) /\
    (!v t. ((?e. e IN L /\ aff_dim e = &1 /\ w IN e /\ v = uedge e) \/
            (?s. s IN L /\ aff_dim s = &2 /\ w IN s /\ v = uart s)) /\
           &0 < t /\ t < rho
           ==> (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:complex->complex) /\
                      (!x. x IN ball(Cx t,r) ==> v * x IN ball(vec 0,rho)) /\
                      (!x. x IN ball(Cx t,r) /\ &0 <= Im x ==> g x = V(v * x)) /\
                      (!x. x IN ball(Cx t,r) ==> &0 < det(jacobian g (at x)))) /\
               (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:complex->complex) /\
                      (!x. x IN ball(Cx t,r) ==> v * x IN ball(vec 0,rho)) /\
                      (!x. x IN ball(Cx t,r) /\ Im x <= &0 ==> g x = V(v * x)) /\
                      (!x. x IN ball(Cx t,r) ==> &0 < det(jacobian g (at x))))) /\
    (!s t. s IN L /\ aff_dim s = &2 /\ w IN s /\ rho / &4 <= t /\ t < rho
           ==> ?r. &0 < r /\ smooth_map_on (ball(Cx t,r)) (\x. V(uart s * x)) /\
                   (!x. x IN ball(Cx t,r) ==> uart s * x IN ball(vec 0,rho)))`;;

(* The vertex package statement: around every vertex the map can be       *)
(* modified to a smooth immersion with the properties of moi_pdg_vp.       *)
(* Proved from the leaves below (MOI_PDG_VP_FROM_LEAVES).                    *)

let moi_pdg_vp_statement = new_definition
 `moi_pdg_vp_statement (u:N->bool) <=>
    !L sigma (h:real^N->real^3) h' w delta.
      simplicial_complex L /\
      smooth_manifold_atlas (subtopology euclidean (UNIONS L)) sigma /\
      homeomorphism (UNIONS L,sphere(vec 0,&1)) (h,h') /\
      moi_smo_conical_pd L sigma h /\ {w} IN L /\ &0 < delta
      ==> ?U phi rho R1 f V uedge uart.
            moi_pdg_vp L sigma h w delta U phi rho R1 f V uedge uart`;;

(* Generic planar lemmas for the assembly: side preservation along the
   real axis, derivatives along the axis, determinants of compositions and
   local injectivity of a creased map with positive one-sided Jacobians. *)

let MOI_PDG_IM_CONT = prove
 (`!(Tm:complex->complex) m s.
      Tm continuous_on s ==> (\x. lift(m * Im(Tm x))) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
  SUBGOAL_THEN `(\x. lift(Im((Tm:complex->complex) x))) = (\y. lift(y$2)) o Tm`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; IM_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  MATCH_MP_TAC LINEAR_LIFT_DOLLAR_COMPONENT THEN
  REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC);;

let MOI_PDG_SHIFT_DERIV = prove
 (`!(Tm:complex->complex) A z.
      (Tm has_derivative A) (at z)
      ==> ((\x. Tm(x + z) - Tm z) has_derivative A) (at (vec 0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `A = \h. (A:complex->complex) h - vec 0` SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_RZERO; ETA_AX]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSLATION THEN ASM_REWRITE_TAC[VECTOR_ADD_LID]);;

let MOI_PDG_SIDE_UP = prove
 (`!(Tm:complex->complex) A p r.
      &0 < r /\ Tm continuous_on ball(Cx p,r) /\ (Tm has_derivative A) (at (Cx p)) /\
      Im(Tm(Cx p)) = &0 /\ ~(Im(A ii) = &0) /\
      (!x. x IN ball(Cx p,r) /\ &0 < Im x ==> ~(Im(Tm x) = &0))
      ==> !x. x IN ball(Cx p,r) /\ &0 < Im x ==> &0 < Im(A ii) * Im(Tm x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(A:complex->complex)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?x0. x0 IN ball(Cx p,r) /\ &0 < Im x0 /\
         &0 < Im((A:complex->complex) ii) * Im((Tm:complex->complex) x0)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. (Tm:complex->complex)(x + Cx p) - Tm(Cx p)`;
                   `A:complex->complex`; `ii`;
                   `Cx(Im((A:complex->complex) ii)) * --ii`] MOI_PDG_FIRST_ORDER) THEN
    REWRITE_TAC[VECTOR_ADD_LID; VECTOR_SUB_REFL] THEN
    ASM_SIMP_TAC[MOI_PDG_SHIFT_DERIV] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; COMPLEX_MUL_LNEG; RE_NEG;
                RE_MUL_II; REAL_NEG_NEG; IM_SUB] THEN
    ASM_REWRITE_TAC[REAL_LT_SQUARE; REAL_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(min t0 r / &2) % ii + Cx p` THEN
    REWRITE_TAC[IN_BALL; dist; IM_ADD; IM_CMUL; IM_II; IM_CX;
                VECTOR_ARITH `Cx p - (x + Cx p) = --x`; NORM_NEG; NORM_MUL;
                COMPLEX_NORM_II] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{x:complex | x IN ball(Cx p,r) /\ &0 < Im x}`;
                 `\x. Im((A:complex->complex) ii) * Im((Tm:complex->complex) x)`;
                 `x0:complex`; `x:complex`] MOI_PDG_SIGN_CONST) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      REWRITE_TAC[SET_RULE `{x:complex | x IN s /\ P x} = s INTER {x | P x}`] THEN
      MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_BALL; GSYM real_gt; CONVEX_HALFSPACE_IM_GT];
      MATCH_MP_TAC MOI_PDG_IM_CONT THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(Cx p,r)` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM; REAL_ENTIRE; DE_MORGAN_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_SIDE_DOWN = prove
 (`!(Tm:complex->complex) A p r.
      &0 < r /\ Tm continuous_on ball(Cx p,r) /\ (Tm has_derivative A) (at (Cx p)) /\
      Im(Tm(Cx p)) = &0 /\ ~(Im(A ii) = &0) /\
      (!x. x IN ball(Cx p,r) /\ Im x < &0 ==> ~(Im(Tm x) = &0))
      ==> !x. x IN ball(Cx p,r) /\ Im x < &0 ==> Im(A ii) * Im(Tm x) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear(A:complex->complex)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?x0. x0 IN ball(Cx p,r) /\ Im x0 < &0 /\
         Im((A:complex->complex) ii) * Im((Tm:complex->complex) x0) < &0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x. (Tm:complex->complex)(x + Cx p) - Tm(Cx p)`;
                   `A:complex->complex`; `--ii`;
                   `Cx(Im((A:complex->complex) ii)) * ii`] MOI_PDG_FIRST_ORDER) THEN
    REWRITE_TAC[VECTOR_ADD_LID; VECTOR_SUB_REFL] THEN
    ASM_SIMP_TAC[MOI_PDG_SHIFT_DERIV] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_NEG th]) THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; RE_MUL_CX; COMPLEX_MUL_RNEG; RE_NEG;
                RE_MUL_II; REAL_NEG_NEG; IM_SUB; IM_NEG; REAL_MUL_RNEG] THEN
    ASM_REWRITE_TAC[REAL_LT_SQUARE; REAL_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(min t0 r / &2) % --ii + Cx p` THEN
    REWRITE_TAC[IN_BALL; dist; IM_ADD; IM_CMUL; IM_II; IM_CX; IM_NEG;
                VECTOR_ARITH `Cx p - (x + Cx p) = --x`; NORM_NEG; NORM_MUL;
                COMPLEX_NORM_II] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 < --(m * y) ==> m * y < &0`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{x:complex | x IN ball(Cx p,r) /\ Im x < &0}`;
                 `\x. Im((A:complex->complex) ii) * Im((Tm:complex->complex) x)`;
                 `x0:complex`; `x:complex`] MOI_PDG_SIGN_CONST) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      REWRITE_TAC[SET_RULE `{x:complex | x IN s /\ P x} = s INTER {x | P x}`] THEN
      MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_BALL; CONVEX_HALFSPACE_IM_LT];
      MATCH_MP_TAC MOI_PDG_IM_CONT THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(Cx p,r)` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM; REAL_ENTIRE; DE_MORGAN_THM] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]];
    ONCE_REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_AXIS_DERIV = prove
 (`!(f:complex->complex) g A B p d.
      (f has_derivative A) (at (Cx p)) /\ (g has_derivative B) (at (Cx p)) /\
      &0 < d /\ (!t. abs(t - p) < d ==> f(Cx t) = g(Cx t))
      ==> A(Cx(&1)) = B(Cx(&1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(A:complex->complex) /\ linear(B:complex->complex)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:complex->complex`; `A:complex->complex`;
                 `g:complex->complex`; `B:complex->complex`; `at(Cx p)`]
         HAS_DERIVATIVE_SUB) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_AT] THEN
  DISCH_THEN(MP_TAC o SPEC `norm((A:complex->complex)(Cx(&1)) - B(Cx(&1)))` o CONJUNCT2) THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(TAUT `(~p ==> q /\ ~r) ==> (q ==> r) ==> p`) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[NORM_POS_LT; NOT_EXISTS_THM] THEN
  X_GEN_TAC `e:real` THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = min e d / &2` THEN
  SUBGOAL_THEN `&0 < m /\ m < e /\ m < d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `Cx(p + m)` THEN
  SUBGOAL_THEN `Cx(p + m) - Cx p = m % Cx(&1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CX_SUB; COMPLEX_CMUL; GSYM CX_MUL] THEN AP_TERM_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; COMPLEX_NORM_CX; VECTOR_MUL_EQ_0; COMPLEX_VEC_0; CX_INJ] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < m ==> abs m = m`; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH; REAL_MUL_RID; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `(f:complex->complex)(Cx(p + m)) = g(Cx(p + m)) /\
                f(Cx p) = g(Cx p)` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_SUB_LZERO; NORM_NEG; VECTOR_NEG_0] THEN
  ASM_SIMP_TAC[LINEAR_CMUL] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL; NORM_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < m ==> abs m = m`] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < m ==> (m * x) / m = x`; REAL_LT_REFL]);;

let MOI_PDG_DET_FIX1 = prove
 (`!A:complex->complex. linear A /\ A(Cx(&1)) = Cx(&1) ==> det(matrix A) = Im(A ii)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[DET_2; matrix; LAMBDA_BETA; DIMINDEX_2; ARITH; COMPLEX_BASIS] THEN
  ASM_REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_CX; IM_CX] THEN REAL_ARITH_TAC);;

let MOI_PDG_DET_CHAIN = prove
 (`!(f:real^2->real^2) g x.
      f differentiable at x /\ g differentiable at (f x)
      ==> det(jacobian (g o f) (at x)) =
          det(jacobian g (at (f x))) * det(jacobian f (at x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN
  SUBGOAL_THEN `frechet_derivative ((g:real^2->real^2) o (f:real^2->real^2)) (at x) =
                frechet_derivative g (at (f x)) o frechet_derivative f (at x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; LINEAR_FRECHET_DERIVATIVE; DET_MUL]);;

let MOI_PDG_DET_INV = prove
 (`!(f:real^2->real^2) g t x.
      open t /\ x IN t /\ (!y. y IN t ==> g(f y) = y) /\
      f differentiable at x /\ g differentiable at (f x)
      ==> det(jacobian g (at (f x))) * det(jacobian f (at x)) = &1`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM MOI_PDG_DET_CHAIN] THEN
  SUBGOAL_THEN `jacobian ((g:real^2->real^2) o (f:real^2->real^2)) (at x) = mat 1`
  SUBST1_TAC THENL [ALL_TAC; REWRITE_TAC[DET_I]] THEN
  REWRITE_TAC[jacobian; GSYM MATRIX_ID] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\y:real^2. y`] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN
  X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `ball(x:real^2,d) SUBSET t` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

let MOI_PDG_CREASE_INJ = prove
 (`!(Gp:complex->complex) Gm p r.
      &0 < r /\ smooth_map_on (ball(Cx p,r)) Gp /\ smooth_map_on (ball(Cx p,r)) Gm /\
      (!x. x IN ball(Cx p,r)
           ==> &0 < det(jacobian Gp (at x)) /\ &0 < det(jacobian Gm (at x))) /\
      (!t. Cx t IN ball(Cx p,r) ==> Gp(Cx t) = Gm(Cx t))
      ==> ?d. &0 < d /\ d <= r /\
              !x y. x IN ball(Cx p,d) /\ y IN ball(Cx p,d) /\
                    (if &0 <= Im x then Gp x else Gm x) =
                    (if &0 <= Im y then Gp y else Gm y)
                    ==> x = y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "axis" o ONCE_REWRITE_RULE[GSYM VECTOR_SUB_EQ]))))) THEN
  SUBGOAL_THEN `Cx p IN ball(Cx p,r)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(jacobian (Gp:complex->complex) (at (Cx p))) /\
                &0 < det(jacobian (Gm:complex->complex) (at (Cx p)))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Gp:complex->complex`; `ball(Cx p,r)`; `Cx p`]
         SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_BALL; GSYM jacobian; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tp:complex->bool` (X_CHOOSE_THEN `up:complex->bool`
    (X_CHOOSE_THEN `gp:complex->complex`
      (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on])))) THEN
  MP_TAC(ISPECL [`Gm:complex->complex`; `ball(Cx p,r)`; `Cx p`]
         SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[OPEN_BALL; GSYM jacobian; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tm:complex->bool` (X_CHOOSE_THEN `um:complex->bool`
    (X_CHOOSE_THEN `gm:complex->complex`
      (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on])))) THEN
  SUBGOAL_THEN `(Gm:complex->complex)(Cx p) = Gp(Cx p)` ASSUME_TAC THENL
   [USE_THEN "axis" (MP_TAC o SPEC `p:real`) THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. Cx t IN tp ==> (gp:complex->complex)((Gm:complex->complex)(Cx t)) = Cx t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(Gm:complex->complex)(Cx t) = Gp(Cx t)` SUBST1_TAC THENL
     [USE_THEN "axis" (MP_TAC o SPEC `t:real`) THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
      ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      UNDISCH_TAC `tp SUBSET ball(Cx p,r)` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `N0 = {y | y IN tm INTER tp /\ (Gm:complex->complex) y IN up}` THEN
  SUBGOAL_THEN `open(N0:complex->bool) /\ N0 SUBSET tm /\ N0 SUBSET tp /\
                IMAGE (Gm:complex->complex) N0 SUBSET up` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N0" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC[OPEN_INTER] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `tm:complex->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN SET_TAC[];
      SET_TAC[]; SET_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((gp:complex->complex) o (Gm:complex->complex)) continuous_on N0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `tm:complex->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `up:complex->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]];
    ALL_TAC] THEN
  ABBREV_TAC `N1 = {x | x IN N0 /\ ((gp:complex->complex) o (Gm:complex->complex)) x IN
                        tm INTER tp}` THEN
  SUBGOAL_THEN `open(N1:complex->bool) /\ Cx p IN N1 /\ N1 SUBSET N0 /\
                (!x. x IN N1 ==> x IN tm /\ x IN tp /\ (Gm:complex->complex) x IN up /\
                                 (gp:complex->complex)(Gm x) IN tm /\ gp(Gm x) IN tp)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N1" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_SIMP_TAC[OPEN_INTER; ETA_AX];
      REWRITE_TAC[IN_ELIM_THM; IN_INTER; o_THM] THEN EXPAND_TAC "N0" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_SIMP_TAC[];
      SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM; IN_INTER; o_THM] THEN EXPAND_TAC "N0" THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((gp:complex->complex) o (Gm:complex->complex)) differentiable at (Cx p)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `tm:complex->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `up:complex->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `A = frechet_derivative ((gp:complex->complex) o (Gm:complex->complex))
                                     (at (Cx p))` THEN
  SUBGOAL_THEN `linear(A:complex->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `(((gp:complex->complex) o (Gm:complex->complex)) has_derivative A)
                (at (Cx p))` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  SUBGOAL_THEN `?d1. &0 < d1 /\ ball(Cx p,d1) SUBSET N1` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `Cx p` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open(N1:complex->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx p,d1)
                    ==> x IN tm /\ x IN tp /\ (Gm:complex->complex) x IN up /\
                        (gp:complex->complex)(Gm x) IN tm /\ gp(Gm x) IN tp`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN N1` (fun th -> ASM_MESON_TAC[th]) THEN
    UNDISCH_TAC `ball(Cx p,d1) SUBSET N1` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:complex->complex)(Cx(&1)) = Cx(&1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(gp:complex->complex) o (Gm:complex->complex)`; `\x:complex. x`;
                   `A:complex->complex`; `\h:complex. h`; `p:real`; `d1:real`]
           MOI_PDG_AXIS_DERIV) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `Cx t IN ball(Cx p,d1)` (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[IN_BALL; DIST_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Im((A:complex->complex) ii)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM MOI_PDG_DET_FIX1] THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[GSYM jacobian] THEN
    SUBGOAL_THEN `(Gm:complex->complex) differentiable at (Cx p) /\
                  (gp:complex->complex) differentiable at (Gp(Cx p)) /\
                  (Gp:complex->complex) differentiable at (Cx p)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
       [EXISTS_TAC `tm:complex->bool`; EXISTS_TAC `up:complex->bool`;
        EXISTS_TAC `tp:complex->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Gm:complex->complex`; `gp:complex->complex`; `Cx p`]
           MOI_PDG_DET_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`Gp:complex->complex`; `gp:complex->complex`; `tp:complex->bool`;
                   `Cx p`] MOI_PDG_DET_INV) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `ia = det(jacobian (gp:complex->complex) (at (Gp(Cx p))))` THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ia = inv(det(jacobian (Gp:complex->complex) (at (Cx p))))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `ia * det(jacobian (Gp:complex->complex) (at (Cx p))) = &1` THEN
      UNDISCH_TAC `&0 < det(jacobian (Gp:complex->complex) (at (Cx p)))` THEN
      CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_LT_INV]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx p,d1) /\
                    Im((gp:complex->complex)((Gm:complex->complex) x)) = &0
                    ==> Im x = &0` ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `x IN tm /\ x IN tp /\ (Gm:complex->complex) x IN up /\
                  (gp:complex->complex)(Gm x) IN tm /\ gp(Gm x) IN tp`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `y = (gp:complex->complex)((Gm:complex->complex) x)` THEN
    SUBGOAL_THEN `y = Cx(Re y)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
    SUBGOAL_THEN `(Gp:complex->complex) y = (Gm:complex->complex) x` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(Gm:complex->complex) y = Gp y` ASSUME_TAC THENL
     [USE_THEN "axis" (MP_TAC o SPEC `Re(y:complex)`) THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
      SUBGOAL_THEN `Cx(Re y) = y` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      UNDISCH_TAC `tp SUBSET ball(Cx p,r)` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `x:complex = y` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `(gm:complex->complex)((Gm:complex->complex) x) = x /\ gm(Gm y) = y`
    MP_TAC THENL [ASM_SIMP_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(gp:complex->complex) o (Gm:complex->complex)`; `A:complex->complex`;
                 `p:real`; `d1:real`] MOI_PDG_SIDE_DOWN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `N0:complex->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `N1:complex->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `(gp:complex->complex)((Gm:complex->complex)(Cx p)) = Cx p`
      SUBST1_TAC THENL [ASM_SIMP_TAC[]; REWRITE_TAC[IM_CX]];
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `Im(x:complex) = &0` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!z. z IN ball(Cx p,d1) /\ Im z < &0
                    ==> Im((gp:complex->complex)((Gm:complex->complex) z)) < &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o check (fun th ->
      can (find_term (fun t -> t = `A:complex->complex`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`Im((A:complex->complex) ii)`;
                  `Im((gp:complex->complex)((Gm:complex->complex) z))`] REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min d1 r` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:complex`; `y:complex`] THEN
  REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `(x:complex) IN ball(Cx p,d1) /\ (y:complex) IN ball(Cx p,d1)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:complex) IN tp /\ x IN tm /\ (y:complex) IN tp /\ y IN tm /\
                (Gm:complex->complex) x IN up /\ Gm y IN up` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= Im(x:complex)` THEN ASM_CASES_TAC `&0 <= Im(y:complex)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(gp:complex->complex)((Gp:complex->complex) x) = x /\ gp(Gp y) = y`
    MP_TAC THENL [ASM_SIMP_TAC[]; ASM_MESON_TAC[]];
    SUBGOAL_THEN `Im((gp:complex->complex)((Gm:complex->complex) y)) < &0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `Im((gp:complex->complex)((Gm:complex->complex) x)) < &0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(gm:complex->complex)((Gm:complex->complex) x) = x /\ gm(Gm y) = y`
    MP_TAC THENL [ASM_SIMP_TAC[]; ASM_MESON_TAC[]]]);;

(* Combinatorics of the simplicial complex: carriers, faces, the two
   triangles at an edge, open relative interiors of triangles and a uniform
   separation radius around the vertices. *)

let MOI_PDG_SC_SIMPLEX = prove
 (`!L s:real^N->bool.
      simplicial_complex L /\ s IN L
      ==> ?c. FINITE c /\ ~(affine_dependent c) /\ s = convex hull c /\
              aff_dim s = &(CARD c) - &1`,
  REWRITE_TAC[simplicial_complex] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^N->bool` THEN ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
  ASM_ARITH_TAC);;

let MOI_PDG_SC_PROPS = prove
 (`!L s:real^N->bool.
      simplicial_complex L /\ s IN L ==> convex s /\ compact s /\ closed s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_PDG_SC_SIMPLEX) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  MATCH_MP_TAC COMPACT_CONVEX_HULL THEN ASM_SIMP_TAC[FINITE_IMP_COMPACT]);;

let MOI_PDG_SC_INTER_FACE = prove
 (`!L s t:real^N->bool.
      simplicial_complex L /\ s IN L /\ t IN L ==> (s INTER t) face_of s`,
  REWRITE_TAC[simplicial_complex] THEN MESON_TAC[]);;

let MOI_PDG_SC_FACE_IN = prove
 (`!L s f:real^N->bool.
      simplicial_complex L /\ s IN L /\ f face_of s ==> f IN L`,
  REWRITE_TAC[simplicial_complex] THEN MESON_TAC[]);;

let MOI_PDG_REL_FACE = prove
 (`!L s t x:real^N.
      simplicial_complex L /\ s IN L /\ t IN L /\
      x IN relative_interior s /\ x IN t
      ==> s SUBSET t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`; `t:real^N->bool`]
         MOI_PDG_SC_INTER_FACE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(s:real^N->bool) INTER t = s` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(s:real^N->bool) INTER t`; `s:real^N->bool`]
         FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]);;

let MOI_PDG_CARRIER = prove
 (`!L x:real^N.
      simplicial_complex L /\ x IN UNIONS L
      ==> ?s. s IN L /\ x IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `x:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_PDG_SC_PROPS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_PDG_SC_FACE_IN]);;

let MOI_PDG_FACE_EQ = prove
 (`!L s t:real^N->bool.
      simplicial_complex L /\ s IN L /\ t IN L /\ s SUBSET t /\
      aff_dim s = aff_dim t
      ==> s = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t:real^N->bool`; `s:real^N->bool`]
         MOI_PDG_SC_INTER_FACE) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t:real^N->bool) INTER s = s` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ASM_REWRITE_TAC[INT_LT_REFL] THEN ASM_MESON_TAC[MOI_PDG_SC_PROPS]);;

let MOI_PDG_EDGE_ENDS = prove
 (`!L e:real^N->bool.
      simplicial_complex L /\ e IN L /\ aff_dim e = &1
      ==> ?w1 w2. ~(w1 = w2) /\ e = segment[w1,w2] /\ {w1} IN L /\ {w2} IN L`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_PDG_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^N` (X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`w1:real^N`; `w2:real^N`] THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_SC_FACE_IN THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
     lhs(concl th) = `e:real^N->bool`)) THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
  MESON_TAC[CONVEX_HULL_SING; SET_RULE `{a:real^N} SUBSET {a,b} /\ {b} SUBSET {a,b}`]);;

let MOI_PDG_TRI_APEX = prove
 (`!L s (w1:real^N) w2.
      simplicial_complex L /\ s IN L /\ aff_dim s = &2 /\
      segment[w1,w2] IN L /\ ~(w1 = w2) /\ segment[w1,w2] SUBSET s
      ==> ?v. ~(v = w1) /\ ~(v = w2) /\
              ~(affine_dependent {w1,w2,v}) /\ s = convex hull {w1,w2,v}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`] MOI_PDG_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)))) THEN
  SUBGOAL_THEN `segment[w1:real^N,w2] face_of s` MP_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`; `segment[w1:real^N,w2]`]
           MOI_PDG_SC_INTER_FACE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s INTER segment[w1:real^N,w2] = segment[w1,w2]`
    (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `segment[w1:real^N,w2] SUBSET s` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) o
    check (fun th -> is_eq(concl th) && rhs(concl th) = `s:real^N->bool`)) THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `d = {w1:real^N,w2}` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(affine_dependent(d:real^N->bool))` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPEC `d:real^N->bool` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    MP_TAC(ISPEC `{w1:real^N,w2}` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `convex hull (d:real^N->bool)`)) THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(c:real^N->bool) = 3` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^N. v IN c /\ ~(v = w1) /\ ~(v = w2)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c:real^N->bool) SUBSET {w1,w2}` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:real^N->bool`; `{w1:real^N,w2}`] CARD_SUBSET) THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `v:real^N` THEN
  SUBGOAL_THEN `{w1:real^N,w2,v} = c` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    UNDISCH_TAC `(d:real^N->bool) SUBSET c` THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN MESON_TAC[];
    SUBGOAL_THEN `~(w1:real^N = v) /\ ~(w2 = v)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV]);;

let MOI_PDG_TRI_NEAR = prove
 (`!(w1:real^N) w2 v lam y1 y2.
      &0 < lam /\ lam < &1 /\ &0 <= y2 /\ abs y1 + y2 <= min lam (&1 - lam)
      ==> ((&1 - lam) % w1 + lam % w2) + y1 % (w2 - w1) + y2 % (v - w1)
          IN convex hull {w1,w2,v}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&1 - lam - y1 - y2`; `lam + y1`; `y2:real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
    VECTOR_ARITH_TAC]);;

let MOI_PDG_EDGE_TWO_TRI = prove
 (`!L e:real^N->bool.
      simplicial_complex L /\ e IN L /\ aff_dim e = &1 /\
      CARD {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = 2
      ==> ?s1 s2. s1 IN L /\ aff_dim s1 = &2 /\ e SUBSET s1 /\
                  s2 IN L /\ aff_dim s2 = &2 /\ e SUBSET s2 /\
                  ~(s1 = s2) /\ s1 INTER s2 = e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{t:real^N->bool | t IN L /\ aff_dim t = &2 /\ e SUBSET t} HAS_SIZE 2`
  MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `L:(real^N->bool)->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; SET_TAC[]];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(s1:real^N->bool) IN L /\ aff_dim s1 = &2 /\ e SUBSET s1 /\
                (s2:real^N->bool) IN L /\ aff_dim s2 = &2 /\ e SUBSET s2`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `f = (s1:real^N->bool) INTER s2` THEN
  SUBGOAL_THEN `(f:real^N->bool) face_of s1 /\ f IN L /\ e SUBSET f /\ f SUBSET s1 /\
                f SUBSET s2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_PDG_SC_INTER_FACE];
      MATCH_MP_TAC MOI_PDG_SC_FACE_IN THEN EXISTS_TAC `s1:real^N->bool` THEN
      ASM_MESON_TAC[MOI_PDG_SC_INTER_FACE];
      ASM SET_TAC[]; SET_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f:real^N->bool = s1)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(s1:real^N->bool = s2)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PDG_FACE_EQ THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(f:real^N->bool) < &2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->bool`; `s1:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[MOI_PDG_SC_PROPS];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PDG_FACE_EQ THEN
  EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`e:real^N->bool`; `f:real^N->bool`] AFF_DIM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let MOI_PDG_TRI_OPEN = prove
 (`!L s:real^N->bool.
      simplicial_complex L /\ (!t. t IN L ==> aff_dim t <= &2) /\
      s IN L /\ aff_dim s = &2
      ==> open_in (subtopology euclidean (UNIONS L)) (relative_interior s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` OPEN_IN_RELATIVE_INTERIOR) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `W0 INTER ((:real^N) DIFF UNIONS {t | t IN L /\ ~((s:real^N->bool) SUBSET t)})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; SET_TAC[]];
      ASM_MESON_TAC[MOI_PDG_SC_PROPS]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM SET_TAC[];
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
      ASM_MESON_TAC[MOI_PDG_REL_FACE]];
    REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET t` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(t:real^N->bool) = s` SUBST_ALL_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PDG_FACE_EQ THEN
      EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] AFF_DIM_SUBSET) THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[INT_LE_ANTISYM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN affine hull s` ASSUME_TAC THENL
     [ASM_MESON_TAC[HULL_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM SET_TAC[]]);;

let MOI_PDG_DELTA = prove
 (`!L:(real^N->bool)->bool.
      simplicial_complex L
      ==> ?delta. &0 < delta /\
                  (!w w'. {w} IN L /\ {w'} IN L /\ ~(w = w')
                          ==> &2 * delta <= dist(w,w')) /\
                  (!w t x. {w} IN L /\ t IN L /\ ~(w IN t) /\ x IN t
                           ==> delta <= dist(w,x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {w:real^N | {w} IN L}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\w:real^N. {w}`; `L:(real^N->bool)->bool`] FINITE_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[SET_RULE `{x:real^N} = {y} <=> x = y`];
    ALL_TAC] THEN
  ABBREV_TAC `VV = {w:real^N | {w} IN L}` THEN
  MP_TAC(ISPECL [`\p:real^N#real^N. dist(FST p,SND p)`;
                 `{p:real^N#real^N | FST p IN VV /\ SND p IN VV /\ ~(FST p = SND p)}`]
         MOI_PDG_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(VV:real^N->bool) CROSS VV` THEN
      ASM_SIMP_TAC[FINITE_CROSS] THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS] THEN MESON_TAC[];
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN BETA_TAC THEN
      REWRITE_TAC[FST; SND; GSYM DIST_NZ] THEN MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\p:real^N#(real^N->bool). setdist({FST p},SND p)`;
                 `{p:real^N#(real^N->bool) | FST p IN VV /\ SND p IN L /\
                                             ~(SND p = {}) /\ ~(FST p IN SND p)}`]
         MOI_PDG_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `(VV:real^N->bool) CROSS (L:(real^N->bool)->bool)` THEN
      ASM_SIMP_TAC[FINITE_CROSS] THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_CROSS] THEN MESON_TAC[];
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN BETA_TAC THEN
      MAP_EVERY X_GEN_TAC [`w:real^N`; `t:real^N->bool`] THEN REWRITE_TAC[FST; SND] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN
      REWRITE_TAC[SETDIST_POS_LE] THEN
      MP_TAC(ISPECL [`{w:real^N}`; `t:real^N->bool`] SETDIST_EQ_0_COMPACT_CLOSED) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[COMPACT_SING] THEN ASM_MESON_TAC[MOI_PDG_SC_PROPS]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2 / &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`w:real^N`; `w':real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(w:real^N,w':real^N)` o check (fun th ->
      can (find_term (fun t -> t = `d1:real`)) (concl th) && is_forall (concl th))) THEN
    REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`w:real^N`; `t:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(w:real^N,t:real^N->bool)` o check (fun th ->
      can (find_term (fun t -> t = `d2:real`)) (concl th) && is_forall (concl th))) THEN
    REWRITE_TAC[FST; SND] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`{w:real^N}`; `t:real^N->bool`; `w:real^N`; `x:real^N`]
           SETDIST_LE_DIST) THEN
    ASM_REWRITE_TAC[IN_SING] THEN ASM_REAL_ARITH_TAC]);;

(* The vertex family, the vertex-smoothed map M (moi_pdg_mmap) and the
   proof that M is a homeomorphism (local homeomorphism plus D5). *)

let MOI_PDG_X_PROPS = prove
 (`!(X:real^N->bool) (h:real^N->real^3) h'.
      homeomorphism (X,sphere(vec 0,&1)) (h,h')
      ==> compact X /\ connected X /\ locally path_connected X /\ ~(X = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(X:real^N->bool) homeomorphic sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[homeomorphic]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE];
    ASM_MESON_TAC[HOMEOMORPHIC_CONNECTEDNESS; CONNECTED_SPHERE; DIMINDEX_3;
                  ARITH_RULE `2 <= 3`];
    ASM_MESON_TAC[HOMEOMORPHIC_LOCAL_PATH_CONNECTEDNESS;
                  LOCALLY_PATH_CONNECTED_SPHERE];
    DISCH_TAC THEN
    UNDISCH_TAC `homeomorphism (X,sphere(vec 0,&1)) (h:real^N->real^3,h')` THEN
    ASM_REWRITE_TAC[homeomorphism; IMAGE_CLAUSES] THEN
    REWRITE_TAC[SET_RULE `({}:real^3->bool) = s <=> s = {}`; SPHERE_EQ_EMPTY] THEN
    REAL_ARITH_TAC]);;

let moi_pdg_vfam = new_definition
 `moi_pdg_vfam (L:(real^N->bool)->bool)
               (sigma:((real^N->bool)#(real^N->real^2))->bool)
               (h:real^N->real^3) (delta:real)
               (U:real^N->real^N->bool) (phi:real^N->real^N->real^2)
               (rho:real^N->real) (R1:real^N->real) (f:real^N->real^3->real^3)
               (V:real^N->complex->complex)
               (uedge:real^N->(real^N->bool)->complex)
               (uart:real^N->(real^N->bool)->complex) <=>
    !w. {w} IN L
        ==> moi_pdg_vp L sigma h w delta (U w) (phi w) (rho w) (R1 w) (f w) (V w)
                       (uedge w) (uart w)`;;

let moi_pdg_mmap = new_definition
 `moi_pdg_mmap (L:(real^N->bool)->bool) (U:real^N->real^N->bool)
               (phi:real^N->real^N->real^2) (rho:real^N->real)
               (f:real^N->real^3->real^3) (V:real^N->complex->complex)
               (h:real^N->real^3) (x:real^N) =
    if ?w. {w} IN L /\ x IN U w /\ norm(phi w x) < rho w
    then moi_pdg_sti (f (@w. {w} IN L /\ x IN U w /\ norm(phi w x) < rho w))
                     (V (@w. {w} IN L /\ x IN U w /\ norm(phi w x) < rho w)
                        (phi (@w. {w} IN L /\ x IN U w /\ norm(phi w x) < rho w) x))
    else h x`;;

let moi_pdg_setting = new_definition
 `moi_pdg_setting (L:(real^N->bool)->bool)
                  (sigma:((real^N->bool)#(real^N->real^2))->bool)
                  (h:real^N->real^3) (h':real^3->real^N) (delta:real)
                  (U:real^N->real^N->bool) (phi:real^N->real^N->real^2)
                  (rho:real^N->real) (R1:real^N->real) (f:real^N->real^3->real^3)
                  (V:real^N->complex->complex)
                  (uedge:real^N->(real^N->bool)->complex)
                  (uart:real^N->(real^N->bool)->complex) <=>
    simplicial_complex L /\
    smooth_manifold_atlas (subtopology euclidean (UNIONS L)) sigma /\
    homeomorphism (UNIONS L,sphere(vec 0,&1)) (h,h') /\
    moi_smo_conical_pd L sigma h /\ &0 < delta /\
    (!t. t IN L ==> aff_dim t <= &2) /\
    (!e. e IN L /\ aff_dim e = &1
         ==> CARD {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = 2) /\
    (!w w'. {w} IN L /\ {w'} IN L /\ ~(w = w') ==> &2 * delta <= dist(w,w')) /\
    (!w t x. {w} IN L /\ t IN L /\ ~(w IN t) /\ x IN t ==> delta <= dist(w,x)) /\
    moi_pdg_vfam L sigma h delta U phi rho R1 f V uedge uart`;;


let MOI_PDG_VP_DISC = prove
 (`!L sigma (h:real^N->real^3) w delta U phi rho R1 f V uedge uart x.
      smooth_manifold_atlas (subtopology euclidean (UNIONS L)) sigma /\
      moi_pdg_vp L sigma h w delta U phi rho R1 f V uedge uart /\
      x IN U /\ norm(phi x) <= rho
      ==> x IN ball(w,delta) /\ x IN UNIONS L /\ chart_inv(U,phi) (phi x) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `chart_inv(U,phi) ((phi:real^N->real^2) x) = x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `chart_inv(U,phi) ((phi:real^N->real^2) x) = x`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `delta:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[IN_CBALL_0];
    ASM_MESON_TAC[MOI_PDG_ATLAS_SUBSET; SUBSET]]);;

let MOI_PDG_DISC_UNIQUE = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w w' x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      {w} IN L /\ x IN U w /\ norm(phi w x) < rho w /\
      {w'} IN L /\ x IN U w' /\ norm(phi w' x) < rho w'
      ==> w = w'`,
  REWRITE_TAC[moi_pdg_setting; moi_pdg_vfam] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `w:real^N`; `delta:real`; `(U:real^N->real^N->bool) w`;
                 `(phi:real^N->real^N->real^2) w`; `(rho:real^N->real) w`;
                 `(R1:real^N->real) w`; `(f:real^N->real^3->real^3) w`;
                 `(V:real^N->complex->complex) w`;
                 `(uedge:real^N->(real^N->bool)->complex) w`;
                 `(uart:real^N->(real^N->bool)->complex) w`; `x:real^N`] MOI_PDG_VP_DISC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `w':real^N`; `delta:real`; `(U:real^N->real^N->bool) w'`;
                 `(phi:real^N->real^N->real^2) w'`; `(rho:real^N->real) w'`;
                 `(R1:real^N->real) w'`; `(f:real^N->real^3->real^3) w'`;
                 `(V:real^N->complex->complex) w'`;
                 `(uedge:real^N->(real^N->bool)->complex) w'`;
                 `(uart:real^N->(real^N->bool)->complex) w'`; `x:real^N`] MOI_PDG_VP_DISC) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_BALL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `w':real^N`] o check (fun th ->
    can (find_term (fun t -> t = `dist:real^N#real^N->real`)) (concl th) &&
    is_forall (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`w:real^N`; `x:real^N`; `w':real^N`] DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`x:real^N`; `w':real^N`] DIST_SYM) THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_MMAP_DISC = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      {w} IN L /\ x IN U w /\ norm(phi w x) < rho w
      ==> moi_pdg_mmap L U phi rho f V h x = moi_pdg_sti (f w) (V w (phi w x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_mmap] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  SUBGOAL_THEN `(@w. {w} IN L /\ (x:real^N) IN (U:real^N->real^N->bool) w /\
                     norm((phi:real^N->real^N->real^2) w x) < (rho:real^N->real) w) = w`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `w'':real^N` THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_DISC_UNIQUE THEN
    MAP_EVERY EXISTS_TAC
     [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
      `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
      `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
      `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
      `uedge:real^N->(real^N->bool)->complex`; `uart:real^N->(real^N->bool)->complex`;
      `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_SETTING_VP = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ {w} IN L
      ==> moi_pdg_vp L sigma h w delta (U w) (phi w) (rho w) (R1 w) (f w) (V w)
                     (uedge w) (uart w)`,
  REWRITE_TAC[moi_pdg_setting; moi_pdg_vfam] THEN MESON_TAC[]);;

let MOI_PDG_SETTING_H = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ x IN UNIONS L
      ==> h x IN sphere(vec 0,&1)`,
  REWRITE_TAC[moi_pdg_setting; homeomorphism] THEN SET_TAC[]);;

let MOI_PDG_MMAP_OUTER = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      x IN UNIONS L /\
      (!w. {w} IN L /\ x IN U w ==> rho w / &2 <= norm(phi w x))
      ==> moi_pdg_mmap L U phi rho f V h x = h x`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?w. {w} IN L /\ (x:real^N) IN (U:real^N->real^N->bool) w /\
                     norm((phi:real^N->real^N->real^2) w x) < (rho:real^N->real) w`
  THENL [ALL_TAC; REWRITE_TAC[moi_pdg_mmap] THEN ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`; `x:real^N`]
         MOI_PDG_MMAP_DISC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `x:real^N`]
         MOI_PDG_SETTING_H) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (subtopology euclidean (UNIONS L:real^N->bool))
                  (sigma:((real^N->bool)#(real^N->real^2))->bool)`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_pdg_setting]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `w:real^N`; `delta:real`; `(U:real^N->real^N->bool) w`;
                 `(phi:real^N->real^N->real^2) w`; `(rho:real^N->real) w`;
                 `(R1:real^N->real) w`; `(f:real^N->real^3->real^3) w`;
                 `(V:real^N->complex->complex) w`;
                 `(uedge:real^N->(real^N->bool)->complex) w`;
                 `(uart:real^N->(real^N->bool)->complex) w`; `x:real^N`] MOI_PDG_VP_DISC) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_pdg_vp]) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi:real^N->real^N->real^2) w x` o check (fun th ->
    can (find_term (fun t -> t = `moi_pdg_st`)) (concl th) && is_forall (concl th))) THEN
  ASM_SIMP_TAC[IN_CBALL_0; REAL_LT_IMP_LE] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_PDG_STI_ST THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_MMAP_SPHERE = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart
      ==> IMAGE (moi_pdg_mmap L U phi rho f V h) (UNIONS L) SUBSET sphere(vec 0,&1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `?w. {w} IN L /\ (x:real^N) IN (U:real^N->real^N->bool) w /\
                     norm((phi:real^N->real^N->real^2) w x) < (rho:real^N->real) w`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                   `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                   `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `w:real^N`; `x:real^N`]
           MOI_PDG_MMAP_DISC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                   `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                   `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
           MOI_PDG_SETTING_VP) THEN
    ASM_REWRITE_TAC[moi_pdg_vp] THEN MESON_TAC[MOI_PDG_STI_SPHERE];
    REWRITE_TAC[moi_pdg_mmap] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_PDG_SETTING_H]]);;

let MOI_PDG_UNIT_ROT = prove
 (`!v y:complex. norm v = &1 ==> v * (cnj v * y) = y /\ cnj v * (v * y) = y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[COMPLEX_MUL_ASSOC; COMPLEX_MUL_CNJ] THEN
  ASM_REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_MUL_LID]);;

let MOI_PDG_SMOOTH_LOCAL_INJ = prove
 (`!(G:complex->complex) s z.
      open s /\ z IN s /\ smooth_map_on s G /\ &0 < det(jacobian G (at z))
      ==> ?W. open W /\ z IN W /\ W SUBSET s /\
              !y1 y2. y1 IN W /\ y2 IN W /\ G y1 = G y2 ==> y1 = y2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:complex->complex`; `s:complex->bool`; `z:complex`]
         SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[GSYM jacobian; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:complex->bool` (X_CHOOSE_THEN `u:complex->bool`
    (X_CHOOSE_THEN `g:complex->complex`
      (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on])))) THEN
  EXISTS_TAC `t:complex->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_PDG_RAY_LOCAL_INJ = prove
 (`!(V:complex->complex) rho v t r1 g1 r2 g2.
      norm v = &1 /\ &0 < t /\
      &0 < r1 /\ smooth_map_on (ball(Cx t,r1)) g1 /\
      (!x. x IN ball(Cx t,r1) ==> v * x IN ball(vec 0,rho)) /\
      (!x. x IN ball(Cx t,r1) /\ &0 <= Im x ==> g1 x = V(v * x)) /\
      (!x. x IN ball(Cx t,r1) ==> &0 < det(jacobian g1 (at x))) /\
      &0 < r2 /\ smooth_map_on (ball(Cx t,r2)) g2 /\
      (!x. x IN ball(Cx t,r2) /\ Im x <= &0 ==> g2 x = V(v * x)) /\
      (!x. x IN ball(Cx t,r2) ==> &0 < det(jacobian g2 (at x)))
      ==> ?W. open W /\ Cx t * v IN W /\ W SUBSET ball(vec 0,rho) /\
              !y1 y2. y1 IN W /\ y2 IN W /\ V y1 = V y2 ==> y1 = y2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g1:complex->complex`; `g2:complex->complex`; `t:real`; `min r1 r2`]
         MOI_PDG_CREASE_INJ) THEN
  SUBGOAL_THEN `ball(Cx t,min r1 r2) SUBSET ball(Cx t,r1) /\
                ball(Cx t,min r1 r2) SUBSET ball(Cx t,r2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r1)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r2)` THEN
      ASM_REWRITE_TAC[];
      ASM SET_TAC[];
      X_GEN_TAC `s:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(g1:complex->complex)(Cx s) = V(v * Cx s) /\
                    (g2:complex->complex)(Cx s) = V(v * Cx s)`
      (fun th -> REWRITE_TAC[th]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IM_CX; REAL_LE_REFL] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t,d)
                    ==> (if &0 <= Im x then (g1:complex->complex) x else g2 x) =
                        V(v * x)` ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN ball(Cx t,r1) /\ x IN ball(Cx t,r2)` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `ball(Cx t,d) SUBSET ball(Cx t,min r1 r2)` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[REAL_NOT_LE; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  EXISTS_TAC `{y:complex | cnj v * y IN ball(Cx t,d)}` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN REWRITE_TAC[OPEN_BALL] THEN
    GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
    REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
    REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `cnj v * (Cx t * v) = Cx t` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[COMPLEX_RING `cnj v * (Cx t * v) = Cx t * (cnj v * v)`] THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_CNJ; COMPLEX_POW_ONE; COMPLEX_MUL_RID];
      ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `y = v * (cnj v * y)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[MOI_PDG_UNIT_ROT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `rho:real`)) (concl th) && is_forall (concl th))) THEN
    SUBGOAL_THEN `ball(Cx t,d) SUBSET ball(Cx t,min r1 r2)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`y1:complex`; `y2:complex`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `cnj v * y1 = cnj v * (y2:complex)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `d:real`)) (concl th) && is_forall (concl th) &&
        length(fst(strip_forall(concl th))) = 2)) THEN
      ASM_SIMP_TAC[MOI_PDG_UNIT_ROT];
      DISCH_THEN(MP_TAC o AP_TERM `\z:complex. v * z`) THEN
      ASM_SIMP_TAC[MOI_PDG_UNIT_ROT]]]);;

let MOI_PDG_VP_ONE_SIDED = prove
 (`!L sigma (h:real^N->real^3) w delta U phi rho R1 f V uedge uart v t.
      moi_pdg_vp L sigma h w delta U phi rho R1 f V uedge uart /\
      ((?e. e IN L /\ aff_dim e = &1 /\ w IN e /\ v = uedge e) \/
       (?s. s IN L /\ aff_dim s = &2 /\ w IN s /\ v = uart s)) /\
      &0 < t /\ t < rho
      ==> norm v = &1 /\
          (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:complex->complex) /\
                 (!x. x IN ball(Cx t,r) ==> v * x IN ball(vec 0,rho)) /\
                 (!x. x IN ball(Cx t,r) /\ &0 <= Im x ==> g x = V(v * x)) /\
                 (!x. x IN ball(Cx t,r) ==> &0 < det(jacobian g (at x)))) /\
          (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:complex->complex) /\
                 (!x. x IN ball(Cx t,r) ==> v * x IN ball(vec 0,rho)) /\
                 (!x. x IN ball(Cx t,r) /\ Im x <= &0 ==> g x = V(v * x)) /\
                 (!x. x IN ball(Cx t,r) ==> &0 < det(jacobian g (at x))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_vp] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_VP_LOCAL_INJ = prove
 (`!L sigma (h:real^N->real^3) w delta U phi rho R1 f V uedge uart z.
      moi_pdg_vp L sigma h w delta U phi rho R1 f V uedge uart /\ z IN ball(vec 0,rho)
      ==> ?W. open W /\ z IN W /\ W SUBSET ball(vec 0,rho) /\
              !y1 y2. y1 IN W /\ y2 IN W /\ V y1 = V y2 ==> y1 = y2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC
   `(?e t. e IN L /\ aff_dim e = &1 /\ w IN e /\ &0 < t /\ z = Cx t * uedge e) \/
    (?s t. s IN L /\ aff_dim s = &2 /\ w IN s /\ &0 < t /\
           z = Cx t * (uart:(real^N->bool)->complex) s)`
  THENL
   [SUBGOAL_THEN
     `?v t. ((?e. e IN L /\ aff_dim e = &1 /\ w IN e /\ v = uedge e) \/
             (?s. s IN L /\ aff_dim s = &2 /\ w IN s /\
                  v = (uart:(real^N->bool)->complex) s)) /\
            &0 < t /\ z = Cx t * v`
    (X_CHOOSE_THEN `v:complex` (X_CHOOSE_THEN `t:real`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq (concl th) &&
      lhs(concl th) = `z:complex`)) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `w:real^N`; `delta:real`; `U:real^N->bool`;
                   `phi:real^N->real^2`; `rho:real`; `R1:real`; `f:real^3->real^3`;
                   `V:complex->complex`; `uedge:(real^N->bool)->complex`;
                   `uart:(real^N->bool)->complex`; `v:complex`; `t:real`]
           MOI_PDG_VP_ONE_SIDED) THEN
    SUBGOAL_THEN `norm(v:complex) = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_pdg_vp L sigma (h:real^N->real^3) w delta U phi rho R1 f V uedge uart` THEN
      REWRITE_TAC[moi_pdg_vp] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `t < rho` ASSUME_TAC THENL
     [UNDISCH_TAC `Cx t * v IN ball(vec 0,rho)` THEN
      ASM_REWRITE_TAC[IN_BALL_0; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `g1:complex->complex` STRIP_ASSUME_TAC))
      (X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `g2:complex->complex` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC MOI_PDG_RAY_LOCAL_INJ THEN
    MAP_EVERY EXISTS_TAC [`r1:real`; `g1:complex->complex`; `r2:real`; `g2:complex->complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_pdg_vp L sigma (h:real^N->real^3) w delta U phi rho R1 f V uedge uart` THEN
  REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(z:complex) IN u0` THENL
   [MP_TAC(ISPECL [`V:complex->complex`; `u0 INTER ball(vec 0:complex,rho)`; `z:complex`]
           MOI_PDG_SMOOTH_LOCAL_INJ) THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u0:complex->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      MESON_TAC[SUBSET_INTER]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o check (fun th ->
    can (find_term (fun t -> t = `uart:(real^N->bool)->complex`)) (concl th) &&
    can (find_term (fun t -> t = `uedge:(real^N->bool)->complex`)) (concl th) &&
    is_forall (concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((vec 0:complex) IN u0)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term (fun t -> t = `R1:real`)) (concl th) &&
        can (find_term (fun t -> t = `u0:complex->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_LT_IMP_LE];
      FIRST_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
        is_disj (rand (concl th)))) THEN
      REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN MESON_TAC[];
      FIRST_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
        is_disj (rand (concl th)))) THEN
      REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`V:complex->complex`; `ball(z:complex,r)`; `z:complex`]
           MOI_PDG_SMOOTH_LOCAL_INJ) THEN
    ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:complex->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `W:complex->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:complex,r)` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_PDG_STI_HOMEO = prove
 (`!(f:real^3->real^3) u.
      orthogonal_transformation f /\ open u
      ==> homeomorphism (u,IMAGE (moi_pdg_sti f) u) (moi_pdg_sti f,moi_pdg_st f) /\
          open_in (subtopology euclidean (sphere(vec 0,&1))) (IMAGE (moi_pdg_sti f) u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  ABBREV_TAC `S = {p | ~(((f:real^3->real^3) p)$3 = &1)}` THEN
  SUBGOAL_THEN `open(S:real^3->bool) /\ smooth_map_on S (moi_pdg_st (f:real^3->real^3))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[MOI_PDG_ST_OPEN; MOI_PDG_ST_SMOOTH]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[MOI_PDG_ST_STI] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
      MATCH_MP_TAC MOI_PDG_STI_SMOOTH THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[MOI_PDG_ST_STI];
      REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_SIMP_TAC[MOI_PDG_ST_STI] THEN
      REWRITE_TAC[IMAGE_ID];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `S:real^3->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN EXPAND_TAC "S" THEN
      ASM_SIMP_TAC[IN_ELIM_THM; MOI_PDG_STI_SPHERE]];
    SUBGOAL_THEN
     `IMAGE (moi_pdg_sti (f:real^3->real^3)) u =
      sphere(vec 0,&1) INTER {p | p IN S /\ moi_pdg_st f p IN u}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `p:real^3` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `w:real^2` STRIP_ASSUME_TAC) THEN
        ASM_SIMP_TAC[MOI_PDG_STI_SPHERE; MOI_PDG_ST_STI] THEN
        EXPAND_TAC "S" THEN ASM_SIMP_TAC[IN_ELIM_THM; MOI_PDG_STI_SPHERE];
        STRIP_TAC THEN EXISTS_TAC `moi_pdg_st (f:real^3->real^3) p` THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MOI_PDG_STI_ST THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(p:real^3) IN S` THEN EXPAND_TAC "S" THEN
        REWRITE_TAC[IN_ELIM_THM]];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; ETA_AX]]]);;

let MOI_PDG_LOCAL_HOMEO_CHART = prove
 (`!(X:real^N->bool) sigma U phi (M:real^N->real^3) (f:real^3->real^3)
    (G:real^2->real^2) t x.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (U,phi) IN sigma /\
      orthogonal_transformation f /\ open t /\ t SUBSET IMAGE phi U /\
      x IN U /\ phi x IN t /\
      G continuous_on t /\ (!y1 y2. y1 IN t /\ y2 IN t /\ G y1 = G y2 ==> y1 = y2) /\
      (!z. z IN U /\ phi z IN t ==> M z = moi_pdg_sti f (G(phi z)))
      ==> ?A B g. x IN A /\ open_in (subtopology euclidean X) A /\
                  open_in (subtopology euclidean (sphere(vec 0,&1))) B /\
                  homeomorphism (A,B) (M,g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^2->real^2`; `t:real^2->bool`]
         INVARIANCE_OF_DOMAIN_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_TAC `Gi:real^2->real^2`) THEN
  SUBGOAL_THEN `open(IMAGE (G:real^2->real^2) t)` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `IMAGE (G:real^2->real^2) t`] MOI_PDG_STI_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] MOI_PDG_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `homeomorphism ({z | z IN U /\ (phi:real^N->real^2) z IN t},t)
                  (phi,chart_inv (U,phi))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `IMAGE (phi:real^N->real^2) U`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `{z | z IN U /\ (phi:real^N->real^2) z IN t}` THEN
  EXISTS_TAC `IMAGE (moi_pdg_sti (f:real^3->real^3)) (IMAGE (G:real^2->real^2) t)` THEN
  EXISTS_TAC `chart_inv (U:real^N->bool,phi:real^N->real^2) o (Gi:real^2->real^2) o
              moi_pdg_st (f:real^3->real^3)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM];
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `U:real^N->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `homeomorphism (U,IMAGE (phi:real^N->real^2) U) (phi,chart_inv (U,phi))` THEN
      SIMP_TAC[homeomorphism];
      MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `U:real^N->bool`; `phi:real^N->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[]];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`moi_pdg_sti (f:real^3->real^3) o (G:real^2->real^2) o (phi:real^N->real^2)`;
      `(chart_inv (U:real^N->bool,phi:real^N->real^2) o (Gi:real^2->real^2)) o
       moi_pdg_st (f:real^3->real^3)`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `IMAGE (G:real^2->real^2) t` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
      EXISTS_TAC `t:real^2->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM; IN_ELIM_THM] THEN ASM_SIMP_TAC[]]]);;

let MOI_PDG_INNER_DISC_COMPACT = prove
 (`!(X:real^N->bool) sigma U (phi:real^N->real^2) r.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (U,phi) IN sigma /\
      cball(vec 0,r) SUBSET IMAGE phi U
      ==> compact {y | y IN U /\ norm(phi y) <= r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] MOI_PDG_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{y | y IN U /\ norm((phi:real^N->real^2) y) <= r} =
                IMAGE (chart_inv(U,phi)) (cball(vec 0,r))` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_CBALL_0] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `(phi:real^N->real^2) y` THEN ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(z:real^2) IN IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
       [UNDISCH_TAC `cball(vec 0:real^2,r) SUBSET IMAGE (phi:real^N->real^2) U` THEN
        REWRITE_TAC[SUBSET; IN_CBALL_0] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_CBALL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (phi:real^N->real^2) U` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_PDG_VERTEX_FINITE = prove
 (`!L:(real^N->bool)->bool. simplicial_complex L ==> FINITE {w | {w} IN L}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\w:real^N. {w}`; `L:(real^N->bool)->bool`] FINITE_IMAGE_INJ) THEN
  REWRITE_TAC[SET_RULE `{x:real^N} = {y} <=> x = y`] THEN
  ASM_MESON_TAC[simplicial_complex]);;

let MOI_PDG_MMAP_LOCAL_HOMEO = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ x IN UNIONS L
      ==> ?A B g. x IN A /\ open_in (subtopology euclidean (UNIONS L)) A /\
                  open_in (subtopology euclidean (sphere(vec 0,&1))) B /\
                  homeomorphism (A,B) (moi_pdg_mmap L U phi rho f V h,g)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  ASM_CASES_TAC `?w. {w} IN L /\ (x:real^N) IN (U:real^N->real^N->bool) w /\
                     norm((phi:real^N->real^N->real^2) w x) < (rho:real^N->real) w`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                   `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                   `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
           MOI_PDG_SETTING_VP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `w:real^N`; `delta:real`; `(U:real^N->real^N->bool) w`;
                   `(phi:real^N->real^N->real^2) w`; `(rho:real^N->real) w`;
                   `(R1:real^N->real) w`; `(f:real^N->real^3->real^3) w`;
                   `(V:real^N->complex->complex) w`;
                   `(uedge:real^N->(real^N->bool)->complex) w`;
                   `(uart:real^N->(real^N->bool)->complex) w`;
                   `(phi:real^N->real^N->real^2) w x`] MOI_PDG_VP_LOCAL_INJ) THEN
    ASM_REWRITE_TAC[IN_BALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `W:complex->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_vp]) THEN
    MATCH_MP_TAC MOI_PDG_LOCAL_HOMEO_CHART THEN
    MAP_EVERY EXISTS_TAC
     [`sigma:((real^N->bool)#(real^N->real^2))->bool`; `(U:real^N->real^N->bool) w`;
      `(phi:real^N->real^N->real^2) w`; `(f:real^N->real^3->real^3) w`;
      `(V:real^N->complex->complex) w`; `W:complex->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(vec 0:complex,rho(w:real^N))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(vec 0:complex,rho(w:real^N))` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `cball(vec 0:complex,rho(w:real^N))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:complex,rho(w:real^N))` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_PDG_MMAP_DISC THEN
      MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                            `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                            `uedge:real^N->(real^N->bool)->complex`;
                            `uart:real^N->(real^N->bool)->complex`] THEN
      ASM_REWRITE_TAC[GSYM IN_BALL_0] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `KK = UNIONS (IMAGE (\w. {y:real^N | y IN (U:real^N->real^N->bool) w /\
                                    norm((phi:real^N->real^N->real^2) w y) <=
                                    (rho:real^N->real) w / &2}) {w | {w} IN L})` THEN
  SUBGOAL_THEN `!y. y IN KK <=> ?w. {w} IN L /\ y IN (U:real^N->real^N->bool) w /\
                                 norm((phi:real^N->real^N->real^2) w y) <=
                                 (rho:real^N->real) w / &2` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `closed(KK:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[MOI_PDG_VERTEX_FINITE];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                     `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                     `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                     `uedge:real^N->(real^N->bool)->complex`;
                     `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
             MOI_PDG_SETTING_VP) THEN
      ASM_REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_PDG_INNER_DISC_COMPACT THEN REWRITE_TAC[ETA_AX] THEN
      MAP_EVERY EXISTS_TAC [`UNIONS L:real^N->bool`;
                            `sigma:((real^N->bool)#(real^N->real^2))->bool`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(vec 0:complex,rho(w:real^N))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN UNIONS L DIFF KK
                    ==> moi_pdg_mmap L U phi rho f V h y = (h:real^N->real^3) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN ASM_REWRITE_TAC[IN_DIFF; NOT_EXISTS_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_PDG_MMAP_OUTER THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^N) IN KK)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC `~(?w. {w} IN L /\ (x:real^N) IN (U:real^N->real^N->bool) w /\
                       norm((phi:real^N->real^N->real^2) w x) < (rho:real^N->real) w)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                   `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                   `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
           MOI_PDG_SETTING_VP) THEN
    ASM_REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS L)) (UNIONS L DIFF (KK:real^N->bool))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `UNIONS L DIFF (KK:real^N->bool) = UNIONS L INTER ((:real^N) DIFF KK)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS L DIFF (KK:real^N->bool)` THEN
  EXISTS_TAC `IMAGE (h:real^N->real^3) (UNIONS L DIFF KK)` THEN
  EXISTS_TAC `h':real^3->real^N` THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `UNIONS L:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_EQ THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `h':real^3->real^N`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`UNIONS L:real^N->bool`; `sphere(vec 0:real^3,&1)`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (UNIONS L,sphere(vec 0,&1)) (h:real^N->real^3,h')` THEN
    REWRITE_TAC[homeomorphism] THEN SET_TAC[]]);;

let MOI_PDG_MMAP_HOMEO = prove
 (`!(u:N->bool) L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart.
      MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT u /\
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart
      ==> ?M'. homeomorphism (UNIONS L,sphere(vec 0,&1))
                             (moi_pdg_mmap L U phi rho f V h,M')`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT]) THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`]
         MOI_PDG_X_PROPS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_pdg_setting]; ALL_TAC] THEN
  SIMP_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PDG_MMAP_SPHERE THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_PDG_MMAP_LOCAL_HOMEO THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`] THEN
    ASM_REWRITE_TAC[]]);;

(* Crease data in the vertex charts: one-sided extensions of M along the
   rays and the artificial creases. *)

let MOI_PDG_SMOOTH_LINEAR = prove
 (`!s (g:real^M->real^N). open s /\ linear g ==> smooth_map_on s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. x`; `g:real^M->real^N`]
         SMOOTH_MAP_ON_LINEAR_O) THEN
  ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX]);;

let MOI_PDG_STI_EXT = prove
 (`!(f:real^3->real^3) (g:complex->complex) B.
      orthogonal_transformation f /\ open B /\ smooth_map_on B g /\
      (!x. x IN B ==> &0 < det(jacobian g (at x)))
      ==> smooth_map_on B (moi_pdg_sti f o g) /\
          (!x v. x IN B /\ frechet_derivative (moi_pdg_sti f o g) (at x) v = vec 0
                 ==> v = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; SUBSET_UNIV; MOI_PDG_STI_SMOOTH];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:complex->complex`; `moi_pdg_sti (f:real^3->real^3)`; `x:complex`]
           MOI_PDG_DERIV_COMPOSE_INJ) THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    SUBGOAL_THEN `(g:complex->complex) differentiable at x` ASSUME_TAC THENL
     [ASM_MESON_TAC[SMOOTH_MAP_ON_DIFFERENTIABLE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH];
      MATCH_MP_TAC MOI_PDG_DET_POS_INJ THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      ASM_MESON_TAC[MOI_PDG_STI_DERIV_INJ]]]);;

let MOI_PDG_VDISC_FACTS = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w z.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ {w} IN L /\
      z IN ball(vec 0,rho w)
      ==> z IN IMAGE (phi w) (U w) /\ chart_inv (U w,phi w) z IN U w /\
          phi w (chart_inv (U w,phi w) z) = z /\
          moi_pdg_mmap L U phi rho f V h (chart_inv (U w,phi w) z) =
          moi_pdg_sti (f w) (V w z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:complex) IN IMAGE ((phi:real^N->real^N->real^2) w) (U w)` ASSUME_TAC THENL
   [UNDISCH_TAC `cball(vec 0:complex,rho(w:real^N)) SUBSET
                  IMAGE ((phi:real^N->real^N->real^2) w) ((U:real^N->real^N->bool) w)` THEN
    UNDISCH_TAC `(z:complex) IN ball(vec 0,(rho:real^N->real) w)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`] CHART_INV) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_pdg_setting]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`;
                 `chart_inv ((U:real^N->real^N->bool) w,(phi:real^N->real^N->real^2) w) z`]
         MOI_PDG_MMAP_DISC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM IN_BALL_0]);;

let MOI_PDG_VCHART_ONE_SIDED = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w v t.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ {w} IN L /\
      ((?e. e IN L /\ aff_dim e = &1 /\ w IN e /\ v = uedge w e) \/
       (?s. s IN L /\ aff_dim s = &2 /\ w IN s /\ v = uart w s)) /\
      &0 < t /\ t < rho w
      ==> (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                 (!x. x IN ball(Cx t,r) ==> vec 0 + v * x IN IMAGE (phi w) (U w)) /\
                 (!x. x IN ball(Cx t,r) /\ &0 <= Im x
                      ==> g x = moi_pdg_mmap L U phi rho f V h
                                  (chart_inv (U w,phi w) (vec 0 + v * x))) /\
                 (!x v'. x IN ball(Cx t,r) /\ &0 <= Im x /\
                         frechet_derivative g (at x) v' = vec 0 ==> v' = vec 0)) /\
          (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                 (!x. x IN ball(Cx t,r) ==> vec 0 + v * x IN IMAGE (phi w) (U w)) /\
                 (!x. x IN ball(Cx t,r) /\ Im x <= &0
                      ==> g x = moi_pdg_mmap L U phi rho f V h
                                  (chart_inv (U w,phi w) (vec 0 + v * x))) /\
                 (!x v'. x IN ball(Cx t,r) /\ Im x <= &0 /\
                         frechet_derivative g (at x) v' = vec 0 ==> v' = vec 0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `w:real^N`; `delta:real`; `(U:real^N->real^N->bool) w`;
                 `(phi:real^N->real^N->real^2) w`; `(rho:real^N->real) w`;
                 `(R1:real^N->real) w`; `(f:real^N->real^3->real^3) w`;
                 `(V:real^N->complex->complex) w`;
                 `(uedge:real^N->(real^N->bool)->complex) w`;
                 `(uart:real^N->(real^N->bool)->complex) w`; `v:complex`; `t:real`]
         MOI_PDG_VP_ONE_SIDED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `g1:complex->complex` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `g2:complex->complex` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `orthogonal_transformation((f:real^N->real^3->real^3) w)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_pdg_vp L sigma (h:real^N->real^3) w delta (U w) (phi w) (rho w) (R1 w)
                   (f w) (V w) (uedge w) (uart w)` THEN SIMP_TAC[moi_pdg_vp];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`r1:real`;
      `moi_pdg_sti ((f:real^N->real^3->real^3) w) o (g1:complex->complex)`] THEN
    MP_TAC(ISPECL [`(f:real^N->real^3->real^3) w`; `g1:complex->complex`;
                   `ball(Cx t,r1)`] MOI_PDG_STI_EXT) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[VECTOR_ADD_LID] THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                     `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                     `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                     `V:real^N->complex->complex`;
                     `uedge:real^N->(real^N->bool)->complex`;
                     `uart:real^N->(real^N->bool)->complex`; `w:real^N`; `v * x:complex`]
             MOI_PDG_VDISC_FACTS) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:complex` THEN STRIP_TAC THEN REWRITE_TAC[VECTOR_ADD_LID; o_THM] THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                     `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                     `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                     `V:real^N->complex->complex`;
                     `uedge:real^N->(real^N->bool)->complex`;
                     `uart:real^N->(real^N->bool)->complex`; `w:real^N`; `v * x:complex`]
             MOI_PDG_VDISC_FACTS) THEN
      ASM_SIMP_TAC[];
      ASM_MESON_TAC[]];
    MAP_EVERY EXISTS_TAC [`min r1 r2`;
      `moi_pdg_sti ((f:real^N->real^3->real^3) w) o (g2:complex->complex)`] THEN
    SUBGOAL_THEN `ball(Cx t,min r1 r2) SUBSET ball(Cx t,r1) /\
                  ball(Cx t,min r1 r2) SUBSET ball(Cx t,r2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`(f:real^N->real^3->real^3) w`; `g2:complex->complex`;
                   `ball(Cx t,min r1 r2)`] MOI_PDG_STI_EXT) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r2)` THEN
        ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[VECTOR_ADD_LID] THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                     `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                     `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                     `V:real^N->complex->complex`;
                     `uedge:real^N->(real^N->bool)->complex`;
                     `uart:real^N->(real^N->bool)->complex`; `w:real^N`; `v * x:complex`]
             MOI_PDG_VDISC_FACTS) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
      X_GEN_TAC `x:complex` THEN STRIP_TAC THEN REWRITE_TAC[VECTOR_ADD_LID; o_THM] THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                     `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                     `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                     `V:real^N->complex->complex`;
                     `uedge:real^N->(real^N->bool)->complex`;
                     `uart:real^N->(real^N->bool)->complex`; `w:real^N`; `v * x:complex`]
             MOI_PDG_VDISC_FACTS) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ASM_MESON_TAC[]]]);;

let MOI_PDG_ART_CREASE = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w s.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      {w} IN L /\ s IN L /\ aff_dim s = &2 /\ w IN s
      ==> moi_pdg_crease sigma (moi_pdg_mmap L U phi rho f V h) (U w) (phi w) (vec 0)
                         (uart w s) (R1 w / &2) (rho w / &2)
                         (min (R1 w / &4) ((rho w - R1 w) / &10)) /\
          (!t. R1 w / &2 <= t /\ t <= rho w / &2
               ==> chart_inv (U w,phi w) (vec 0 + uart w s * Cx t) IN relative_interior s /\
                   chart_inv (U w,phi w) (vec 0 + uart w s * Cx t) IN U w /\
                   norm(phi w (chart_inv (U w,phi w) (vec 0 + uart w s * Cx t))) < rho w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_vp]) THEN
  SUBGOAL_THEN `norm((uart:real^N->(real^N->bool)->complex) w s) = &1 /\
                (!t. &0 < t /\ t < rho w
                     ==> chart_inv ((U:real^N->real^N->bool) w,
                                    (phi:real^N->real^N->real^2) w) (Cx t * uart w s) IN
                         relative_interior s)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. norm((uart:real^N->(real^N->bool)->complex) w s * x) = norm x`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[COMPLEX_NORM_MUL; REAL_MUL_LID]; ALL_TAC] THEN
  ABBREV_TAC `ee = min ((R1:real^N->real) w / &4) (((rho:real^N->real) w - R1 w) / &10)` THEN
  SUBGOAL_THEN `&0 < ee /\ ee <= (R1:real^N->real) w / &4 /\
                ee <= ((rho:real^N->real) w - R1 w) / &10` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ee" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[VECTOR_ADD_LID] THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
    SUBGOAL_THEN `Cx t * (uart:real^N->(real^N->bool)->complex) w s IN ball(vec 0,rho w)`
    ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`;
                   `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                   `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                   `V:real^N->complex->complex`;
                   `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `w:real^N`;
                   `Cx t * (uart:real^N->(real^N->bool)->complex) w s`]
           MOI_PDG_VDISC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[IN_BALL_0]];
    DISCH_TAC] THEN
  REWRITE_TAC[moi_pdg_crease] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_PDG_VCHART_ONE_SIDED THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
    X_GEN_TAC `t:real` THEN STRIP_TAC THENL
     [ (* inner end: inside the faded zone *)
      SUBGOAL_THEN `(uart:real^N->(real^N->bool)->complex) w s * Cx t IN
                    u0 INTER ball(vec 0,(rho:real^N->real) w)` MP_TAC THENL
       [REWRITE_TAC[IN_INTER; IN_BALL_0] THEN ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          can (find_term (fun t -> t = `u0:complex->bool`)) (concl th) &&
          can (find_term (fun t -> t = `cball:complex#real->complex->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[IN_CBALL_0; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `open(u0 INTER ball(vec 0:complex,(rho:real^N->real) w))` MP_TAC THENL
       [ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL]; ALL_TAC] THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `r:real` THEN
      EXISTS_TAC `moi_pdg_sti ((f:real^N->real^3->real^3) w) o
                  (V:real^N->complex->complex) w o
                  (\x. (uart:real^N->(real^N->bool)->complex) w s * x)` THEN
      SUBGOAL_THEN `!x. x IN ball(Cx t,r)
                        ==> (uart:real^N->(real^N->bool)->complex) w s * x IN
                            u0 INTER ball(vec 0,(rho:real^N->real) w)` ASSUME_TAC THENL
       [X_GEN_TAC `x:complex` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
        UNDISCH_TAC `ball((uart:real^N->(real^N->bool)->complex) w s * Cx t,r) SUBSET
                     u0 INTER ball(vec 0,(rho:real^N->real) w)` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[dist; GSYM COMPLEX_SUB_LDISTRIB] THEN
        ASM_MESON_TAC[dist];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
        REWRITE_TAC[OPEN_BALL; OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
          EXISTS_TAC `u0 INTER ball(vec 0:complex,(rho:real^N->real) w)` THEN
          ASM_SIMP_TAC[OPEN_BALL; OPEN_INTER] THEN REPEAT CONJ_TAC THENL
           [ASM SET_TAC[];
            MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN
            REWRITE_TAC[OPEN_BALL; LINEAR_COMPLEX_MUL];
            MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u0:complex->bool` THEN
            ASM_REWRITE_TAC[INTER_SUBSET]];
          MATCH_MP_TAC MOI_PDG_STI_SMOOTH THEN REWRITE_TAC[OPEN_UNIV] THEN
          ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR]];
        X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[VECTOR_ADD_LID; o_THM] THEN
        MP_TAC(ISPECL [`L:(real^N->bool)->bool`;
                       `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                       `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                       `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                       `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                       `V:real^N->complex->complex`;
                       `uedge:real^N->(real^N->bool)->complex`;
                       `uart:real^N->(real^N->bool)->complex`; `w:real^N`;
                       `(uart:real^N->(real^N->bool)->complex) w s * x`]
               MOI_PDG_VDISC_FACTS) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
      (* outer end: smooth across the artificial ray *)
      FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `t:real`] o check (fun th ->
        can (find_term (fun t -> t = `&4`)) (concl th) &&
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> t = `uart:real^N->(real^N->bool)->complex`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `r:real` THEN
      EXISTS_TAC `moi_pdg_sti ((f:real^N->real^3->real^3) w) o
                  (\x. (V:real^N->complex->complex) w
                         ((uart:real^N->(real^N->bool)->complex) w s * x))` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[OPEN_BALL; OPEN_UNIV; SUBSET_UNIV] THEN
        MATCH_MP_TAC MOI_PDG_STI_SMOOTH THEN REWRITE_TAC[OPEN_UNIV] THEN
        ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR];
        X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[VECTOR_ADD_LID; o_THM] THEN
        MP_TAC(ISPECL [`L:(real^N->bool)->bool`;
                       `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                       `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                       `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                       `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                       `V:real^N->complex->complex`;
                       `uedge:real^N->(real^N->bool)->complex`;
                       `uart:real^N->(real^N->bool)->complex`; `w:real^N`;
                       `(uart:real^N->(real^N->bool)->complex) w s * x`]
               MOI_PDG_VDISC_FACTS) THEN
        ASM_SIMP_TAC[]]]]);;

(* One-sided extensions in an edge chart from the triangles (closure
   lemmas, the affine parametrization of a triangle, inverse along the axis). *)

let MOI_PDG_UPPER_APPROX = prove
 (`!(c:complex) r x d.
      x IN ball(c,r) /\ &0 <= Im x /\ &0 < d
      ==> ?y. y IN ball(c,r) /\ &0 < Im y /\ dist(y,x) < d`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = min d (r - dist(c:complex,x)) / &2` THEN
  SUBGOAL_THEN `&0 < s /\ s < d /\ dist(c:complex,x) + s < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `x + s % ii` THEN
  SUBGOAL_THEN `dist(x + s % ii,x) = s` ASSUME_TAC THENL
   [REWRITE_TAC[dist; VECTOR_ARITH `(x + a) - x:complex = a`; NORM_MUL; COMPLEX_NORM_II] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_BALL; IM_ADD; IM_CMUL; IM_II] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:complex`; `x:complex`; `x + s % ii`] DIST_TRIANGLE) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let MOI_PDG_HALF_CLOSURE = prove
 (`!(f:complex->real^M) g c r.
      f continuous_on ball(c,r) /\ g continuous_on ball(c,r) /\
      (!x. x IN ball(c,r) /\ &0 < Im x ==> f x = g x)
      ==> !x. x IN ball(c,r) /\ &0 <= Im x ==> f x = g x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (f:complex->real^M) y - g y) continuous at x` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THEN
    ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `norm((f:complex->real^M) x - g x)`) THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(TAUT `(~p ==> q /\ ~r) ==> (q ==> r) ==> p`) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[NORM_POS_LT; NOT_EXISTS_THM] THEN
  X_GEN_TAC `d:real` THEN REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
  ASM_CASES_TAC `&0 < d` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:complex`; `r:real`; `x:complex`; `d:real`] MOI_PDG_UPPER_APPROX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:complex` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:complex->real^M) y = g y` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; dist; VECTOR_SUB_LZERO; NORM_NEG; REAL_LT_REFL]);;

let MOI_PDG_HALF_CLOSURE_LE = prove
 (`!(f:complex->real) c r.
      (\x. lift(f x)) continuous_on ball(c,r) /\
      (!x. x IN ball(c,r) /\ &0 < Im x ==> &0 < f x)
      ==> !x. x IN ball(c,r) /\ &0 <= Im x ==> &0 <= f x`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `~(f < &0) ==> &0 <= f`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\y. lift((f:complex->real) y)) continuous at x` MP_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL]; ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `--((f:complex->real) x)`) THEN
  ASM_REWRITE_TAC[REAL_NEG_GT0; NOT_EXISTS_THM] THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:complex`; `r:real`; `x:complex`; `d:real`] MOI_PDG_UPPER_APPROX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:complex` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:complex`) THEN ASM_REWRITE_TAC[DIST_LIFT] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:complex`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let MOI_PDG_LINEAR_CXIM = prove
 (`linear (\z:complex. Cx(Im z))`,
  REWRITE_TAC[linear; IM_ADD; IM_CMUL; CX_ADD; COMPLEX_CMUL; CX_MUL]);;

let MOI_PDG_IM_AXIS_DERIV = prove
 (`!(F1:complex->complex) B t d.
      (F1 has_derivative B) (at (Cx t)) /\ &0 < d /\
      (!q. abs(q - t) < d ==> Im(F1(Cx q)) = &0)
      ==> Im(B(Cx(&1))) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(\z:complex. Cx(Im z)) o (F1:complex->complex)`; `\z:complex. Cx(&0)`;
                 `(\z:complex. Cx(Im z)) o (B:complex->complex)`; `\h:complex. vec 0:complex`;
                 `t:real`; `d:real`] MOI_PDG_AXIS_DERIV) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MOI_PDG_LINEAR_CXIM];
      REWRITE_TAC[HAS_DERIVATIVE_CONST];
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[o_THM]];
    REWRITE_TAC[o_THM; COMPLEX_VEC_0; CX_INJ]]);;

let MOI_PDG_INJ_REAL_AXIS = prove
 (`!Bi:complex->complex.
      linear Bi /\ (!z. Bi z = vec 0 ==> z = vec 0) /\ Im(Bi(Cx(&1))) = &0
      ==> ~(Im(Bi ii) = &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `Cx(Re(Bi ii)) - Cx(Re((Bi:complex->complex)(Cx(&1)))) * ii`) THEN
  MATCH_MP_TAC(TAUT `p /\ ~q ==> (p ==> q) ==> F`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `Cx(Re((Bi:complex->complex) ii)) - Cx(Re(Bi(Cx(&1)))) * ii =
                  Re(Bi ii) % Cx(&1) - Re(Bi(Cx(&1))) % ii` SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th; MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[COMPLEX_EQ; RE_SUB; IM_SUB; RE_CMUL; IM_CMUL; COMPLEX_VEC_0; RE_CX; IM_CX] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[COMPLEX_EQ; RE_SUB; IM_SUB; RE_MUL_CX; IM_MUL_CX; RE_CX; IM_CX; RE_II; IM_II;
                COMPLEX_VEC_0] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(Bi:complex->complex)(Cx(&1)) = vec 0` MP_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_EQ; COMPLEX_VEC_0; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun t ->
        is_forall (concl t)))) THEN
      REWRITE_TAC[COMPLEX_VEC_0; CX_INJ] THEN REAL_ARITH_TAC]]);;

let MOI_PDG_LEFT_INV_REAL = prove
 (`!B Bi:complex->complex.
      linear B /\ linear Bi /\ (!z. Bi(B z) = z) /\ Im(B(Cx(&1))) = &0
      ==> Im(Bi(Cx(&1))) = &0`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a = Re((B:complex->complex)(Cx(&1)))` THEN
  SUBGOAL_THEN `(B:complex->complex)(Cx(&1)) = Cx a` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
  SUBGOAL_THEN `~(a = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&1)` o check (fun th -> is_forall (concl th))) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    REWRITE_TAC[COMPLEX_VEC_0; CX_INJ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&1)` o check (fun th -> is_forall (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `Cx a = a % Cx(&1)` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[IM_CMUL; IM_CX; REAL_ENTIRE] THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_LIN_INDEP_TRI = prove
 (`!(w1:real^N) w2 v.
      ~(w1 = w2) /\ ~(v = w1) /\ ~(v = w2) /\ ~(affine_dependent {w1,w2,v})
      ==> !a b. a % (w2 - w1) + b % (v - w1) = vec 0 ==> a = &0 /\ b = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `b = &0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_EQ_0;
                                VECTOR_SUB_EQ]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(affine_dependent {w1:real^N,w2,v})` THEN
  REWRITE_TAC[affine_dependent] THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  EXISTS_TAC `v:real^N` THEN
  REWRITE_TAC[IN_INSERT] THEN
  SUBGOAL_THEN `{w1:real^N,w2,v} DELETE v = {w1,w2}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&1 + a / b`; `--(a / b)`] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^N. inv b % z`) THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; VECTOR_MUL_RZERO] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV] THEN
  REWRITE_TAC[VECTOR_MUL_LID; real_div] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN VECTOR_ARITH_TAC);;

let MOI_PDG_CNJ_BALL_REAL = prove
 (`!t r x. x IN ball(Cx t,r) ==> cnj x IN ball(Cx t,r)`,
  REWRITE_TAC[IN_BALL; dist] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx t - cnj x = cnj(Cx t - x)` SUBST1_TAC THENL
   [REWRITE_TAC[CNJ_SUB; CNJ_CX]; ASM_REWRITE_TAC[COMPLEX_NORM_CNJ]]);;

let MOI_PDG_HALF_CLOSURE_SG = prove
 (`!(f:complex->real^M) g t r sg.
      (sg = &1 \/ sg = -- &1) /\
      f continuous_on ball(Cx t,r) /\ g continuous_on ball(Cx t,r) /\
      (!x. x IN ball(Cx t,r) /\ &0 < sg * Im x ==> f x = g x)
      ==> !x. x IN ball(Cx t,r) /\ &0 <= sg * Im x ==> f x = g x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LID]) THEN
  REWRITE_TAC[REAL_MUL_LID] THENL
   [MATCH_MP_TAC MOI_PDG_HALF_CLOSURE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:complex->real^M) o cnj`; `(g:complex->real^M) o cnj`; `Cx t`; `r:real`]
         MOI_PDG_HALF_CLOSURE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_CNJ] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_PDG_CNJ_BALL_REAL];
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_CNJ] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_PDG_CNJ_BALL_REAL];
      REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[MOI_PDG_CNJ_BALL_REAL; IM_CNJ] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[o_THM] THEN DISCH_TAC THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `cnj x`) THEN
    ASM_SIMP_TAC[MOI_PDG_CNJ_BALL_REAL; IM_CNJ; CNJ_CNJ] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_HALF_CLOSURE_LE_SG = prove
 (`!(f:complex->real) t r sg.
      (sg = &1 \/ sg = -- &1) /\
      (\x. lift(f x)) continuous_on ball(Cx t,r) /\
      (!x. x IN ball(Cx t,r) /\ &0 < sg * Im x ==> &0 < f x)
      ==> !x. x IN ball(Cx t,r) /\ &0 <= sg * Im x ==> &0 <= f x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LID]) THEN
  REWRITE_TAC[REAL_MUL_LID] THENL
   [MATCH_MP_TAC MOI_PDG_HALF_CLOSURE_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(f:complex->real) o cnj`; `Cx t`; `r:real`] MOI_PDG_HALF_CLOSURE_LE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `(\x. lift(((f:complex->real) o cnj) x)) = (\x. lift(f x)) o cnj`
      SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_CNJ] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_PDG_CNJ_BALL_REAL];
      REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[MOI_PDG_CNJ_BALL_REAL; IM_CNJ] THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[o_THM] THEN DISCH_TAC THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `cnj x`) THEN
    ASM_SIMP_TAC[MOI_PDG_CNJ_BALL_REAL; IM_CNJ; CNJ_CNJ] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_TRI_PARAM = prove
 (`!(w1:real^N) w2 v lam N0.
      &0 < lam /\ lam < &1 /\ open N0 /\ (&1 - lam) % w1 + lam % w2 IN N0
      ==> ?e. &0 < e /\
              !y:complex. norm y < e
                  ==> ((&1 - lam) % w1 + lam % w2) + Re y % (w2 - w1) + Im y % (v - w1)
                      IN N0 /\
                      (&0 <= Im y
                       ==> ((&1 - lam) % w1 + lam % w2) + Re y % (w2 - w1) +
                           Im y % (v - w1) IN convex hull {w1,w2,v}) /\
                      (Im y = &0 /\ ~(w1 = w2)
                       ==> ((&1 - lam) % w1 + lam % w2) + Re y % (w2 - w1) +
                           Im y % (v - w1) IN segment(w1,w2))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `(&1 - lam) % w1 + lam % (w2:real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `K = norm(w2 - w1:real^N) + norm(v - w1:real^N) + &1` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MP_TAC(ISPEC `w2 - w1:real^N` NORM_POS_LE) THEN
    MP_TAC(ISPEC `v - w1:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (e1 / K) (min lam (&1 - lam) / &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> &0 < min a b`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(Re y) <= norm(y:complex) /\ abs(Im y) <= norm y` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_GE_RE_IM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `ball((&1 - lam) % w1 + lam % (w2:real^N),e1) SUBSET N0` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[dist; VECTOR_ARITH `x - (x + a + b):real^N = --(a + b)`; NORM_NEG] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `abs(Re y) * norm(w2 - w1:real^N) + abs(Im y) * norm(v - w1:real^N)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM NORM_MUL] THEN MATCH_ACCEPT_TAC NORM_TRIANGLE; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(y:complex) * K` THEN CONJ_TAC THENL
     [EXPAND_TAC "K" THEN REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN
      MP_TAC(SPECL [`abs(Re y)`; `norm(y:complex)`; `norm(w2 - w1:real^N)`] REAL_LE_RMUL) THEN
      MP_TAC(SPECL [`abs(Im y)`; `norm(y:complex)`; `norm(v - w1:real^N)`] REAL_LE_RMUL) THEN
      ASM_REWRITE_TAC[NORM_POS_LE] THEN MP_TAC(ISPEC `y:complex` NORM_POS_LE) THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC THEN MATCH_MP_TAC MOI_PDG_TRI_NEAR THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; IN_SEGMENT] THEN
    EXISTS_TAC `lam + Re y` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN VECTOR_ARITH_TAC]);;
let MOI_PDG_DERIV_LEFT_INV = prove
 (`!(f:real^M->real^N) (g:real^N->real^M) t x.
      open t /\ x IN t /\ (!y. y IN t ==> g(f y) = y) /\
      f differentiable at x /\ g differentiable at (f x)
      ==> !z. frechet_derivative g (at (f x)) (frechet_derivative f (at x) z) = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `frechet_derivative g (at ((f:real^M->real^N) x)) o
                frechet_derivative f (at x) = (\z:real^M. z)`
  (fun th -> X_GEN_TAC `z:real^M` THEN MP_TAC(AP_THM th `z:real^M`) THEN
             REWRITE_TAC[o_THM]) THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`(g:real^N->real^M) o (f:real^M->real^N)`; `x:real^M`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    EXISTS_TAC `\y:real^M. y` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; o_THM] THEN
    X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(x:real^M,d) SUBSET t` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]]);;

let MOI_PDG_AXIS_INVERSE = prove
 (`!(F1:complex->complex) e t.
      &0 < e /\ smooth_map_on (ball(vec 0,e)) F1 /\ F1(vec 0) = Cx t /\
      ~(det(jacobian F1 (at (vec 0))) = &0) /\
      (!q. abs q < e ==> Im(F1(Cx q)) = &0)
      ==> ?sg r G. (sg = &1 \/ sg = -- &1) /\ &0 < r /\
                   smooth_map_on (ball(Cx t,r)) G /\ G(Cx t) = vec 0 /\
                   (!x. x IN ball(Cx t,r) ==> G x IN ball(vec 0,e) /\ F1(G x) = x) /\
                   (!x. x IN ball(Cx t,r) /\ &0 < sg * Im x ==> &0 < Im(G x)) /\
                   (!x v. x IN ball(Cx t,r) /\ frechet_derivative G (at x) v = vec 0
                          ==> v = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`F1:complex->complex`; `ball(vec 0:complex,e)`; `vec 0:complex`]
         SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; GSYM jacobian]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:complex->bool` (X_CHOOSE_THEN `u1:complex->bool`
    (X_CHOOSE_THEN `G:complex->complex`
      (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on])))) THEN
  SUBGOAL_THEN `(G:complex->complex)(Cx t) = vec 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(G:complex->complex)((F1:complex->complex)(vec 0)) = vec 0` MP_TAC THENL
     [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx t IN u1` ASSUME_TAC THENL
   [UNDISCH_TAC `(F1:complex->complex)(vec 0) IN u1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(F1:complex->complex) differentiable at (vec 0) /\
                (G:complex->complex) differentiable at (Cx t)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `t1:complex->bool`; EXISTS_TAC `u1:complex->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `B = frechet_derivative (F1:complex->complex) (at (vec 0))` THEN
  ABBREV_TAC `Bi = frechet_derivative (G:complex->complex) (at (Cx t))` THEN
  SUBGOAL_THEN `linear(B:complex->complex) /\ linear(Bi:complex->complex)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN EXPAND_TAC "Bi" THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (Bi:complex->complex)(B z) = z` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`F1:complex->complex`; `G:complex->complex`; `t1:complex->bool`;
                   `vec 0:complex`] MOI_PDG_DERIV_LEFT_INV) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (B:complex->complex)(Bi z) = z` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:complex->complex`; `F1:complex->complex`; `u1:complex->bool`;
                   `Cx t`] MOI_PDG_DERIV_LEFT_INV) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Im((B:complex->complex)(Cx(&1))) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_IM_AXIS_DERIV THEN
    MAP_EVERY EXISTS_TAC [`F1:complex->complex`; `&0`; `e:real`] THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO; GSYM COMPLEX_VEC_0] THEN
    EXPAND_TAC "B" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Im((Bi:complex->complex) ii) = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_INJ_REAL_AXIS THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      MP_TAC(SPEC `z:complex` (ASSUME `!z. (B:complex->complex)(Bi z) = z`)) THEN
      UNDISCH_TAC `(Bi:complex->complex) z = vec 0` THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) o
        check (fun th -> concl th = `linear(B:complex->complex)`)) THEN
      MESON_TAC[];
      MATCH_MP_TAC MOI_PDG_LEFT_INV_REAL THEN EXISTS_TAC `B:complex->complex` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r1. &0 < r1 /\ ball(Cx t,r1) SUBSET u1` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `Cx t` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open(u1:complex->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t,r1) ==> x IN u1 /\ (G:complex->complex) x IN ball(vec 0,e)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC [`ball(Cx t,r1) SUBSET u1`; `IMAGE (G:complex->complex) u1 = t1`;
                           `t1 SUBSET ball(vec 0:complex,e)`; `(x:complex) IN ball(Cx t,r1)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t,r1) /\ ~(Im x = &0)
                    ==> ~(Im((G:complex->complex) x) = &0)` (LABEL_TAC "nonreal") THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN u1 /\ (G:complex->complex) x IN ball(vec 0,e)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(G:complex->complex) x IN ball(vec 0,e)` THEN
    SUBGOAL_THEN `(G:complex->complex) x = Cx(Re(G x))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
    REWRITE_TAC[IN_BALL_0; COMPLEX_NORM_CX] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(Im(x:complex) = &0)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `x = (F1:complex->complex)(Cx(Re((G:complex->complex) x)))` SUBST1_TAC THENL
     [SUBGOAL_THEN `Cx(Re((G:complex->complex) x)) = G x` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ASM_SIMP_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G:complex->complex) continuous_on ball(Cx t,r1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u1:complex->bool` THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
    ALL_TAC] THEN
  SUBGOAL_THEN `((G:complex->complex) has_derivative Bi) (at (Cx t))` ASSUME_TAC THENL
   [EXPAND_TAC "Bi" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:complex->complex`; `Bi:complex->complex`; `t:real`; `r1:real`]
         MOI_PDG_SIDE_UP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_VEC_0; IM_CX] THEN
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN USE_THEN "nonreal" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "up")] THEN
  MP_TAC(ISPECL [`G:complex->complex`; `Bi:complex->complex`; `t:real`; `r1:real`]
         MOI_PDG_SIDE_DOWN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_VEC_0; IM_CX] THEN
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN USE_THEN "nonreal" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "down")] THEN
  EXISTS_TAC `if &0 < Im((Bi:complex->complex) ii) then &1 else -- &1` THEN
  MAP_EVERY EXISTS_TAC [`r1:real`; `G:complex->complex`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u1:complex->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN u1 /\ (G:complex->complex) x IN ball(vec 0,e)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ASM_SIMP_TAC[]];
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 < Im((Bi:complex->complex) ii)` THENL
     [SUBGOAL_THEN `&0 < Im(x:complex)` ASSUME_TAC THENL
       [UNDISCH_TAC `&0 < (if &0 < Im((Bi:complex->complex) ii) then &1 else -- &1) *
                          Im(x:complex)` THEN
        ASM_REWRITE_TAC[REAL_MUL_LID];
        ALL_TAC] THEN
      USE_THEN "up" (MP_TAC o SPEC `x:complex`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `Im(x:complex) < &0` ASSUME_TAC THENL
       [UNDISCH_TAC `&0 < (if &0 < Im((Bi:complex->complex) ii) then &1 else -- &1) *
                          Im(x:complex)` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      USE_THEN "down" (MP_TAC o SPEC `x:complex`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `m * y < &0 ==> &0 < --m * y`)) THEN
      ONCE_REWRITE_TAC[REAL_MUL_POS_LT] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `x:complex` THEN X_GEN_TAC `v:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:complex) IN u1 /\ (G:complex->complex) x IN ball(vec 0,e)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`G:complex->complex`; `F1:complex->complex`; `u1:complex->bool`;
                   `x:complex`] MOI_PDG_DERIV_LEFT_INV) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
       [EXISTS_TAC `u1:complex->bool`; EXISTS_TAC `t1:complex->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`IMAGE (G:complex->complex) u1 = t1`; `(x:complex) IN u1`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `v:complex`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `linear(frechet_derivative (F1:complex->complex) (at (G(x:complex))))`
    (fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `t1:complex->bool` THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`IMAGE (G:complex->complex) u1 = t1`; `(x:complex) IN u1`] THEN
      SET_TAC[];
      MESON_TAC[]]]);;
let MOI_PDG_LIN_RE_IM = prove
 (`!(a:real^N) b. linear (\y:complex. Re y % a + Im y % b)`,
  REWRITE_TAC[linear; RE_ADD; IM_ADD; RE_CMUL; IM_CMUL] THEN VECTOR_ARITH_TAC);;

let MOI_PDG_AFFINE_DERIV = prove
 (`!(a:real^N) (L:complex->real^N) y.
      linear L ==> ((\y. a + L y) has_derivative L) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:complex. a:real^N`; `\h:complex. vec 0:real^N`;
                 `L:complex->real^N`; `L:complex->real^N`; `at(y:complex)`]
         HAS_DERIVATIVE_ADD) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_LINEAR] THEN
  REWRITE_TAC[VECTOR_ADD_LID; ETA_AX]);;

let MOI_PDG_AFFINE_SMOOTH = prove
 (`!(a:real^N) (L:complex->real^N) s.
      open s /\ linear L ==> smooth_map_on s (\y. a + L y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN
  ASM_SIMP_TAC[SMOOTH_MAP_ON_CONST; ETA_AX; MOI_PDG_SMOOTH_LINEAR]);;

let MOI_PDG_TRI_EXT = prove
 (`!(X:real^N->bool) sigma (M:real^N->real^3) (h:real^N->real^3) s Ue phie z0 c t
    (w1:real^N) w2 v O.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (Ue,phie) IN sigma /\
      ~(w1 = w2) /\ ~(v = w1) /\ ~(v = w2) /\ ~(affine_dependent {w1,w2,v}) /\
      s = convex hull {w1,w2,v} /\ moi_smo_cell_smooth s h /\ h continuous_on X /\
      s SUBSET X /\ norm c = &1 /\
      (!y. y IN segment(w1,w2) ==> y IN Ue /\ ?q. phie y = z0 + c * Cx q) /\
      z0 + c * Cx t IN IMAGE phie Ue /\
      chart_inv(Ue,phie)(z0 + c * Cx t) IN segment(w1,w2) /\
      (?r. &0 < r /\ s INTER cball(chart_inv(Ue,phie)(z0 + c * Cx t),r) SUBSET Ue /\
           moi_smo_cell_smooth (s INTER cball(chart_inv(Ue,phie)(z0 + c * Cx t),r)) phie) /\
      open_in (subtopology euclidean X) O /\ chart_inv(Ue,phie)(z0 + c * Cx t) IN O /\
      (!y. y IN O ==> M y = h y)
      ==> ?sg r g. (sg = &1 \/ sg = -- &1) /\ &0 < r /\
                   smooth_map_on (ball(Cx t,r)) (g:complex->real^3) /\
                   (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phie Ue) /\
                   (!x. x IN ball(Cx t,r) /\ &0 < sg * Im x
                        ==> chart_inv(Ue,phie)(z0 + c * x) IN s) /\
                   (!x. x IN ball(Cx t,r) /\ &0 <= sg * Im x
                        ==> g x = M(chart_inv(Ue,phie)(z0 + c * x))) /\
                   (!x v'. x IN ball(Cx t,r) /\ &0 <= sg * Im x /\
                           frechet_derivative g (at x) v' = vec 0 ==> v' = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `s:real^N->bool`)) THEN
  ABBREV_TAC `x0 = chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx t)` THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `Ue:real^N->bool`; `phie:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cinv") THEN
  SUBGOAL_THEN `!y. y IN IMAGE (phie:real^N->real^2) Ue ==> chart_inv(Ue,phie) y IN Ue`
  (LABEL_TAC "cinvU") THENL [USE_THEN "cinv" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^N) IN Ue /\ (phie:real^N->real^2) x0 = z0 + c * Cx t`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "x0" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?lam. &0 < lam /\ lam < &1 /\ x0 = (&1 - lam) % w1 + lam % (w2:real^N)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^N) IN segment(w1,w2)` THEN REWRITE_TAC[IN_SEGMENT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^N) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull {w1:real^N,w2,v} = s` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`w1:real^N`; `w2:real^N`; `v:real^N`; `lam:real`;
      `&0`; `&0`] MOI_PDG_TRI_NEAR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_smo_cell_smooth (s INTER cball(x0:real^N,r)) (phie:real^N->real^2)` THEN
  REWRITE_TAC[moi_smo_cell_smooth] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `Phi:real^N->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "Phieq") (LABEL_TAC "Phiinj"))))))) THEN
  UNDISCH_TAC `moi_smo_cell_smooth s (h:real^N->real^3)` THEN
  REWRITE_TAC[moi_smo_cell_smooth] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real^N->bool` (X_CHOOSE_THEN `H:real^N->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "Heq") (LABEL_TAC "Hinj"))))))) THEN
  UNDISCH_TAC `open_in (subtopology euclidean X) (O:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `O':real^N->bool` STRIP_ASSUME_TAC) THEN
  (* the affine parametrization of the triangle around x0 *)
  MP_TAC(ISPECL [`w1:real^N`; `w2:real^N`; `v:real^N`; `lam:real`;
                 `u INTER u' INTER O' INTER ball(x0:real^N,r)`] MOI_PDG_TRI_PARAM) THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `x0:real^N`)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC) THEN ASM_REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `s INTER cball(x0:real^N,r) SUBSET u` THEN
        REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `s SUBSET (u':real^N->bool)` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(x0:real^N) IN O` THEN ASM_REWRITE_TAC[IN_INTER] THEN MESON_TAC[];
        ASM_REWRITE_TAC[CENTRE_IN_BALL]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `x0:real^N`)) THEN
  ABBREV_TAC `LA = \y:complex. Re y % (w2 - w1) + Im y % (v - w1:real^N)` THEN
  SUBGOAL_THEN `linear(LA:complex->real^N)` ASSUME_TAC THENL
   [EXPAND_TAC "LA" THEN REWRITE_TAC[MOI_PDG_LIN_RE_IM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. norm y < e
        ==> x0 + (LA:complex->real^N) y IN u /\ x0 + LA y IN u' /\ x0 + LA y IN O' /\
            x0 + LA y IN ball(x0,r) /\
            (&0 <= Im y ==> x0 + LA y IN s) /\
            (Im y = &0 ==> x0 + LA y IN segment(w1,w2))`
  (LABEL_TAC "Aprop") THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN EXPAND_TAC "LA" THEN BETA_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:complex` o check (fun th ->
      can (find_term ((=) `e:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. norm y < e /\ &0 <= Im y
        ==> x0 + (LA:complex->real^N) y IN s /\ x0 + LA y IN s INTER cball(x0,r) /\
            (Phi:real^N->real^2)(x0 + LA y) = phie(x0 + LA y) /\
            x0 + LA y IN Ue /\ x0 + LA y IN O`
  (LABEL_TAC "Aside") THENL
   [X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
    USE_THEN "Aprop" (fun th -> MP_TAC(MATCH_MP th (ASSUME `norm(y:complex) < e`))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `x0 + (LA:complex->real^N) y IN s INTER cball(x0,r)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      MP_TAC(ISPECL [`x0:real^N`; `r:real`] BALL_SUBSET_CBALL) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "Phieq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `s INTER cball(x0:real^N,r) SUBSET Ue` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(O:real^N->bool) = X INTER O'` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `s SUBSET (X:real^N->bool)` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `F1 = \y:complex. cnj c * ((Phi:real^N->real^2)(x0 + (LA:complex->real^N) y) -
                                          z0)` THEN
  SUBGOAL_THEN `cnj c * c = Cx(&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_CNJ; COMPLEX_POW_ONE]; ALL_TAC] THEN
  SUBGOAL_THEN `(LA:complex->real^N)(vec 0) = vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPEC `LA:complex->real^N` LINEAR_0) THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(F1:complex->complex)(vec 0) = Cx t` ASSUME_TAC THENL
   [EXPAND_TAC "F1" THEN ASM_REWRITE_TAC[VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `(Phi:real^N->real^2) x0 = phie x0` SUBST1_TAC THENL
     [USE_THEN "Phieq" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[COMPLEX_RING `(z0 + c * x) - z0 = c * x:complex`] THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_ASSOC; COMPLEX_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. abs q < e ==> Im((F1:complex->complex)(Cx q)) = &0` ASSUME_TAC THENL
   [X_GEN_TAC `q:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(Cx q) < e /\ Im(Cx q) = &0` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_NORM_CX; IM_CX]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Im(Cx q)` ASSUME_TAC THENL
     [REWRITE_TAC[IM_CX; REAL_LE_REFL]; ALL_TAC] THEN
    USE_THEN "Aside" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `norm(Cx q) < e`) (ASSUME `&0 <= Im(Cx q)`)))) THEN
    USE_THEN "Aprop" (fun th -> MP_TAC(MATCH_MP th (ASSUME `norm(Cx q) < e`))) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x0 + (LA:complex->real^N)(Cx q)` o check (fun th ->
      can (find_term ((=) `segment(w1:real^N,w2)`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXPAND_TAC "F1" THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_RING `(z0 + c * x) - z0 = c * x:complex`] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_ASSOC; COMPLEX_MUL_LID; IM_CX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. cnj c * ((Phi:real^N->real^2)(x0 + (LA:complex->real^N) y) - z0)) =
                (\z. --(cnj c * z0) + cnj c * z) o Phi o (\y. x0 + LA y)`
  (LABEL_TAC "F1comp") THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  SUBGOAL_THEN `!y. norm y < e ==> x0 + (LA:complex->real^N) y IN u` ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    USE_THEN "Aprop" (fun th -> MP_TAC(MATCH_MP th (ASSUME `norm(y:complex) < e`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(vec 0,e)) (F1:complex->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "F1" THEN USE_THEN "F1comp" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_BALL; OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u:real^N->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC MOI_PDG_AFFINE_SMOOTH THEN ASM_REWRITE_TAC[OPEN_BALL]];
      MATCH_MP_TAC MOI_PDG_AFFINE_SMOOTH THEN REWRITE_TAC[OPEN_UNIV; LINEAR_COMPLEX_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Phi:real^N->real^2) differentiable at x0` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `x0 = x0 + (LA:complex->real^N)(vec 0)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_ADD_RID]; FIRST_X_ASSUM MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[NORM_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((F1:complex->complex) has_derivative
     ((\z. cnj c * z) o frechet_derivative (Phi:real^N->real^2) (at x0) o
      (LA:complex->real^N))) (at (vec 0))` ASSUME_TAC THENL
   [EXPAND_TAC "F1" THEN USE_THEN "F1comp" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_PDG_AFFINE_DERIV THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[VECTOR_ADD_RID; GSYM FRECHET_DERIVATIVE_WORKS]];
      MATCH_MP_TAC MOI_PDG_AFFINE_DERIV THEN REWRITE_TAC[LINEAR_COMPLEX_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(det(jacobian (F1:complex->complex) (at (vec 0))) = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_DET_NZ_INJ THEN CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_DERIVATIVE_IMP_DIFFERENTIABLE); ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    X_GEN_TAC `w:complex` THEN REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `frechet_derivative (Phi:real^N->real^2) (at x0) ((LA:complex->real^N) w) =
                  vec 0` ASSUME_TAC THENL
     [UNDISCH_TAC `cnj c * frechet_derivative (Phi:real^N->real^2) (at x0)
                     ((LA:complex->real^N) w) = vec 0` THEN
      REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ENTIRE; CNJ_EQ_0] THEN
      SUBGOAL_THEN `~(c = Cx(&0))` (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `norm(Cx(&0)) = &1` THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(LA:complex->real^N) w = vec 0` ASSUME_TAC THENL
     [USE_THEN "Phiinj" MATCH_MP_TAC THEN EXISTS_TAC `x0:real^N` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[moi_smo_tangent] THEN
      ABBREV_TAC `dl = e / &2` THEN
      SUBGOAL_THEN `&0 < dl /\ norm(Cx dl) < e /\ norm(ii * Cx dl) < e` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "dl" THEN
        REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_II; COMPLEX_NORM_CX; REAL_MUL_LID] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `x0 + (LA:complex->real^N)(Cx dl) IN s INTER cball(x0,r) /\
                    x0 + LA(ii * Cx dl) IN s INTER cball(x0,r)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "Aside" (MP_TAC o SPEC `Cx dl`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[IM_CX; REAL_LE_REFL]; SIMP_TAC[]];
          USE_THEN "Aside" (MP_TAC o SPEC `ii * Cx dl`) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[IM_MUL_II; RE_CX] THEN ASM_REAL_ARITH_TAC;
                          SIMP_TAC[]]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x0:real^N) IN s INTER cball(x0,r)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `(LA:complex->real^N) w =
        (Re w / dl) % ((x0 + LA(Cx dl)) - x0) + (Im w / dl) % ((x0 + LA(ii * Cx dl)) - x0)`
      SUBST1_TAC THENL
       [EXPAND_TAC "LA" THEN
        REWRITE_TAC[RE_CX; IM_CX; RE_MUL_II; IM_MUL_II; REAL_NEG_0; VECTOR_MUL_LZERO;
                    VECTOR_ADD_LID; VECTOR_ADD_RID;
                    VECTOR_ARITH `(x0 + a) - x0:real^N = a`; VECTOR_MUL_ASSOC] THEN
        SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; ASSUME `&0 < dl`];
        ALL_TAC] THEN
      MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
      MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY (MP_TAC o ASSUME)
       [`x0 + (LA:complex->real^N)(Cx dl) IN s INTER cball(x0,r)`;
        `x0 + (LA:complex->real^N)(ii * Cx dl) IN s INTER cball(x0,r)`;
        `(x0:real^N) IN s INTER cball(x0,r)`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`w1:real^N`; `w2:real^N`; `v:real^N`] MOI_PDG_LIN_INDEP_TRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`Re w`; `Im w`]) THEN
    UNDISCH_TAC `(LA:complex->real^N) w = vec 0` THEN EXPAND_TAC "LA" THEN
    SIMP_TAC[COMPLEX_EQ; COMPLEX_VEC_0; RE_CX; IM_CX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`F1:complex->complex`; `e:real`; `t:real`] MOI_PDG_AXIS_INVERSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real` (X_CHOOSE_THEN `rho:real`
    (X_CHOOSE_THEN `G:complex->complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "Gin")
      (CONJUNCTS_THEN2 (LABEL_TAC "Gsg") (LABEL_TAC "Ginj")))))))))) THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `Ue:real^N->bool`; `phie:real^N->real^2`] MOI_PDG_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open(IMAGE (phie:real^N->real^2) Ue)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                   `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `Ue:real^N->bool`; `phie:real^N->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r2. &0 < r2 /\
         !x. x IN ball(Cx t,r2)
             ==> z0 + c * x IN IMAGE (phie:real^N->real^2) Ue /\
                 chart_inv(Ue,phie)(z0 + c * x) IN O'` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open {x:complex | z0 + c * x IN
                     {y | y IN IMAGE (phie:real^N->real^2) Ue /\ chart_inv(Ue,phie) y IN O'}}`
    MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
        REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
        MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[ETA_AX] THEN
        UNDISCH_TAC `homeomorphism (Ue,IMAGE (phie:real^N->real^2) Ue)
                                   (phie,chart_inv (Ue,phie))` THEN
        SIMP_TAC[homeomorphism]];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `Cx t`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x0:real^N) IN O` THEN
      ASM_REWRITE_TAC[IN_INTER] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r2:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "SUBSET" (concl th) &&
      lhand(concl th) = `ball(Cx t,r2)`)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ue:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_ATLAS_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`; `phie:real^N->real^2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (LA:complex->real^N) y IN moi_smo_tangent s` ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN EXPAND_TAC "LA" THEN REWRITE_TAC[moi_smo_tangent] THEN
    MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
    UNDISCH_TAC `convex hull {w1:real^N,w2,v} = s` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MESON_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. (LA:complex->real^N) y = vec 0 ==> y = vec 0` ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN EXPAND_TAC "LA" THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w1:real^N`; `w2:real^N`; `v:real^N`] MOI_PDG_LIN_INDEP_TRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`Re y`; `Im y`]) THEN
    ASM_REWRITE_TAC[COMPLEX_EQ; COMPLEX_VEC_0; RE_CX; IM_CX];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * cnj c = Cx(&1)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(Cx t,rho) /\ &0 <= Im((G:complex->complex) x)
        ==> x0 + (LA:complex->real^N)(G x) IN s /\ x0 + LA(G x) IN Ue /\
            x0 + LA(G x) IN O /\ chart_inv(Ue,phie)(z0 + c * x) = x0 + LA(G x)`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    USE_THEN "Gin" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:complex) IN ball(Cx t,rho)`))) THEN
    REWRITE_TAC[IN_BALL_0] THEN STRIP_TAC THEN
    USE_THEN "Aside" (fun th -> MP_TAC(MATCH_MP th (CONJ
      (ASSUME `norm((G:complex->complex) x) < e`)
      (ASSUME `&0 <= Im((G:complex->complex) x)`)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(phie:real^N->real^2)(x0 + (LA:complex->real^N)((G:complex->complex) x)) =
                  z0 + c * x` (SUBST1_TAC o SYM) THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        can (find_term ((=) `Phi:real^N->real^2`)) (lhs(concl th)))) THEN
      MATCH_MP_TAC(GEN_ALL(COMPLEX_RING
       `k * c = Cx(&1) /\ k * (p - z0) = x ==> p = z0 + c * x:complex`)) THEN
      EXISTS_TAC `cnj c` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(F1:complex->complex)((G:complex->complex) x) = x` THEN
      EXPAND_TAC "F1" THEN BETA_TAC THEN REWRITE_TAC[];
      USE_THEN "cinv" (fun th -> MATCH_MP_TAC(CONJUNCT1 th)) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `sg:real` THEN EXISTS_TAC `min rho r2` THEN
  EXISTS_TAC `(H:real^N->real^3) o (\y. x0 + (LA:complex->real^N) y) o (G:complex->complex)` THEN
  SUBGOAL_THEN `ball(Cx t,min rho r2) SUBSET ball(Cx t,rho) /\
                ball(Cx t,min rho r2) SUBSET ball(Cx t,r2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(Cx t,min rho r2))
                 ((H:real^N->real^3) o (\y. x0 + (LA:complex->real^N) y) o
                  (G:complex->complex))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u':real^N->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `x:complex` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:complex) IN ball(Cx t,rho)` ASSUME_TAC THENL
       [UNDISCH_TAC `ball(Cx t,min rho r2) SUBSET ball(Cx t,rho)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "Gin" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:complex) IN ball(Cx t,rho)`))) THEN
      REWRITE_TAC[IN_BALL_0] THEN STRIP_TAC THEN
      USE_THEN "Aprop" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `norm((G:complex->complex) x) < e`))) THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
      REWRITE_TAC[OPEN_BALL; OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,rho)` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_PDG_AFFINE_SMOOTH THEN ASM_REWRITE_TAC[OPEN_UNIV]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN ball(Cx t,r2)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(Cx t,min rho r2) SUBSET ball(Cx t,r2)` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
      can (find_term ((=) `r2:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:complex) IN ball(Cx t,rho)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(Cx t,min rho r2) SUBSET ball(Cx t,rho)` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < Im((G:complex->complex) x)` ASSUME_TAC THENL
     [USE_THEN "Gsg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "key" (MP_TAC o SPEC `x:complex`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[]; MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    MP_TAC(ISPECL [`(H:real^N->real^3) o (\y. x0 + (LA:complex->real^N) y) o
                    (G:complex->complex)`;
                   `\x:complex. (h:real^N->real^3)(chart_inv(Ue,phie)(z0 + c * x))`;
                   `t:real`; `min rho r2`; `sg:real`] MOI_PDG_HALF_CLOSURE_SG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(\x:complex. (h:real^N->real^3)(chart_inv(Ue,phie)(z0 + c * x))) =
                      h o chart_inv(Ue,phie) o (\x. z0 + c * x)` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        SUBGOAL_THEN `!x. x IN ball(Cx t,min rho r2)
                          ==> z0 + c * x IN IMAGE (phie:real^N->real^2) Ue`
        (LABEL_TAC "imgB") THENL
         [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
          SUBGOAL_THEN `(x:complex) IN ball(Cx t,r2)` ASSUME_TAC THENL
           [UNDISCH_TAC `ball(Cx t,min rho r2) SUBSET ball(Cx t,r2)` THEN
            REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
            ALL_TAC] THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
            can (find_term ((=) `r2:real`)) (concl th) && is_forall (concl th))) THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
           [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
            MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
            MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
            EXISTS_TAC `IMAGE (phie:real^N->real^2) Ue` THEN CONJ_TAC THENL
             [UNDISCH_TAC `homeomorphism (Ue,IMAGE (phie:real^N->real^2) Ue)
                                         (phie,chart_inv (Ue,phie))` THEN
              SIMP_TAC[homeomorphism];
              REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:complex` THEN
              DISCH_TAC THEN USE_THEN "imgB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `X:real^N->bool` THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `x:complex` THEN
          DISCH_TAC THEN
          UNDISCH_TAC `(Ue:real^N->bool) SUBSET X` THEN REWRITE_TAC[SUBSET] THEN
          DISCH_THEN MATCH_MP_TAC THEN
          USE_THEN "cinvU" MATCH_MP_TAC THEN USE_THEN "imgB" MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]];
        X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(x:complex) IN ball(Cx t,rho)` ASSUME_TAC THENL
         [UNDISCH_TAC `ball(Cx t,min rho r2) SUBSET ball(Cx t,rho)` THEN
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `&0 < Im((G:complex->complex) x)` ASSUME_TAC THENL
         [USE_THEN "Gsg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        USE_THEN "key" (MP_TAC o SPEC `x:complex`) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [ASM_REWRITE_TAC[]; MATCH_MP_TAC REAL_LT_IMP_LE THEN
                                             ASM_REWRITE_TAC[]];
          ALL_TAC] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[o_THM] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
        USE_THEN "Heq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `(x:complex) IN ball(Cx t,r2)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(Cx t,min rho r2) SUBSET ball(Cx t,r2)` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(O:real^N->bool) = X INTER O'` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(Ue:real^N->bool) SUBSET X` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "cinvU" MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
        can (find_term ((=) `r2:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
        can (find_term ((=) `r2:real`)) (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`x:complex`; `w':complex`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:complex) IN ball(Cx t,rho)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(Cx t,min rho r2) SUBSET ball(Cx t,rho)` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Im((G:complex->complex) x)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\x:complex. Im((G:complex->complex) x)`; `t:real`; `min rho r2`;
                     `sg:real`] MOI_PDG_HALF_CLOSURE_LE_SG) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`G:complex->complex`; `&1`; `ball(Cx t,min rho r2)`]
                 MOI_PDG_IM_CONT) THEN
          REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,rho)` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
            ASM_REWRITE_TAC[]];
          X_GEN_TAC `y:complex` THEN STRIP_TAC THEN USE_THEN "Gsg" MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `ball(Cx t,min rho r2) SUBSET ball(Cx t,rho)` THEN
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    USE_THEN "key" (MP_TAC o SPEC `x:complex`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    USE_THEN "Gin" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:complex) IN ball(Cx t,rho)`))) THEN
    REWRITE_TAC[IN_BALL_0] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(G:complex->complex) differentiable at x` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(Cx t,rho)` THEN
      ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(H:real^N->real^3) differentiable at (x0 + (LA:complex->real^N)((G:complex->complex) x))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `u':real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "Aprop" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `norm((G:complex->complex) x) < e`))) THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `frechet_derivative ((H:real^N->real^3) o (\y. x0 + (LA:complex->real^N) y) o
                          (G:complex->complex)) (at x) =
      frechet_derivative H (at (x0 + LA(G x))) o LA o frechet_derivative G (at x)`
    ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
          MATCH_MP_TAC MOI_PDG_AFFINE_DERIV THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
      ALL_TAC] THEN
    UNDISCH_TAC `frechet_derivative ((H:real^N->real^3) o (\y. x0 + (LA:complex->real^N) y) o
                          (G:complex->complex)) (at x) w' = vec 0` THEN
    ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
    USE_THEN "Ginj" MATCH_MP_TAC THEN EXISTS_TAC `x:complex` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) &&
      (try rand(snd(dest_imp(snd(strip_forall(concl th))))) = `vec 0:complex` with _ -> false) &&
      can (find_term ((=) `LA:complex->real^N`)) (concl th))) THEN
    USE_THEN "Hinj" MATCH_MP_TAC THEN
    EXISTS_TAC `x0 + (LA:complex->real^N)((G:complex->complex) x)` THEN
    ASM_REWRITE_TAC[]]);;

(* One-sided extensions of M in an edge chart near a vertex, through the
   transition map into the vertex chart. *)

let MOI_PDG_VERTEX_NOT_RELINT = prove
 (`!L e (w:real^N).
      simplicial_complex L /\ e IN L /\ aff_dim e = &1 /\ {w} IN L
      ==> ~(w IN relative_interior e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~({w:real^N} = e)` ASSUME_TAC THENL
   [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `aff_dim {w:real^N} = &1` THEN REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `{w:real^N}`; `e:real^N->bool`]
         SIMPLICIAL_COMPLEX_DISJOINT_RELATIVE_INTERIORS) THEN
  ASM_REWRITE_TAC[RELATIVE_INTERIOR_SING] THEN ASM SET_TAC[]);;

let MOI_PDG_EDGE_NEAR_RELINT = prove
 (`!L e (w:real^N) delta p.
      simplicial_complex L /\ e IN L /\ aff_dim e = &1 /\ {w} IN L /\ w IN e /\
      (!w w'. {w} IN L /\ {w'} IN L /\ ~(w = w') ==> &2 * delta <= dist(w,w')) /\
      p IN e /\ dist(w,p) < delta /\ ~(p = w)
      ==> p IN relative_interior e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_PDG_EDGE_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^N` (X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~((w:real^N) IN relative_interior e)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_VERTEX_NOT_RELINT THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior e = segment(w1:real^N,w2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) = w1 \/ w = w2` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^N) IN e` THEN UNDISCH_TAC `~((w:real^N) IN relative_interior e)` THEN
    ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(p:real^N) IN e` THEN ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
  REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC(TAUT `~b /\ ~c ==> a \/ b \/ c ==> a`) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`w1:real^N`; `w2:real^N`] o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`w1:real^N`; `w2:real^N`] DIST_SYM) THEN
  MP_TAC(ISPECL [`w1:real^N`; `w2:real^N`] DIST_POS_LE) THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_TRANS_DERIV_INJ = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) V psi x.
      smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
      (V,psi) IN atlas /\ x IN U INTER V
      ==> chart_trans (U,phi) (V,psi) differentiable at (phi x) /\
          !z. frechet_derivative (chart_trans (U,phi) (V,psi)) (at (phi x)) z = vec 0
              ==> z = vec 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
         CHART_TRANS_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[differentiable]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`; `x:A`]
         CHART_JAC_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o C AP_THM `z:real^N`) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `V:A->bool`; `psi:A->real^N`; `U:A->bool`; `phi:A->real^N`; `x:A`]
         CHART_TRANS_HAS_DERIVATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP LINEAR_0
    (CONJUNCT1(REWRITE_RULE[has_derivative] th))]));;

let MOI_PDG_TRANS_PIECE = prove
 (`!(Tm:complex->complex) (gV:complex->complex) (f:real^3->real^3) t d s0 r'
    (P:complex->bool) (K:complex->real^3).
      orthogonal_transformation f /\ &0 < d /\
      smooth_map_on (ball(Cx t,d)) Tm /\
      (!x v. x IN ball(Cx t,d) /\ frechet_derivative Tm (at x) v = vec 0 ==> v = vec 0) /\
      (!x. x IN ball(Cx t,d) ==> Tm x IN ball(Cx s0,r')) /\
      smooth_map_on (ball(Cx s0,r')) gV /\
      (!z. z IN ball(Cx s0,r') ==> &0 < det(jacobian gV (at z))) /\
      (!x. x IN ball(Cx t,d) /\ P x ==> moi_pdg_sti f (gV(Tm x)) = K x)
      ==> smooth_map_on (ball(Cx t,d)) (moi_pdg_sti f o gV o Tm) /\
          (!x. x IN ball(Cx t,d) /\ P x ==> (moi_pdg_sti f o gV o Tm) x = K x) /\
          (!x v. x IN ball(Cx t,d) /\
                 frechet_derivative (moi_pdg_sti f o gV o Tm) (at x) v = vec 0
                 ==> v = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  SUBGOAL_THEN `smooth_map_on (ball(Cx t,d)) ((gV:complex->complex) o (Tm:complex->complex))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `ball(Cx s0,r')` THEN
    ASM_REWRITE_TAC[OPEN_BALL; SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[OPEN_BALL; OPEN_UNIV; SUBSET_UNIV; MOI_PDG_STI_SMOOTH];
    ASM_SIMP_TAC[o_THM];
    MAP_EVERY X_GEN_TAC [`x:complex`; `v:complex`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(gV:complex->complex) o (Tm:complex->complex)`;
                   `moi_pdg_sti (f:real^3->real^3)`; `x:complex`]
           MOI_PDG_DERIV_COMPOSE_INJ) THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    SUBGOAL_THEN `(Tm:complex->complex) differentiable at x /\
                  (gV:complex->complex) differentiable at (Tm x)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
       [EXISTS_TAC `ball(Cx t,d)`; EXISTS_TAC `ball(Cx s0,r')`] THEN
      ASM_SIMP_TAC[OPEN_BALL];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
      ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH];
      MATCH_MP_TAC MOI_PDG_DERIV_COMPOSE_INJ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC MOI_PDG_DET_POS_INJ THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]];
      ASM_MESON_TAC[MOI_PDG_STI_DERIV_INJ]]]);;

let MOI_PDG_TRANS_CLAUSE = prove
 (`!(M:real^N->real^3) (Tm:complex->complex) (gV:complex->complex)
    (V0:complex->complex) (f0:real^3->real^3) (Ue:real^N->bool) (phie:real^N->real^2)
    z0 c t d s0 r' (P:complex->bool) v.
      orthogonal_transformation f0 /\ &0 < d /\ smooth_map_on (ball(Cx t,d)) Tm /\
      (!x u. x IN ball(Cx t,d) /\ frechet_derivative Tm (at x) u = vec 0 ==> u = vec 0) /\
      (!x. x IN ball(Cx t,d) ==> Tm x IN ball(Cx s0,r')) /\
      smooth_map_on (ball(Cx s0,r')) gV /\
      (!z. z IN ball(Cx s0,r') ==> &0 < det(jacobian gV (at z))) /\
      (!x. x IN ball(Cx t,d)
           ==> z0 + c * x IN IMAGE phie Ue /\
               M(chart_inv(Ue,phie)(z0 + c * x)) = moi_pdg_sti f0 (V0(v * Tm x))) /\
      (!x. x IN ball(Cx t,d) /\ P x ==> gV(Tm x) = V0(v * Tm x))
      ==> ?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phie Ue) /\
                (!x. x IN ball(Cx t,r) /\ P x ==> g x = M(chart_inv(Ue,phie)(z0 + c * x))) /\
                (!x v'. x IN ball(Cx t,r) /\ P x /\ frechet_derivative g (at x) v' = vec 0
                        ==> v' = vec 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tm:complex->complex`; `gV:complex->complex`; `f0:real^3->real^3`;
                 `t:real`; `d:real`; `s0:real`; `r':real`; `P:complex->bool`;
                 `\x. (M:real^N->real^3)(chart_inv(Ue,phie)(z0 + c * x))`]
         MOI_PDG_TRANS_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SIMP_TAC[ASSUME `!x. x IN ball(Cx t,d) /\ (P:complex->bool) x
                         ==> (gV:complex->complex)((Tm:complex->complex) x) =
                             (V0:complex->complex)(v * Tm x)`;
             ASSUME `!x. x IN ball(Cx t,d)
                         ==> z0 + c * x IN IMAGE (phie:real^N->real^2) (Ue:real^N->bool) /\
                             (M:real^N->real^3)(chart_inv(Ue,phie)(z0 + c * x)) =
                             moi_pdg_sti (f0:real^3->real^3)
                               ((V0:complex->complex)(v * (Tm:complex->complex) x))`;
             ASSUME `(x:complex) IN ball(Cx t,d)`; ASSUME `(P:complex->bool) x`];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `moi_pdg_sti f0 o (gV:complex->complex) o (Tm:complex->complex)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[]; FIRST_ASSUM(ACCEPT_TAC o BETA_RULE); ASM_MESON_TAC[]]);;

let MOI_PDG_TRANS_EXT = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart e w Ue phie
    z0 c t d0.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      e IN L /\ aff_dim e = &1 /\ {w} IN L /\ w IN e /\ (Ue,phie) IN sigma /\
      norm c = &1 /\
      (!y. y IN relative_interior e ==> y IN Ue /\ ?q. phie y = z0 + c * Cx q) /\
      &0 < d0 /\
      (!q. abs(q - t) < d0
           ==> z0 + c * Cx q IN IMAGE phie Ue /\
               chart_inv(Ue,phie)(z0 + c * Cx q) IN relative_interior e) /\
      chart_inv(Ue,phie)(z0 + c * Cx t) IN U w /\
      norm(phi w (chart_inv(Ue,phie)(z0 + c * Cx t))) < rho w
      ==> (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                 (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phie Ue) /\
                 (!x. x IN ball(Cx t,r) /\ &0 <= Im x
                      ==> g x = moi_pdg_mmap L U phi rho f V h
                                  (chart_inv (Ue,phie) (z0 + c * x))) /\
                 (!x v. x IN ball(Cx t,r) /\ &0 <= Im x /\
                        frechet_derivative g (at x) v = vec 0 ==> v = vec 0)) /\
          (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                 (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phie Ue) /\
                 (!x. x IN ball(Cx t,r) /\ Im x <= &0
                      ==> g x = moi_pdg_mmap L U phi rho f V h
                                  (chart_inv (Ue,phie) (z0 + c * x))) /\
                 (!x v. x IN ball(Cx t,r) /\ Im x <= &0 /\
                        frechet_derivative g (at x) v = vec 0 ==> v = vec 0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  USE_THEN "set" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  ABBREV_TAC `x0 = chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx t)` THEN
  SUBGOAL_THEN `z0 + c * Cx t IN IMAGE (phie:real^N->real^2) Ue /\
                (x0:real^N) IN relative_interior e` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      can (find_term ((=) `d0:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `Ue:real^N->bool`; `phie:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cinv") THEN
  SUBGOAL_THEN `(x0:real^N) IN Ue /\ (phie:real^N->real^2) x0 = z0 + c * Cx t`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "x0" THEN USE_THEN "cinv" (fun th -> ASM_MESON_TAC[th]);
                          ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "vp") THEN
  USE_THEN "vp" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_vp]) THEN
  SUBGOAL_THEN
   `norm((uedge:real^N->(real^N->bool)->complex) w e) = &1 /\
    (!s. &0 <= s /\ s < (rho:real^N->real) w
         ==> chart_inv ((U:real^N->real^N->bool) w,(phi:real^N->real^N->real^2) w)
                       (Cx s * uedge w e) IN e) /\
    (!x. x IN e /\ x IN U w /\ norm(phi w x) < rho w
         ==> ?s. &0 <= s /\ phi w x = Cx s * uedge w e)`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ray_in") (LABEL_TAC "on_ray")))
  THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
      can (find_term ((=) `uedge:real^N->(real^N->bool)->complex`)) (concl th) &&
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `v = (uedge:real^N->(real^N->bool)->complex) w e` THEN
  SUBGOAL_THEN `(x0:real^N) IN e` ASSUME_TAC THENL
   [MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x0:real^N) IN relative_interior e` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s0. &0 < s0 /\ s0 < (rho:real^N->real) w /\
                     (phi:real^N->real^N->real^2) w x0 = Cx s0 * v` STRIP_ASSUME_TAC THENL
   [USE_THEN "on_ray" (MP_TAC o SPEC `x0:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `norm((phi:real^N->real^N->real^2) w x0) = s0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MP_TAC(ASSUME `norm((phi:real^N->real^N->real^2) w x0) = s0`) THEN
      MP_TAC(ASSUME `norm((phi:real^N->real^N->real^2) w x0) < (rho:real^N->real) w`) THEN
      REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= s /\ ~(s = &0) ==> &0 < s`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x0:real^N) = w` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                      `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                      `(U:real^N->real^N->bool) w`;
                      `(phi:real^N->real^N->real^2) w`; `x0:real^N`; `w:real^N`]
             SMOOTH_MANIFOLD_ATLAS_CHART_INJ) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; GSYM COMPLEX_VEC_0];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`; `w:real^N`]
           MOI_PDG_VERTEX_NOT_RELINT) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x0:real^N) IN relative_interior e` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cnj v * v = Cx(&1) /\ v * cnj v = Cx(&1) /\ ~(v = Cx(&0)) /\ ~(c = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_CNJ; COMPLEX_POW_ONE] THEN
    CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_NORM_CX; REAL_ABS_NUM]) THEN
    UNDISCH_TAC `&0 = &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `tau = chart_trans (Ue:real^N->bool,phie:real^N->real^2)
                     ((U:real^N->real^N->bool) w,(phi:real^N->real^N->real^2) w)` THEN
  SUBGOAL_THEN `!y. (phi:real^N->real^N->real^2) w (chart_inv(Ue,phie) y) =
                    (tau:complex->complex) y`
  ASSUME_TAC THENL [EXPAND_TAC "tau" THEN REWRITE_TAC[chart_trans]; ALL_TAC] THEN
  ABBREV_TAC `Om = IMAGE (phie:real^N->real^2) (Ue INTER (U:real^N->real^N->bool) w)` THEN
  SUBGOAL_THEN `open(Om:complex->bool) /\ smooth_map_on Om (tau:complex->complex) /\
                Om SUBSET IMAGE (phie:real^N->real^2) Ue` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Om" THEN EXPAND_TAC "tau" THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `Ue:real^N->bool`; `phie:real^N->real^2`;
                     `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`]
             CHART_OVERLAP_IMAGE_OPEN) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `Ue:real^N->bool`; `phie:real^N->real^2`;
                     `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`]
             CHART_TRANS_SMOOTH) THEN ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN Om ==> chart_inv(Ue,phie) y IN Ue /\
                                chart_inv(Ue,phie) y IN (U:real^N->real^N->bool) w /\
                                (phie:real^N->real^2)(chart_inv(Ue,phie) y) = y`
  (LABEL_TAC "Omp") THENL
   [EXPAND_TAC "Om" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv(Ue,phie) ((phie:real^N->real^2) p) = p` SUBST1_TAC THENL
     [USE_THEN "cinv" (fun th -> MATCH_MP_TAC(CONJUNCT1 th)) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `z0 + c * Cx t IN (Om:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Om" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `x0:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Tm = \x. cnj v * (tau:complex->complex)(z0 + c * x)` THEN
  SUBGOAL_THEN `(Tm:complex->complex) = (\z. cnj v * z) o tau o (\x. z0 + c * x)`
  (LABEL_TAC "Tmcomp") THENL
   [EXPAND_TAC "Tm" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ABBREV_TAC `D = {x:complex | z0 + c * x IN Om}` THEN
  SUBGOAL_THEN `open(D:complex->bool) /\ Cx t IN D` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
        REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on D (Tm:complex->complex)` ASSUME_TAC THENL
   [USE_THEN "Tmcomp" SUBST1_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `Om:complex->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "D" THEN SET_TAC[];
        MATCH_MP_TAC MOI_PDG_AFFINE_SMOOTH THEN ASM_REWRITE_TAC[LINEAR_COMPLEX_MUL]];
      MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN REWRITE_TAC[OPEN_UNIV; LINEAR_COMPLEX_MUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN D
                    ==> (Tm:complex->complex) differentiable at x /\
                        !u. frechet_derivative Tm (at x) u = vec 0 ==> u = vec 0`
  (LABEL_TAC "Tmd") THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `z0 + c * x IN (Om:complex->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:complex) IN D` THEN EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "Omp" (fun th -> MP_TAC(MATCH_MP th (ASSUME `z0 + c * x IN (Om:complex->bool)`))) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                   `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `Ue:real^N->bool`; `phie:real^N->real^2`;
                   `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`;
                   `chart_inv(Ue:real^N->bool,phie:real^N->real^2) (z0 + c * x)`]
           MOI_PDG_TRANS_DERIV_INJ) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    USE_THEN "Tmcomp" SUBST1_TAC THEN
    SUBGOAL_THEN `(\x. z0 + c * x) differentiable at (x:complex) /\
                  (!u. frechet_derivative (\x. z0 + c * x) (at x) u = vec 0 ==> u = vec 0)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `((\x. z0 + c * x) has_derivative (\z. c * z)) (at (x:complex))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_PDG_AFFINE_DERIV THEN REWRITE_TAC[LINEAR_COMPLEX_MUL]; ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_DERIVATIVE_IMP_DIFFERENTIABLE); ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ENTIRE];
      ALL_TAC] THEN
    SUBGOAL_THEN `(\z. cnj v * z) differentiable at ((tau:complex->complex)(z0 + c * x)) /\
                  (!u. frechet_derivative (\z. cnj v * z) (at (tau(z0 + c * x))) u = vec 0
                       ==> u = vec 0)` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `((\z. cnj v * z) has_derivative (\z. cnj v * z))
                    (at ((tau:complex->complex)(z0 + c * x)))` ASSUME_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_COMPLEX_MUL]; ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_DERIVATIVE_IMP_DIFFERENTIABLE); ALL_TAC] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
      ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ENTIRE; CNJ_EQ_0] THEN
      ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `(phie:real^N->real^2)(chart_inv(Ue,phie)(z0 + c * x)) = z0 + c * x`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(tau:complex->complex) differentiable at (z0 + c * x) /\
                  (!u. frechet_derivative tau (at (z0 + c * x)) u = vec 0 ==> u = vec 0)`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[o_THM] THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_PDG_DERIV_COMPOSE_INJ THEN ASM_REWRITE_TAC[o_THM] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_PDG_DERIV_COMPOSE_INJ THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REMOVE_THEN "Tmcomp" (K ALL_TAC) THEN
  SUBGOAL_THEN `(Tm:complex->complex)(Cx t) = Cx s0` ASSUME_TAC THENL
   [EXPAND_TAC "Tm" THEN BETA_TAC THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM(SPEC `z0 + c * Cx t` th)]) o check (fun th ->
      is_forall (concl th) &&
      can (find_term ((=) `tau:complex->complex`)) (concl th) &&
      length(fst(strip_forall(concl th))) = 1 &&
      is_eq(snd(strip_forall(concl th))))) THEN
    REWRITE_TAC[ASSUME `chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx t) = x0`;
                ASSUME `(phi:real^N->real^N->real^2) w x0 = Cx s0 * v`] THEN
    UNDISCH_TAC `cnj v * v = Cx(&1)` THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ABBREV_TAC `N1 = {x | x IN D /\ (Tm:complex->complex) x IN
                        {z | z IN ball(vec 0,(rho:real^N->real) w) /\ Re z > &0}}` THEN
  SUBGOAL_THEN `open(N1:complex->bool) /\ Cx t IN N1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N1" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SET_RULE `{z:complex | z IN s /\ P z} = s INTER {z | P z}`] THEN
        MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_BALL; OPEN_HALFSPACE_RE_GT]];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[IN_BALL_0; RE_CX; COMPLEX_NORM_CX] THEN
      MP_TAC(ASSUME `&0 < s0`) THEN MP_TAC(ASSUME `s0 < (rho:real^N->real) w`) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d1. &0 < d1 /\ d1 <= d0 /\ ball(Cx t,d1) SUBSET N1` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `Cx t` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open(N1:complex->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d d0` THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `&0 < d`) THEN MP_TAC(ASSUME `&0 < d0`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(Cx t,d)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(Cx t,d1)
        ==> x IN D /\ chart_inv(Ue,phie)(z0 + c * x) IN Ue /\
            chart_inv(Ue,phie)(z0 + c * x) IN (U:real^N->real^N->bool) w /\
            (phie:real^N->real^2)(chart_inv(Ue,phie)(z0 + c * x)) = z0 + c * x /\
            (phi:real^N->real^N->real^2) w (chart_inv(Ue,phie)(z0 + c * x)) =
            v * (Tm:complex->complex) x /\
            norm(phi w (chart_inv(Ue,phie)(z0 + c * x))) < (rho:real^N->real) w /\
            &0 < Re(Tm x) /\
            moi_pdg_mmap L U phi rho f V h (chart_inv(Ue,phie)(z0 + c * x)) =
            moi_pdg_sti ((f:real^N->real^3->real^3) w)
                        ((V:real^N->complex->complex) w (v * Tm x))`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN N1` MP_TAC THENL
     [UNDISCH_TAC `ball(Cx t,d1) SUBSET N1` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "N1" THEN REWRITE_TAC[IN_ELIM_THM; IN_BALL_0; real_gt] THEN STRIP_TAC THEN
    SUBGOAL_THEN `z0 + c * x IN (Om:complex->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:complex) IN D` THEN EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "Omp" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `z0 + c * x IN (Om:complex->bool)`))) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(phi:real^N->real^N->real^2) w (chart_inv(Ue,phie)(z0 + c * x)) =
                  v * (Tm:complex->complex) x` ASSUME_TAC THENL
     [EXPAND_TAC "Tm" THEN BETA_TAC THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_forall (concl th) &&
        can (find_term ((=) `tau:complex->complex`)) (concl th) &&
        length(fst(strip_forall(concl th))) = 1 &&
        is_eq(snd(strip_forall(concl th))))) THEN
      UNDISCH_TAC `v * cnj v = Cx(&1)` THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; REAL_MUL_LID] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `v * (Tm:complex->complex) x`)) THEN
    MATCH_MP_TAC MOI_PDG_MMAP_DISC THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q. abs(q - t) < d1 ==> Im((Tm:complex->complex)(Cx q)) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `Cx q IN ball(Cx t,d1)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL; DIST_CX] THEN MP_TAC(ASSUME `abs(q - t) < d1`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `Cx q IN ball(Cx t,d1)`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx q) IN e`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `q:real` o check (fun th ->
        can (find_term ((=) `d0:real`)) (concl th) && is_forall (concl th))) THEN
      ANTS_TAC THENL
       [MP_TAC(ASSUME `abs(q - t) < d1`) THEN MP_TAC(ASSUME `d1 <= d0`) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "on_ray" (MP_TAC o SPEC
      `chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx q)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(Tm:complex->complex)(Cx q) = Cx s` SUBST1_TAC THENL
     [MATCH_MP_TAC(COMPLEX_RING
       `cnj v * v = Cx(&1) /\ v * a = b * v ==> a = b`) THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(phi:real^N->real^N->real^2) w
                    (chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx q))` THEN
      CONJ_TAC THENL [CONV_TAC SYM_CONV; ALL_TAC] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IM_CX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Tm:complex->complex) differentiable at (Cx t) /\
                !u. frechet_derivative Tm (at (Cx t)) u = vec 0 ==> u = vec 0`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "Tmd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (Tm:complex->complex) (at (Cx t))) /\
                ((Tm:complex->complex) has_derivative frechet_derivative Tm (at (Cx t)))
                (at (Cx t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  ABBREV_TAC `B = frechet_derivative (Tm:complex->complex) (at (Cx t))` THEN
  SUBGOAL_THEN `~(Im((B:complex->complex) ii) = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_INJ_REAL_AXIS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PDG_IM_AXIS_DERIV THEN
    MAP_EVERY EXISTS_TAC [`Tm:complex->complex`; `t:real`; `d1:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t,d1) /\ ~(Im x = &0)
                    ==> ~(Im((Tm:complex->complex) x) = &0)` (LABEL_TAC "nonreal") THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:complex) IN ball(Cx t,d1)`))) THEN
    STRIP_TAC THEN
    ABBREV_TAC `p = chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * x)` THEN
    ABBREV_TAC `q' = Re((Tm:complex->complex) x)` THEN
    SUBGOAL_THEN `(Tm:complex->complex) x = Cx q'` ASSUME_TAC THENL
     [EXPAND_TAC "q'" THEN ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
    SUBGOAL_THEN `(phi:real^N->real^N->real^2) w p = Cx q' * v` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    SUBGOAL_THEN `q' < (rho:real^N->real) w` ASSUME_TAC THENL
     [UNDISCH_TAC `norm((phi:real^N->real^N->real^2) w p) < rho w` THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^N) IN e` ASSUME_TAC THENL
     [SUBGOAL_THEN `p = chart_inv ((U:real^N->real^N->bool) w,(phi:real^N->real^N->real^2) w)
                                   (Cx q' * v)` SUBST1_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          rhs(concl th) = `Cx q' * v`)) THEN
        MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                       `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                       `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`]
               CHART_INV) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP(CONJUNCT1 th)
          (ASSUME `(p:real^N) IN (U:real^N->real^N->bool) w`)]);
        USE_THEN "ray_in" MATCH_MP_TAC THEN
        MP_TAC(ASSUME `&0 < q'`) THEN MP_TAC(ASSUME `q' < (rho:real^N->real) w`) THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^N) IN relative_interior e` MP_TAC THENL
     [MATCH_MP_TAC MOI_PDG_EDGE_NEAR_RELINT THEN
      MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `w:real^N`; `delta:real`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`L:(real^N->bool)->bool`;
                       `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                       `h:real^N->real^3`; `w:real^N`; `delta:real`;
                       `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`;
                       `(rho:real^N->real) w`; `(R1:real^N->real) w`;
                       `(f:real^N->real^3->real^3) w`; `(V:real^N->complex->complex) w`;
                       `(uedge:real^N->(real^N->bool)->complex) w`;
                       `(uart:real^N->(real^N->bool)->complex) w`; `p:real^N`]
               MOI_PDG_VP_DISC) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LT_IMP_LE) THEN FIRST_ASSUM ACCEPT_TAC;
          SIMP_TAC[IN_BALL]];
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `(phi:real^N->real^N->real^2) w w = Cx q' * v` THEN
        ASM_REWRITE_TAC[COMPLEX_VEC_0] THEN DISCH_THEN(MP_TAC o SYM) THEN
        ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN MP_TAC(ASSUME `&0 < q'`) THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `relative_interior (e:real^N->bool)`)) (concl th) &&
      not (can (find_term ((=) `d0:real`)) (concl th))))) THEN
    DISCH_THEN(X_CHOOSE_THEN `q'':real` MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `x = Cx q''` ASSUME_TAC THENL
     [UNDISCH_TAC `z0 + c * x = z0 + c * Cx q''` THEN
      UNDISCH_TAC `~(c = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
      UNDISCH_TAC `~(Im(x:complex) = &0)` THEN ASM_REWRITE_TAC[IM_CX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(Cx t,d1) SUBSET D /\ (Tm:complex->complex) continuous_on ball(Cx t,d1)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
      USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:complex) IN ball(Cx t,d1)`))) THEN
      SIMP_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `D:complex->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Tm:complex->complex`; `B:complex->complex`; `t:real`; `d1:real`]
         MOI_PDG_SIDE_UP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IM_CX] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    USE_THEN "nonreal" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "up")] THEN
  MP_TAC(ISPECL [`Tm:complex->complex`; `B:complex->complex`; `t:real`; `d1:real`]
         MOI_PDG_SIDE_DOWN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IM_CX] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    USE_THEN "nonreal" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(LABEL_TAC "down")] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `w:real^N`; `delta:real`; `(U:real^N->real^N->bool) w`;
                 `(phi:real^N->real^N->real^2) w`; `(rho:real^N->real) w`;
                 `(R1:real^N->real) w`; `(f:real^N->real^3->real^3) w`;
                 `(V:real^N->complex->complex) w`;
                 `(uedge:real^N->(real^N->bool)->complex) w`;
                 `(uart:real^N->(real^N->bool)->complex) w`; `v:complex`; `s0:real`]
         MOI_PDG_VP_ONE_SIDED) THEN
  ANTS_TAC THENL
   [USE_THEN "vp" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `g1:complex->complex`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (LABEL_TAC "g1eq") (LABEL_TAC "g1det")))))))
    (X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `g2:complex->complex`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (LABEL_TAC "g2eq") (LABEL_TAC "g2det"))))))))) THEN
  SUBGOAL_THEN `?d2. &0 < d2 /\ d2 <= d1 /\
                     !x. x IN ball(Cx t,d2) ==> (Tm:complex->complex) x IN ball(Cx s0,min r1 r2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(Tm:complex->complex) continuous at (Cx t)` MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `min r1 r2`) THEN
    ANTS_TAC THENL
     [MP_TAC(ASSUME `&0 < r1`) THEN MP_TAC(ASSUME `&0 < r2`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min dd d1` THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `&0 < dd`) THEN MP_TAC(ASSUME `&0 < d1`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:complex` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `dist(x:complex,Cx t) < dd` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN MP_TAC(ASSUME `dist(Cx t,x:complex) < min dd d1`) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `dd:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t,d2) ==> x IN ball(Cx t,d1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Cx t`; `d2:real`; `d1:real`] SUBSET_BALL) THEN
    ASM_REWRITE_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t,d2) /\ Im x = &0 ==> Im((Tm:complex->complex) x) = &0`
  (LABEL_TAC "realax") THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `x = Cx(Re x)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d1:real`)) (concl th) &&
      can (find_term ((=) `Tm:complex->complex`)) (concl th) &&
      not (can (find_term ((=) `D:complex->bool`)) (concl th)))) THEN
    SUBGOAL_THEN `(x:complex) IN ball(Cx t,d1)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(SPEC `Cx t - x` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[RE_SUB; RE_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ball(Cx t,d2)
        ==> z0 + c * x IN IMAGE (phie:real^N->real^2) Ue /\
            moi_pdg_mmap L U phi rho f V h (chart_inv(Ue,phie)(z0 + c * x)) =
            moi_pdg_sti ((f:real^N->real^3->real^3) w)
                        ((V:real^N->complex->complex) w (v * (Tm:complex->complex) x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN ball(Cx t,d1)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:complex) IN ball(Cx t,d1)`))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Om:complex->bool) SUBSET IMAGE (phie:real^N->real^2) Ue` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:complex) IN D` THEN EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(Cx t,d2)) (Tm:complex->complex) /\
                (!x u. x IN ball(Cx t,d2) /\ frechet_derivative Tm (at x) u = vec 0
                       ==> u = vec 0) /\
                (!x. x IN ball(Cx t,d2) ==> Tm x IN ball(Cx s0,r1)) /\
                (!x. x IN ball(Cx t,d2) ==> Tm x IN ball(Cx s0,r2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `D:complex->bool` THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ASSUME `ball(Cx t,d1) SUBSET D`) THEN
      MP_TAC(ASSUME `!x. x IN ball(Cx t,d2) ==> x IN ball(Cx t,d1)`) THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:complex`; `u:complex`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:complex) IN D` ASSUME_TAC THENL
       [MP_TAC(ASSUME `ball(Cx t,d1) SUBSET D`) THEN
        MP_TAC(ASSUME `!x. x IN ball(Cx t,d2) ==> x IN ball(Cx t,d1)`) THEN
        MP_TAC(ASSUME `(x:complex) IN ball(Cx t,d2)`) THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "Tmd" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:complex) IN D`))) THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`Cx s0`; `min r1 r2`; `r1:real`] SUBSET_BALL) THEN
      REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL; SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`Cx s0`; `min r1 r2`; `r2:real`] SUBSET_BALL) THEN
      REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL; SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < Im((B:complex->complex) ii)` THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PDG_TRANS_CLAUSE THEN
      MAP_EVERY EXISTS_TAC [`Tm:complex->complex`; `g1:complex->complex`;
                            `(V:real^N->complex->complex) w`;
                            `(f:real^N->real^3->real^3) w`; `d2:real`; `s0:real`;
                            `r1:real`; `v:complex`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
      USE_THEN "g1eq" MATCH_MP_TAC THEN
      SIMP_TAC[ASSUME `!x. x IN ball(Cx t,d2) ==> (Tm:complex->complex) x IN ball(Cx s0,r1)`;
               ASSUME `(x:complex) IN ball(Cx t,d2)`] THEN
      ASM_CASES_TAC `Im(x:complex) = &0` THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        USE_THEN "realax" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "up" (MP_TAC o SPEC `x:complex`) THEN
        ANTS_TAC THENL
         [SIMP_TAC[ASSUME `!x. x IN ball(Cx t,d2) ==> x IN ball(Cx t,d1)`;
                   ASSUME `(x:complex) IN ball(Cx t,d2)`] THEN
          MP_TAC(ASSUME `&0 <= Im(x:complex)`) THEN MP_TAC(ASSUME `~(Im(x:complex) = &0)`) THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        ONCE_REWRITE_TAC[REAL_MUL_POS_LT] THEN MP_TAC(ASSUME `&0 < Im((B:complex->complex) ii)`) THEN REAL_ARITH_TAC];
      MATCH_MP_TAC MOI_PDG_TRANS_CLAUSE THEN
      MAP_EVERY EXISTS_TAC [`Tm:complex->complex`; `g2:complex->complex`;
                            `(V:real^N->complex->complex) w`;
                            `(f:real^N->real^3->real^3) w`; `d2:real`; `s0:real`;
                            `r2:real`; `v:complex`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
      USE_THEN "g2eq" MATCH_MP_TAC THEN
      SIMP_TAC[ASSUME `!x. x IN ball(Cx t,d2) ==> (Tm:complex->complex) x IN ball(Cx s0,r2)`;
               ASSUME `(x:complex) IN ball(Cx t,d2)`] THEN
      ASM_CASES_TAC `Im(x:complex) = &0` THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        USE_THEN "realax" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "down" (MP_TAC o SPEC `x:complex`) THEN
        ANTS_TAC THENL
         [SIMP_TAC[ASSUME `!x. x IN ball(Cx t,d2) ==> x IN ball(Cx t,d1)`;
                   ASSUME `(x:complex) IN ball(Cx t,d2)`] THEN
          MP_TAC(ASSUME `Im(x:complex) <= &0`) THEN MP_TAC(ASSUME `~(Im(x:complex) = &0)`) THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `m * y < &0 ==> &0 < --m * y`)) THEN
        ONCE_REWRITE_TAC[REAL_MUL_POS_LT] THEN MP_TAC(ASSUME `&0 < Im((B:complex->complex) ii)`) THEN REAL_ARITH_TAC]];
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PDG_TRANS_CLAUSE THEN
      MAP_EVERY EXISTS_TAC [`Tm:complex->complex`; `g2:complex->complex`;
                            `(V:real^N->complex->complex) w`;
                            `(f:real^N->real^3->real^3) w`; `d2:real`; `s0:real`;
                            `r2:real`; `v:complex`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
      USE_THEN "g2eq" MATCH_MP_TAC THEN
      SIMP_TAC[ASSUME `!x. x IN ball(Cx t,d2) ==> (Tm:complex->complex) x IN ball(Cx s0,r2)`;
               ASSUME `(x:complex) IN ball(Cx t,d2)`] THEN
      ASM_CASES_TAC `Im(x:complex) = &0` THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        USE_THEN "realax" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "up" (MP_TAC o SPEC `x:complex`) THEN
        ANTS_TAC THENL
         [SIMP_TAC[ASSUME `!x. x IN ball(Cx t,d2) ==> x IN ball(Cx t,d1)`;
                   ASSUME `(x:complex) IN ball(Cx t,d2)`] THEN
          MP_TAC(ASSUME `&0 <= Im(x:complex)`) THEN MP_TAC(ASSUME `~(Im(x:complex) = &0)`) THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        ONCE_REWRITE_TAC[REAL_MUL_POS_LT] THEN MP_TAC(ASSUME `~(&0 < Im((B:complex->complex) ii))`) THEN
        MP_TAC(ASSUME `~(Im((B:complex->complex) ii) = &0)`) THEN REAL_ARITH_TAC];
      MATCH_MP_TAC MOI_PDG_TRANS_CLAUSE THEN
      MAP_EVERY EXISTS_TAC [`Tm:complex->complex`; `g1:complex->complex`;
                            `(V:real^N->complex->complex) w`;
                            `(f:real^N->real^3->real^3) w`; `d2:real`; `s0:real`;
                            `r1:real`; `v:complex`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
      USE_THEN "g1eq" MATCH_MP_TAC THEN
      SIMP_TAC[ASSUME `!x. x IN ball(Cx t,d2) ==> (Tm:complex->complex) x IN ball(Cx s0,r1)`;
               ASSUME `(x:complex) IN ball(Cx t,d2)`] THEN
      ASM_CASES_TAC `Im(x:complex) = &0` THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        USE_THEN "realax" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "down" (MP_TAC o SPEC `x:complex`) THEN
        ANTS_TAC THENL
         [SIMP_TAC[ASSUME `!x. x IN ball(Cx t,d2) ==> x IN ball(Cx t,d1)`;
                   ASSUME `(x:complex) IN ball(Cx t,d2)`] THEN
          MP_TAC(ASSUME `Im(x:complex) <= &0`) THEN MP_TAC(ASSUME `~(Im(x:complex) = &0)`) THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `m * y < &0 ==> &0 < --m * y`)) THEN
        ONCE_REWRITE_TAC[REAL_MUL_POS_LT] THEN MP_TAC(ASSUME `~(&0 < Im((B:complex->complex) ii))`) THEN
        MP_TAC(ASSUME `~(Im((B:complex->complex) ii) = &0)`) THEN REAL_ARITH_TAC]]]);;

(* Edge parametrisation, outer neighbourhoods, smoothness at faded crease ends *)

let MOI_PDG_EDGE_PSI_CONT = prove
 (`!(w1:real^N) w2 (F1:real^N->real^2) s c a.
      ~(w1 = w2) /\ F1 continuous_on s /\ segment(w1,w2) SUBSET s
      ==> (\l. Re(c * (F1((&1 - l) % w1 + l % w2) - a))) real_continuous_on
          real_interval(&0,&1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON] THEN
  SUBGOAL_THEN
   `lift o (\l. Re(c * ((F1:real^N->real^2)((&1 - l) % w1 + l % w2) - a))) o drop =
    (\z. lift(Re(c * (F1 z - a)))) o (\u. (&1 - drop u) % w1 + drop u % w2)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(Re(c * ((F1:real^N->real^2) z - a)))) =
                (\y. lift(y$1)) o (\y. c * (y - a)) o F1` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; RE_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `segment(w1:real^N,w2)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_SEGMENT] THEN
      ASM_REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN
      X_GEN_TAC `l:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]];
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    MATCH_MP_TAC LINEAR_LIFT_DOLLAR_COMPONENT THEN REWRITE_TAC[DIMINDEX_2] THEN
    ARITH_TAC]);;

let MOI_PDG_EDGE_PARAM = prove
 (`!(X:real^N->bool) sigma Ue (phie:real^N->real^2) (w1:real^N) w2 a p.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (Ue,phie) IN sigma /\
      ~(w1 = w2) /\ segment(w1,w2) SUBSET Ue /\
      (!x. x IN segment(w1,w2) ==> ?t. phie x = a + t % p)
      ==> ?z0 c ps. norm c = &1 /\
                    (!y. y IN segment(w1,w2) ==> ?q. phie y = z0 + c * Cx q) /\
                    (!l. &0 < l /\ l < &1
                         ==> phie((&1 - l) % w1 + l % w2) = z0 + c * Cx(ps l)) /\
                    ps real_continuous_on real_interval(&0,&1) /\
                    (!l l'. &0 < l /\ l < l' /\ l' < &1 ==> ps l < ps l')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x y. x IN segment(w1:real^N,w2) /\ y IN segment(w1,w2) /\
                      (phie:real^N->real^2) x = phie y ==> x = y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                   `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `Ue:real^N->bool`; `phie:real^N->real^2`; `x:real^N`; `y:real^N`]
           SMOOTH_MANIFOLD_ATLAS_CHART_INJ) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l. &0 < l /\ l < &1 ==> (&1 - l) % w1 + l % w2 IN segment(w1:real^N,w2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `l:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l l'. (&1 - l) % w1 + l % w2 = (&1 - l') % w1 + l' % (w2:real^N) ==> l = l'`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - l) % w1 + l % w2 = (&1 - l') % w1 + l' % w2 <=>
                              (l - l') % (w2 - w1:real^N) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p:real^2 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_RZERO; VECTOR_ADD_RID]) THEN
    SUBGOAL_THEN `(&1 - inv(&2)) % w1 + inv(&2) % w2 = (&1 - inv(&4)) % w1 + inv(&4) % (w2:real^N)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `phie:real^N->real^2`)) (concl th) &&
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ASM_MESON_TAC[REAL_ARITH `&0 < inv(&2) /\ inv(&2) < &1 /\ &0 < inv(&4) /\ inv(&4) < &1`]];
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 2 &&
        not (can (find_term (fun t -> t = `phie:real^N->real^2`)) (concl th))))) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  ABBREV_TAC `c0 = inv(norm(p:real^2)) % p` THEN
  SUBGOAL_THEN `norm(c0:complex) = &1 /\ !t. t % (p:real^2) = c0 * Cx(t * norm p)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "c0" THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REWRITE_TAC[NORM_EQ_0];
      GEN_TAC THEN ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
      EXPAND_TAC "c0" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(REAL_FIELD `~(n = &0) ==> t = (t * n) * inv n`) THEN
      ASM_REWRITE_TAC[NORM_EQ_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `cnj c0 * c0 = Cx(&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_CNJ; COMPLEX_POW_ONE]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN segment(w1:real^N,w2)
                    ==> (phie:real^N->real^2) y = a + c0 * Cx(Re(cnj c0 * (phie y - a)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      can (find_term (fun t -> t = `p:real^2`)) (concl th) && is_forall (concl th) &&
      length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:real` SUBST1_TAC) THEN
    ASM_REWRITE_TAC[COMPLEX_RING `(a + b) - a:complex = b`; COMPLEX_MUL_ASSOC; COMPLEX_MUL_LID;
                    RE_CX];
    ALL_TAC] THEN
  ABBREV_TAC `ps0 = \l. Re(cnj c0 * ((phie:real^N->real^2)((&1 - l) % w1 + l % w2) - a))` THEN
  SUBGOAL_THEN `(ps0:real->real) real_continuous_on real_interval(&0,&1)` ASSUME_TAC THENL
   [EXPAND_TAC "ps0" THEN MATCH_MP_TAC MOI_PDG_EDGE_PSI_CONT THEN
    EXISTS_TAC `Ue:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`X:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `Ue:real^N->bool`; `phie:real^N->real^2`] MOI_PDG_CHART_HOMEO) THEN
    ASM_SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l. &0 < l /\ l < &1
                    ==> (phie:real^N->real^2)((&1 - l) % w1 + l % w2) =
                        a + c0 * Cx((ps0:real->real) l)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ps0" THEN BETA_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> t = `c0:complex`)) (concl th))) THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> t = `segment(w1:real^N,w2)`)) (concl th) &&
      not (can (find_term (fun t -> t = `phie:real^N->real^2`)) (concl th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ps0:real->real`; `real_interval(&0,&1)`]
         REAL_CONTINUOUS_INJECTIVE_IFF_MONOTONIC) THEN
  ASM_REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`l:real`; `l':real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 2 &&
      not (can (find_term (fun t -> t = `phie:real^N->real^2`)) (concl th)) &&
      can (find_term (fun t -> t = `w1:real^N`)) (concl th))) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `phie:real^N->real^2`)) (concl th) &&
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`a:complex`; `c0:complex`; `ps0:real->real`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `Re(cnj c0 * ((phie:real^N->real^2) y - a))` THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> t = `c0:complex`)) (concl th) &&
        can (find_term (fun t -> t = `segment(w1:real^N,w2)`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    MAP_EVERY EXISTS_TAC [`a:complex`; `--c0:complex`; `\l. --((ps0:real->real) l)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[NORM_NEG];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `--Re(cnj c0 * ((phie:real^N->real^2) y - a))` THEN
      REWRITE_TAC[CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> t = `c0:complex`)) (concl th) &&
        can (find_term (fun t -> t = `segment(w1:real^N,w2)`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN BETA_TAC THEN
      REWRITE_TAC[CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> t = `ps0:real->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_NEG THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LT_NEG2] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]]);;

let MOI_PDG_OUTER_NBHD = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ x IN UNIONS L /\
      ~(?w. {w} IN L /\ x IN U w /\ norm(phi w x) < rho w)
      ==> ?O. open_in (subtopology euclidean (UNIONS L)) O /\ x IN O /\
              !y. y IN O ==> moi_pdg_mmap L U phi rho f V h y = h y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  ABBREV_TAC `KK = UNIONS (IMAGE (\w. {y:real^N | y IN (U:real^N->real^N->bool) w /\
                                    norm((phi:real^N->real^N->real^2) w y) <=
                                    (rho:real^N->real) w / &2}) {w | {w} IN L})` THEN
  SUBGOAL_THEN `!y. y IN KK <=> ?w. {w} IN L /\ y IN (U:real^N->real^N->bool) w /\
                                 norm((phi:real^N->real^N->real^2) w y) <=
                                 (rho:real^N->real) w / &2` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `closed(KK:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "KK" THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[MOI_PDG_VERTEX_FINITE];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                     `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                     `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                     `uedge:real^N->(real^N->bool)->complex`;
                     `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
             MOI_PDG_SETTING_VP) THEN
      ASM_REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_PDG_INNER_DISC_COMPACT THEN REWRITE_TAC[ETA_AX] THEN
      MAP_EVERY EXISTS_TAC [`UNIONS L:real^N->bool`;
                            `sigma:((real^N->bool)#(real^N->real^2))->bool`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `cball(vec 0:complex,rho(w:real^N))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_CBALL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS L DIFF (KK:real^N->bool)` THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `UNIONS L DIFF (KK:real^N->bool) = UNIONS L INTER ((:real^N) DIFF KK)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed];
    ASM_REWRITE_TAC[IN_DIFF; NOT_EXISTS_THM] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC `~(?w. {w} IN L /\ (x:real^N) IN (U:real^N->real^N->bool) w /\
                       norm((phi:real^N->real^N->real^2) w x) < (rho:real^N->real) w)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                   `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                   `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
           MOI_PDG_SETTING_VP) THEN
    ASM_REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `y:real^N` THEN ASM_REWRITE_TAC[IN_DIFF; NOT_EXISTS_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_PDG_MMAP_OUTER THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let MOI_PDG_END_SMOOTH = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w Ue phie z0 c t.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ {w} IN L /\
      (Ue,phie) IN sigma /\ z0 + c * Cx t IN IMAGE phie Ue /\
      chart_inv(Ue,phie)(z0 + c * Cx t) IN U w /\
      norm(phi w (chart_inv(Ue,phie)(z0 + c * Cx t))) < R1 w
      ==> ?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                !x. x IN ball(Cx t,r)
                    ==> z0 + c * x IN IMAGE phie Ue /\
                        g x = moi_pdg_mmap L U phi rho f V h
                                (chart_inv (Ue,phie) (z0 + c * x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  USE_THEN "set" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "vp") THEN
  USE_THEN "vp" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_vp]) THEN
  ABBREV_TAC `x0 = chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx t)` THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `Ue:real^N->bool`; `phie:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cinv") THEN
  SUBGOAL_THEN `(x0:real^N) IN Ue /\ (phie:real^N->real^2) x0 = z0 + c * Cx t`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN USE_THEN "cinv" (fun th -> ASM_MESON_TAC[th]); ALL_TAC] THEN
  ABBREV_TAC `tau = chart_trans (Ue:real^N->bool,phie:real^N->real^2)
                     ((U:real^N->real^N->bool) w,(phi:real^N->real^N->real^2) w)` THEN
  SUBGOAL_THEN `!y. (phi:real^N->real^N->real^2) w (chart_inv(Ue,phie) y) =
                    (tau:complex->complex) y`
  ASSUME_TAC THENL [EXPAND_TAC "tau" THEN REWRITE_TAC[chart_trans]; ALL_TAC] THEN
  ABBREV_TAC `Om = IMAGE (phie:real^N->real^2) (Ue INTER (U:real^N->real^N->bool) w)` THEN
  SUBGOAL_THEN `open(Om:complex->bool) /\ smooth_map_on Om (tau:complex->complex) /\
                Om SUBSET IMAGE (phie:real^N->real^2) Ue` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Om" THEN EXPAND_TAC "tau" THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `Ue:real^N->bool`; `phie:real^N->real^2`;
                     `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`]
             CHART_OVERLAP_IMAGE_OPEN) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `Ue:real^N->bool`; `phie:real^N->real^2`;
                     `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`]
             CHART_TRANS_SMOOTH) THEN ASM_REWRITE_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN Om ==> chart_inv(Ue,phie) y IN Ue /\
                                chart_inv(Ue,phie) y IN (U:real^N->real^N->bool) w /\
                                (phie:real^N->real^2)(chart_inv(Ue,phie) y) = y`
  (LABEL_TAC "Omp") THENL
   [EXPAND_TAC "Om" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv(Ue,phie) ((phie:real^N->real^2) p) = p` SUBST1_TAC THENL
     [USE_THEN "cinv" (fun th -> MATCH_MP_TAC(CONJUNCT1 th)) THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `z0 + c * Cx t IN (Om:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Om" THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `x0:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `W = {x:complex | x IN {x | z0 + c * x IN (Om:complex->bool)} /\
                   ((tau:complex->complex) o (\x. z0 + c * x)) x IN
                   (u0:complex->bool) INTER ball(vec 0,(rho:real^N->real) w)}` THEN
  SUBGOAL_THEN `open(W:complex->bool) /\ Cx t IN W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
          MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `Om:complex->bool` THEN
          CONJ_TAC THENL [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
                          REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]]];
        MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
        GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
        MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
        REWRITE_TAC[CONTINUOUS_CONST; CONTINUOUS_AT_ID];
        MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_BALL]];
      REWRITE_TAC[IN_ELIM_THM; o_THM; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(tau:complex->complex)(z0 + c * Cx t) = (phi:real^N->real^N->real^2) w x0`
      SUBST1_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `z0 + c * Cx t` o check (fun th ->
          is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
          can (find_term (fun t -> t = `tau:complex->complex`)) (concl th) &&
          is_eq(snd(strip_forall(concl th))))) THEN
        REWRITE_TAC[ASSUME `chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx t) = x0`] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          can (find_term (fun t -> t = `u0:complex->bool`)) (concl th) &&
          can (find_term (fun t -> t = `cball:complex#real->complex->bool`)) (concl th))) THEN
        ASM_SIMP_TAC[IN_CBALL_0; REAL_LT_IMP_LE];
        REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `Cx t` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> concl th = `open(W:complex->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t,r)
                    ==> z0 + c * x IN (Om:complex->bool) /\
                        (tau:complex->complex)(z0 + c * x) IN u0 /\
                        tau(z0 + c * x) IN ball(vec 0,(rho:real^N->real) w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN W` MP_TAC THENL
     [UNDISCH_TAC `ball(Cx t,r) SUBSET W` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "W" THEN REWRITE_TAC[IN_ELIM_THM; o_THM; IN_INTER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `r:real` THEN
  EXISTS_TAC `moi_pdg_sti ((f:real^N->real^3->real^3) w) o
              (V:real^N->complex->complex) w o (tau:complex->complex) o
              (\x. z0 + c * x)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[OPEN_BALL; OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u0:complex->bool` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `Om:complex->bool` THEN
        ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
          MATCH_MP_TAC MOI_PDG_AFFINE_SMOOTH THEN REWRITE_TAC[OPEN_BALL; LINEAR_COMPLEX_MUL]]];
      MATCH_MP_TAC MOI_PDG_STI_SMOOTH THEN REWRITE_TAC[OPEN_UNIV] THEN
      ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR]];
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `r:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "Omp" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `z0 + c * x IN (Om:complex->bool)`))) THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN `(tau:complex->complex)(z0 + c * x) =
                  (phi:real^N->real^N->real^2) w (chart_inv(Ue,phie)(z0 + c * x))`
    SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `(z0:complex) + c * (x:complex)` o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> t = `tau:complex->complex`)) (concl th) &&
        is_eq(snd(strip_forall(concl th))))) THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_PDG_MMAP_DISC THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(z0:complex) + c * (x:complex)` o check (fun th ->
      is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> t = `tau:complex->complex`)) (concl th) &&
      is_eq(snd(strip_forall(concl th))))) THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(tau:complex->complex)(z0 + c * x) IN ball(vec 0,(rho:real^N->real) w)` THEN
    REWRITE_TAC[IN_BALL_0]]);;

(* The edge creases: parameter facts, neighbourhoods of vertices, the two sides of an edge, and MOI_PDG_EDGE_CREASE *)

let MOI_PDG_PS_IVT = prove
 (`!ps la lb t.
      ps real_continuous_on real_interval(&0,&1) /\
      &0 < la /\ la <= lb /\ lb < &1 /\ ps la <= t /\ t <= ps lb
      ==> ?l. la <= l /\ l <= lb /\ ps l = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ps:real->real`; `la:real`; `lb:real`; `t:real`] REAL_IVT_INCREASING) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `real_interval(&0,&1)` THEN ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_REAL_INTERVAL] THEN MESON_TAC[]]);;

let MOI_PDG_PS_LOCAL = prove
 (`!ps l.
      ps real_continuous_on real_interval(&0,&1) /\
      (!l l'. &0 < l /\ l < l' /\ l' < &1 ==> ps l < ps l') /\
      &0 < l /\ l < &1
      ==> ?d. &0 < d /\
              !q. abs(q - ps l) < d ==> ?l'. &0 < l' /\ l' < &1 /\ ps l' = q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(ps:real->real)(l / &2) < ps l /\ ps l < ps((&1 + l) / &2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min ((ps:real->real) l - ps(l / &2)) (ps((&1 + l) / &2) - ps l)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `q:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ps:real->real`; `l / &2`; `(&1 + l) / &2`; `q:real`] MOI_PDG_PS_IVT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `l':real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_PS_MONO = prove
 (`!ps l l'.
      (!l l'. &0 < l /\ l < l' /\ l' < &1 ==> ps l < ps l') /\
      &0 < l /\ l <= l' /\ l' < &1
      ==> ps l <= ps l'`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `l:real = l'` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_R1_NBHD = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ {w} IN L
      ==> ?r. &0 < r /\
              !y. y IN UNIONS L /\ dist(w,y) < r
                  ==> y IN U w /\ norm(phi w y) < R1 w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") ASSUME_TAC) THEN
  USE_THEN "set" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS L))
                 {y | y IN (U:real^N->real^N->bool) w /\
                      (phi:real^N->real^N->real^2) w y IN ball(vec 0,(R1:real^N->real) w)}`
  MP_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `(U:real^N->real^N->bool) w` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN REWRITE_TAC[OPEN_BALL] THEN
      MP_TAC(ISPECL [`UNIONS L:real^N->bool`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`]
             MOI_PDG_CHART_HOMEO) THEN
      ASM_REWRITE_TAC[HOMEOMORPHISM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[ETA_AX];
      MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`]
             SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; IN_BALL_0; NORM_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o REWRITE_RULE[SUBSET] o check (fun th ->
    can (find_term (fun t -> t = `r:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_BALL; IN_ELIM_THM; IN_BALL_0]);;

let MOI_PDG_SEG_NEAR = prove
 (`!(w1:real^N) w2 r.
      ~(w1 = w2) /\ &0 < r
      ==> ?lam. &0 < lam /\ lam <= &1 / &4 /\
                (!l. &0 <= l /\ l < &2 * lam ==> dist(w1,(&1 - l) % w1 + l % w2) < r) /\
                (!l. &1 - &2 * lam < l /\ l <= &1 ==> dist(w2,(&1 - l) % w1 + l % w2) < r)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `n = norm(w2 - w1:real^N)` THEN
  SUBGOAL_THEN `&0 < n` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r / (&2 * n) /\ &2 * (r / (&2 * n)) = r / n` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (&1 / &4) (r / (&2 * n))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    X_GEN_TAC `l:real` THEN STRIP_TAC THEN
    REWRITE_TAC[dist; VECTOR_ARITH
      `w1 - ((&1 - l) % w1 + l % w2):real^N = l % (w1 - w2)`] THEN
    REWRITE_TAC[NORM_MUL] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `l < r / n` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `l:real` THEN STRIP_TAC THEN
    REWRITE_TAC[dist; VECTOR_ARITH
      `w2 - ((&1 - l) % w1 + l % w2):real^N = (&1 - l) % (w2 - w1)`] THEN
    REWRITE_TAC[NORM_MUL] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 - l < r / n` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_SIDES_OPPOSITE = prove
 (`!(X:real^N->bool) sigma Ue phie z0 c t r1 r2 s1 s2 (w1:real^N) w2 sg.
      smooth_manifold_atlas (subtopology euclidean X) sigma /\ (Ue,phie) IN sigma /\
      norm c = &1 /\
      (!y. y IN segment(w1,w2) ==> ?q. phie y = z0 + c * Cx q) /\
      s1 INTER s2 = segment[w1,w2] /\ &0 < r1 /\ &0 < r2 /\
      (sg = &1 \/ sg = -- &1) /\
      (!x. x IN ball(Cx t,r1) ==> z0 + c * x IN IMAGE phie Ue) /\
      (!x. x IN ball(Cx t,r1) /\ &0 < sg * Im x
           ==> chart_inv(Ue,phie)(z0 + c * x) IN s1) /\
      (!x. x IN ball(Cx t,r2) /\ &0 < sg * Im x
           ==> chart_inv(Ue,phie)(z0 + c * x) IN s2)
      ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`subtopology euclidean (X:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `Ue:real^N->bool`; `phie:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ci" o CONJUNCT2) THEN
  SUBGOAL_THEN `~(c = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `norm(c:complex) = &1` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = min r1 r2` THEN
  SUBGOAL_THEN `&0 < r /\ r <= r1 /\ r <= r2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k. Im(Cx t + Cx(sg * k * r) * ii) = sg * k * r` (LABEL_TAC "im") THENL
   [REWRITE_TAC[IM_ADD; IM_CX; IM_MUL_II; RE_CX] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!k. &0 < k /\ k < &1
      ==> Cx t + Cx(sg * k * r) * ii IN ball(Cx t,r1) /\
          Cx t + Cx(sg * k * r) * ii IN ball(Cx t,r2) /\
          &0 < sg * Im(Cx t + Cx(sg * k * r) * ii)`
  (LABEL_TAC "kf") THENL
   [X_GEN_TAC `k:real` THEN STRIP_TAC THEN
    USE_THEN "im" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[IN_BALL; dist] THEN
    REWRITE_TAC[COMPLEX_RING `a - (a + b) = --b:complex`; NORM_NEG;
                COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II; REAL_MUL_RID] THEN
    SUBGOAL_THEN `&0 < k * r /\ k * r < r` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. &0 < k /\ k < &1
      ==> ((chart_inv(Ue,phie)(z0 + c * (Cx t + Cx(sg * k * r) * ii)):real^N) = w1 \/
           chart_inv(Ue,phie)(z0 + c * (Cx t + Cx(sg * k * r) * ii)) = w2) /\
          (phie:real^N->real^2)(chart_inv(Ue,phie)(z0 + c * (Cx t + Cx(sg * k * r) * ii))) =
          z0 + c * (Cx t + Cx(sg * k * r) * ii)`
  (LABEL_TAC "pk") THENL
   [X_GEN_TAC `k:real` THEN DISCH_TAC THEN
    USE_THEN "kf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `&0 < k /\ k < &1`))) THEN
    ABBREV_TAC `x = Cx t + Cx(sg * k * r) * ii` THEN
    SUBGOAL_THEN `z0 + c * x IN IMAGE (phie:real^N->real^2) Ue` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `IMAGE (phie:real^N->real^2) Ue`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "ci" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `z0 + c * x IN IMAGE (phie:real^N->real^2) Ue`))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `chart_inv(Ue,phie)(z0 + c * x) IN segment[w1:real^N,w2]` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(s1:real^N->bool) INTER s2 = segment[w1,w2]`)) THEN
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    MATCH_MP_TAC(TAUT `~a ==> (a \/ b \/ c) ==> b \/ c`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `chart_inv(Ue,phie)(z0 + c * x):real^N` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `segment(w1:real^N,w2)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[COMPLEX_EQ_ADD_LCANCEL; COMPLEX_EQ_MUL_LCANCEL] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real` (MP_TAC o AP_TERM `Im`)) THEN
    REWRITE_TAC[IM_CX] THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < sg * Im x` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j k. &0 < j /\ j < &1 /\ &0 < k /\ k < &1 /\ ~(j = k)
      ==> ~((chart_inv(Ue,phie)(z0 + c * (Cx t + Cx(sg * j * r) * ii)):real^N) =
            chart_inv(Ue,phie)(z0 + c * (Cx t + Cx(sg * k * r) * ii)))`
  (LABEL_TAC "inj") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    USE_THEN "pk" (fun th -> MP_TAC(CONJUNCT2(MP (SPEC `j:real` th)
      (CONJ (ASSUME `&0 < j`) (ASSUME `j < &1`))))) THEN
    USE_THEN "pk" (fun th -> MP_TAC(CONJUNCT2(MP (SPEC `k:real` th)
      (CONJ (ASSUME `&0 < k`) (ASSUME `k < &1`))))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_EQ_ADD_LCANCEL; COMPLEX_EQ_MUL_LCANCEL] THEN
    DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN
    REWRITE_TAC[IM_ADD; IM_CX; IM_MUL_II; RE_CX; REAL_ADD_LID] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL; REAL_LT_IMP_NZ] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "pk" (MP_TAC o SPEC `&1 / &4`) THEN
  USE_THEN "pk" (MP_TAC o SPEC `&1 / &2`) THEN
  USE_THEN "pk" (MP_TAC o SPEC `&3 / &4`) THEN
  USE_THEN "inj" (MP_TAC o SPECL [`&1 / &4`; `&1 / &2`]) THEN
  USE_THEN "inj" (MP_TAC o SPECL [`&1 / &4`; `&3 / &4`]) THEN
  USE_THEN "inj" (MP_TAC o SPECL [`&1 / &2`; `&3 / &4`]) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MESON_TAC[]);;

let MOI_PDG_TWO_SIDES = prove
 (`!(M:real^N->real^3) U phi z0 c t sg1 r1 (g1:real^2->real^3) sg2 r2 g2.
      (sg1 = &1 \/ sg1 = -- &1) /\ (sg2 = &1 \/ sg2 = -- &1) /\ ~(sg1 = sg2) /\
      &0 < r1 /\ smooth_map_on (ball(Cx t,r1)) g1 /\
      (!x. x IN ball(Cx t,r1) ==> z0 + c * x IN IMAGE phi U) /\
      (!x. x IN ball(Cx t,r1) /\ &0 <= sg1 * Im x
           ==> g1 x = M(chart_inv(U,phi)(z0 + c * x))) /\
      (!x v. x IN ball(Cx t,r1) /\ &0 <= sg1 * Im x /\
             frechet_derivative g1 (at x) v = vec 0 ==> v = vec 0) /\
      &0 < r2 /\ smooth_map_on (ball(Cx t,r2)) g2 /\
      (!x. x IN ball(Cx t,r2) ==> z0 + c * x IN IMAGE phi U) /\
      (!x. x IN ball(Cx t,r2) /\ &0 <= sg2 * Im x
           ==> g2 x = M(chart_inv(U,phi)(z0 + c * x))) /\
      (!x v. x IN ball(Cx t,r2) /\ &0 <= sg2 * Im x /\
             frechet_derivative g2 (at x) v = vec 0 ==> v = vec 0)
      ==> (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                 (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phi U) /\
                 (!x. x IN ball(Cx t,r) /\ &0 <= Im x
                      ==> g x = M(chart_inv (U,phi) (z0 + c * x))) /\
                 (!x v. x IN ball(Cx t,r) /\ &0 <= Im x /\
                        frechet_derivative g (at x) v = vec 0 ==> v = vec 0)) /\
          (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                 (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phi U) /\
                 (!x. x IN ball(Cx t,r) /\ Im x <= &0
                      ==> g x = M(chart_inv (U,phi) (z0 + c * x))) /\
                 (!x v. x IN ball(Cx t,r) /\ Im x <= &0 /\
                        frechet_derivative g (at x) v = vec 0 ==> v = vec 0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `(sg1 = &1 /\ sg2 = -- &1) \/ (sg1 = -- &1 /\ sg2 = &1)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `&0 <= &1 * y <=> &0 <= y`;
                              REAL_ARITH `&0 <= -- &1 * y <=> y <= &0`]) THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`r1:real`; `g1:real^2->real^3`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`r2:real`; `g2:real^2->real^3`] THEN ASM_REWRITE_TAC[]];
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`r2:real`; `g2:real^2->real^3`] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`r1:real`; `g1:real^2->real^3`] THEN ASM_REWRITE_TAC[]]]);;

let MOI_PDG_OUTER_CLAUSES = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart (w1:real^N) w2
    Ue phie z0 c t.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      segment[w1,w2] IN L /\ aff_dim(segment[w1,w2]) = &1 /\ ~(w1 = w2) /\
      (Ue,phie) IN sigma /\ norm c = &1 /\
      (!y. y IN segment(w1,w2) ==> y IN Ue /\ ?q. phie y = z0 + c * Cx q) /\
      (!s x. s IN L /\ aff_dim s = &2 /\ segment[w1,w2] SUBSET s /\ x IN segment(w1,w2)
             ==> ?r. &0 < r /\ s INTER cball(x,r) SUBSET Ue /\
                     moi_smo_cell_smooth (s INTER cball(x,r)) phie) /\
      z0 + c * Cx t IN IMAGE phie Ue /\
      chart_inv(Ue,phie)(z0 + c * Cx t) IN segment(w1,w2) /\
      ~(?w. {w} IN L /\ chart_inv(Ue,phie)(z0 + c * Cx t) IN U w /\
            norm(phi w (chart_inv(Ue,phie)(z0 + c * Cx t))) < rho w)
      ==> (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                 (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phie Ue) /\
                 (!x. x IN ball(Cx t,r) /\ &0 <= Im x
                      ==> g x = moi_pdg_mmap L U phi rho f V h
                                  (chart_inv (Ue,phie) (z0 + c * x))) /\
                 (!x v. x IN ball(Cx t,r) /\ &0 <= Im x /\
                        frechet_derivative g (at x) v = vec 0 ==> v = vec 0)) /\
          (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                 (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phie Ue) /\
                 (!x. x IN ball(Cx t,r) /\ Im x <= &0
                      ==> g x = moi_pdg_mmap L U phi rho f V h
                                  (chart_inv (Ue,phie) (z0 + c * x))) /\
                 (!x v. x IN ball(Cx t,r) /\ Im x <= &0 /\
                        frechet_derivative g (at x) v = vec 0 ==> v = vec 0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  USE_THEN "set" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  ABBREV_TAC `x0 = chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx t)` THEN
  SUBGOAL_THEN `(x0:real^N) IN UNIONS L` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[w1:real^N,w2]` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET]
      (ISPECL [`w1:real^N`; `w2:real^N`] SEGMENT_OPEN_SUBSET_CLOSED)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN segment(w1:real^N,w2) ==> ?q. (phie:real^N->real^2) y = z0 + c * Cx q`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      is_forall (concl th) &&
      can (find_term (fun t -> t = `Ue:real^N->bool`)) (concl th) &&
      can (find_term (fun t -> t = `segment(w1:real^N,w2)`)) (concl th) &&
      not (can (find_term (fun t -> t = `cball:real^N#real->real^N->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `x0:real^N`]
         MOI_PDG_OUTER_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(h:real^N->real^3) continuous_on UNIONS L` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (UNIONS L,sphere(vec 0,&1)) (h:real^N->real^3,h')` THEN
    SIMP_TAC[HOMEOMORPHISM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN L /\ aff_dim s = &2 ==> moi_smo_cell_smooth s (h:real^N->real^3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_smo_conical_pd L sigma (h:real^N->real^3)` THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_smo_conical_pd]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN L /\ aff_dim s = &2 /\ segment[w1:real^N,w2] SUBSET s
      ==> ?sg r g. (sg = &1 \/ sg = -- &1) /\ &0 < r /\
                   smooth_map_on (ball(Cx t,r)) (g:complex->real^3) /\
                   (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE (phie:real^N->real^2) Ue) /\
                   (!x. x IN ball(Cx t,r) /\ &0 < sg * Im x
                        ==> chart_inv(Ue,phie)(z0 + c * x) IN s) /\
                   (!x. x IN ball(Cx t,r) /\ &0 <= sg * Im x
                        ==> g x = moi_pdg_mmap L (U:real^N->real^N->bool) phi rho f V h
                                    (chart_inv(Ue,phie)(z0 + c * x))) /\
                   (!x v'. x IN ball(Cx t,r) /\ &0 <= sg * Im x /\
                           frechet_derivative g (at x) v' = vec 0 ==> v' = vec 0)`
  (LABEL_TAC "side") THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`; `w1:real^N`; `w2:real^N`]
           MOI_PDG_TRI_APEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))))) THEN
    SUBGOAL_THEN `moi_smo_cell_smooth s (h:real^N->real^3)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `h:real^N->real^3`)) (concl th) &&
        can (find_term (fun t -> name_of t = "moi_smo_cell_smooth")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `s SUBSET UNIONS (L:(real^N->bool)->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?r. &0 < r /\ s INTER cball(x0:real^N,r) SUBSET Ue /\
                      moi_smo_cell_smooth (s INTER cball(x0,r)) (phie:real^N->real^2)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) &&
        can (find_term (fun t -> t = `cball:real^N#real->real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_PDG_TRI_EXT THEN
    MAP_EVERY EXISTS_TAC [`UNIONS L:real^N->bool`;
                          `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `h:real^N->real^3`; `w1:real^N`; `w2:real^N`; `v:real^N`;
                          `O:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `segment[w1:real^N,w2]`] MOI_PDG_EDGE_TWO_TRI) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "side" (MP_TAC o SPEC `s1:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg1:real` (X_CHOOSE_THEN `r1:real`
    (X_CHOOSE_THEN `g1:complex->real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
  USE_THEN "side" (MP_TAC o SPEC `s2:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg2:real` (X_CHOOSE_THEN `r2:real`
    (X_CHOOSE_THEN `g2:complex->real^3` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
  SUBGOAL_THEN `~(sg1:real = sg2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `Ue:real^N->bool`; `phie:real^N->real^2`; `z0:complex`; `c:complex`;
                   `t:real`; `r1:real`; `r2:real`; `s1:real^N->bool`; `s2:real^N->bool`;
                   `w1:real^N`; `w2:real^N`; `sg2:real`] MOI_PDG_SIDES_OPPOSITE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_TWO_SIDES THEN
  MAP_EVERY EXISTS_TAC [`sg1:real`; `r1:real`; `g1:complex->real^3`;
                        `sg2:real`; `r2:real`; `g2:complex->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_EDGE_POINT = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart (w1:real^N) w2
    Ue phie z0 c t d0.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      segment[w1,w2] IN L /\ aff_dim(segment[w1,w2]) = &1 /\ ~(w1 = w2) /\
      (Ue,phie) IN sigma /\ norm c = &1 /\
      (!y. y IN segment(w1,w2) ==> y IN Ue /\ ?q. phie y = z0 + c * Cx q) /\
      (!s x. s IN L /\ aff_dim s = &2 /\ segment[w1,w2] SUBSET s /\ x IN segment(w1,w2)
             ==> ?r. &0 < r /\ s INTER cball(x,r) SUBSET Ue /\
                     moi_smo_cell_smooth (s INTER cball(x,r)) phie) /\
      &0 < d0 /\
      (!q. abs(q - t) < d0
           ==> z0 + c * Cx q IN IMAGE phie Ue /\
               chart_inv(Ue,phie)(z0 + c * Cx q) IN segment(w1,w2))
      ==> (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                 (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phie Ue) /\
                 (!x. x IN ball(Cx t,r) /\ &0 <= Im x
                      ==> g x = moi_pdg_mmap L U phi rho f V h
                                  (chart_inv (Ue,phie) (z0 + c * x))) /\
                 (!x v. x IN ball(Cx t,r) /\ &0 <= Im x /\
                        frechet_derivative g (at x) v = vec 0 ==> v = vec 0)) /\
          (?r g. &0 < r /\ smooth_map_on (ball(Cx t,r)) (g:real^2->real^3) /\
                 (!x. x IN ball(Cx t,r) ==> z0 + c * x IN IMAGE phie Ue) /\
                 (!x. x IN ball(Cx t,r) /\ Im x <= &0
                      ==> g x = moi_pdg_mmap L U phi rho f V h
                                  (chart_inv (Ue,phie) (z0 + c * x))) /\
                 (!x v. x IN ball(Cx t,r) /\ Im x <= &0 /\
                        frechet_derivative g (at x) v = vec 0 ==> v = vec 0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  USE_THEN "set" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  SUBGOAL_THEN `z0 + c * Cx t IN IMAGE (phie:real^N->real^2) Ue /\
                chart_inv(Ue,phie)(z0 + c * Cx t) IN segment(w1:real^N,w2)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `d0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?w. {w} IN L /\
        chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx t) IN
          (U:real^N->real^N->bool) w /\
        norm((phi:real^N->real^N->real^2) w (chart_inv(Ue,phie)(z0 + c * Cx t))) <
          (rho:real^N->real) w`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(w:real^N) IN segment[w1,w2]` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                     `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                     `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                     `V:real^N->complex->complex`; `uedge:real^N->(real^N->bool)->complex`;
                     `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
             MOI_PDG_SETTING_VP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `h:real^N->real^3`; `w:real^N`; `delta:real`;
                     `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`;
                     `(rho:real^N->real) w`; `(R1:real^N->real) w`;
                     `(f:real^N->real^3->real^3) w`; `(V:real^N->complex->complex) w`;
                     `(uedge:real^N->(real^N->bool)->complex) w`;
                     `(uart:real^N->(real^N->bool)->complex) w`;
                     `chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx t)`]
             MOI_PDG_VP_DISC) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_BALL] THEN STRIP_TAC THEN
      ASM_CASES_TAC `(w:real^N) IN segment[w1,w2]` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
        [`w:real^N`; `segment[w1:real^N,w2]`;
         `chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx t)`] o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 3 &&
        can (find_term (fun t -> t = `delta:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `chart_inv(Ue:real^N->bool,phie:real^N->real^2)(z0 + c * Cx t) IN
                    segment[w1:real^N,w2]` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC(REWRITE_RULE[SUBSET]
          (ISPECL [`w1:real^N`; `w2:real^N`] SEGMENT_OPEN_SUBSET_CLOSED)) THEN
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                   `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                   `V:real^N->complex->complex`; `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `segment[w1:real^N,w2]`;
                   `w:real^N`; `Ue:real^N->bool`; `phie:real^N->real^2`; `z0:complex`;
                   `c:complex`; `t:real`; `d0:real`] MOI_PDG_TRANS_EXT) THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                   `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                   `V:real^N->complex->complex`; `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `w1:real^N`; `w2:real^N`;
                   `Ue:real^N->bool`; `phie:real^N->real^2`; `z0:complex`;
                   `c:complex`; `t:real`] MOI_PDG_OUTER_CLAUSES) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_PDG_EDGE_CREASE = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart e.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      e IN L /\ aff_dim e = &1
      ==> ?Ue phie z0 c a b ee.
            moi_pdg_crease sigma (moi_pdg_mmap L U phi rho f V h) Ue phie z0 c a b ee /\
            (!t. a <= t /\ t <= b
                 ==> chart_inv(Ue,phie)(z0 + c * Cx t) IN relative_interior e) /\
            (!x. x IN relative_interior e /\
                 ~(?t. a + ee < t /\ t < b - ee /\ x = chart_inv(Ue,phie)(z0 + c * Cx t))
                 ==> ?w. {w} IN L /\ w IN e /\ x IN U w /\ norm(phi w x) < R1 w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") STRIP_ASSUME_TAC) THEN
  USE_THEN "set" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_PDG_EDGE_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^N` (X_CHOOSE_THEN `w2:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `relative_interior(segment[w1:real^N,w2]) = segment(w1,w2)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT]; ALL_TAC] THEN
  MP_TAC(CONJUNCT1(CONJUNCT2(CONJUNCT2(GEN_REWRITE_RULE I [moi_smo_conical_pd]
    (ASSUME `moi_smo_conical_pd L sigma (h:real^N->real^3)`))))) THEN
  DISCH_THEN(MP_TAC o SPEC `segment[w1:real^N,w2]`) THEN
  ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ue:real^N->bool` (X_CHOOSE_THEN `phie:real^N->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `a0:complex` (X_CHOOSE_TAC `p0:complex`))
                       (LABEL_TAC "cs")))))) THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `Ue:real^N->bool`; `phie:real^N->real^2`; `w1:real^N`; `w2:real^N`;
                 `a0:complex`; `p0:complex`] MOI_PDG_EDGE_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:complex` (X_CHOOSE_THEN `c:complex`
    (X_CHOOSE_THEN `ps:real->real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "line") (CONJUNCTS_THEN2 (LABEL_TAC "param")
        (CONJUNCTS_THEN2 (LABEL_TAC "pscont") (LABEL_TAC "psmono")))))))) THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `Ue:real^N->bool`; `phie:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cinv") THEN
  SUBGOAL_THEN `!y. y IN segment(w1:real^N,w2)
                    ==> y IN Ue /\ ?q. (phie:real^N->real^2) y = z0 + c * Cx q`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `segment(w1:real^N,w2) SUBSET Ue` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "line" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l. &0 < l /\ l < &1
      ==> (&1 - l) % w1 + l % w2 IN segment(w1:real^N,w2) /\
          z0 + c * Cx((ps:real->real) l) IN IMAGE (phie:real^N->real^2) Ue /\
          chart_inv(Ue,phie)(z0 + c * Cx(ps l)) = (&1 - l) % w1 + l % w2`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `l:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&1 - l) % w1 + l % w2 IN segment(w1:real^N,w2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - l) % w1 + l % w2 IN (Ue:real^N->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `segment(w1:real^N,w2) SUBSET Ue` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "param" (fun th -> MP_TAC(MATCH_MP th (ASSUME `&0 < l /\ l < &1`))) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(&1 - l) % w1 + l % w2:real^N` THEN
      ASM_REWRITE_TAC[];
      USE_THEN "cinv" (fun th -> MATCH_MP_TAC(CONJUNCT1 th)) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l. &0 <= l /\ l <= &1
                    ==> (&1 - l) % w1 + l % (w2:real^N) IN UNIONS L`
  (LABEL_TAC "pu") THENL
   [X_GEN_TAC `l:real` THEN DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `segment[w1:real^N,w2]` THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN
    EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w1:real^N`] MOI_PDG_R1_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ra:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n1"))) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w2:real^N`] MOI_PDG_R1_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n2"))) THEN
  MP_TAC(ISPECL [`w1:real^N`; `w2:real^N`; `min ra rb`] MOI_PDG_SEG_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "near1") (LABEL_TAC "near2"))))) THEN
  SUBGOAL_THEN `!l. &0 < l /\ l < &2 * lam
      ==> (&1 - l) % w1 + l % w2 IN (U:real^N->real^N->bool) w1 /\
          norm((phi:real^N->real^N->real^2) w1 ((&1 - l) % w1 + l % w2)) <
          (R1:real^N->real) w1`
  (LABEL_TAC "e1") THENL
   [X_GEN_TAC `l:real` THEN STRIP_TAC THEN USE_THEN "n1" MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "pu" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "near1" (MP_TAC o SPEC `l:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l. &1 - &2 * lam < l /\ l < &1
      ==> (&1 - l) % w1 + l % w2 IN (U:real^N->real^N->bool) w2 /\
          norm((phi:real^N->real^N->real^2) w2 ((&1 - l) % w1 + l % w2)) <
          (R1:real^N->real) w2`
  (LABEL_TAC "e2") THENL
   [X_GEN_TAC `l:real` THEN STRIP_TAC THEN USE_THEN "n2" MATCH_MP_TAC THEN CONJ_TAC THENL
     [USE_THEN "pu" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      USE_THEN "near2" (MP_TAC o SPEC `l:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ps:real->real) lam < ps(&2 * lam) /\
                ps(&2 * lam) <= ps(&1 - &2 * lam) /\
                ps(&1 - &2 * lam) < ps(&1 - lam)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "psmono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_PDG_PS_MONO THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "psmono" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `a = (ps:real->real) lam` THEN
  ABBREV_TAC `b = (ps:real->real)(&1 - lam)` THEN
  ABBREV_TAC `ee = min ((ps:real->real)(&2 * lam) - a) (b - ps(&1 - &2 * lam)) / &4` THEN
  SUBGOAL_THEN `&0 < ee /\ &4 * ee < b - a /\ a < b /\
                a + ee < (ps:real->real)(&2 * lam) /\ ps(&1 - &2 * lam) < b - ee`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "ee" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!l. &0 < l /\ l < &1 /\ (ps:real->real) l <= a + ee ==> l < &2 * lam`
  (LABEL_TAC "lo") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ps:real->real`; `&2 * lam`; `l:real`] MOI_PDG_PS_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l. &0 < l /\ l < &1 /\ b - ee <= (ps:real->real) l ==> &1 - &2 * lam < l`
  (LABEL_TAC "hi") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ps:real->real`; `l:real`; `&1 - &2 * lam`] MOI_PDG_PS_MONO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= b ==> ?l. lam <= l /\ l <= &1 - lam /\ (ps:real->real) l = t`
  (LABEL_TAC "ivt") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_PS_IVT THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Ue:real^N->bool`; `phie:real^N->real^2`; `z0:complex`; `c:complex`;
                        `a:real`; `b:real`; `ee:real`] THEN
  REWRITE_TAC[moi_pdg_crease] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "ivt" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)))) THEN
    MP_TAC(ISPECL [`ps:real->real`; `l:real`] MOI_PDG_PS_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
    MATCH_MP_TAC MOI_PDG_EDGE_POINT THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`;
                          `w1:real^N`; `w2:real^N`; `d0:real`] THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:real` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `abs(q - (ps:real->real) l) < d0`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `l':real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)))) THEN
    USE_THEN "pt" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `&0 < l'`) (ASSUME `l' < &1`)))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "ivt" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)))) THEN
    SUBGOAL_THEN `&0 < l /\ l < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pt" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `&0 < l /\ l < &1`))) THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [SUBGOAL_THEN `l < &2 * lam` ASSUME_TAC THENL
       [USE_THEN "lo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_PDG_END_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                            `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                            `uedge:real^N->(real^N->bool)->complex`;
                            `uart:real^N->(real^N->bool)->complex`; `w1:real^N`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "e1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `&1 - &2 * lam < l` ASSUME_TAC THENL
       [USE_THEN "hi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_PDG_END_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`;
                            `h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                            `uedge:real^N->(real^N->bool)->complex`;
                            `uart:real^N->(real^N->bool)->complex`; `w2:real^N`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "e2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "ivt" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)))) THEN
    SUBGOAL_THEN `&0 < l /\ l < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "pt" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `&0 < l /\ l < &1`))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[IN_SEGMENT]) (LABEL_TAC "nm")) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
    USE_THEN "pt" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (CONJ (ASSUME `&0 < l`) (ASSUME `l < &1`)))) THEN
    SUBGOAL_THEN `(ps:real->real) l <= a + ee \/ b - ee <= ps l` MP_TAC THENL
     [USE_THEN "nm" (MP_TAC o SPEC `(ps:real->real) l` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `w1:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      USE_THEN "e1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "lo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `w2:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      USE_THEN "e2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "hi" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;


(* Immersion off the crease middles: vertex charts, rays, triangles, MOI_PDG_IMM_OFF *)

let MOI_PDG_JAC_LOCAL_EQ = prove
 (`!(f:real^M->real^N) g s x.
      open s /\ x IN s /\ (!y. y IN s ==> f y = g y) /\ f differentiable at x
      ==> jacobian f (at x) = jacobian g (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC(GEN_ALL HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN) THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `s:real^M->bool`] THEN
  ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let MOI_PDG_IMM_VCHART = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w x W
    (g:real^2->real^3).
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ {w} IN L /\
      x IN U w /\ open W /\ phi w x IN W /\ W SUBSET ball(vec 0,rho w) /\
      smooth_map_on W g /\
      (!y. y IN W ==> g y = moi_pdg_sti (f w) (V w y)) /\
      (!y v. y IN W /\ frechet_derivative g (at y) v = vec 0 ==> v = vec 0)
      ==> moi_pdg_imm_at sigma (moi_pdg_mmap L U phi rho f V h) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_vp]) THEN
  REWRITE_TAC[moi_pdg_imm_at] THEN
  MAP_EVERY EXISTS_TAC [`(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`;
                        `W:real^2->bool`; `g:real^2->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `cball(vec 0:real^2,(rho:real^N->real) w)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(vec 0:real^2,(rho:real^N->real) w)` THEN
    ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm((phi:real^N->real^N->real^2) w z) < (rho:real^N->real) w`
  ASSUME_TAC THENL
   [UNDISCH_TAC `W SUBSET ball(vec 0:real^2,(rho:real^N->real) w)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`; `z:real^N`]
         MOI_PDG_MMAP_DISC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `g:real^2->real^3`)) (concl th) &&
    can (find_term (fun t -> name_of t = "moi_pdg_sti")) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_IMM_INNER = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ {w} IN L /\
      x IN U w /\ norm(phi w x) < R1 w
      ==> moi_pdg_imm_at sigma (moi_pdg_mmap L U phi rho f V h) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_vp]) THEN
  MP_TAC(ISPECL [`(f:real^N->real^3->real^3) w`; `(V:real^N->complex->complex) w`;
                 `(u0:complex->bool) INTER ball(vec 0,(R1:real^N->real) w)`]
         MOI_PDG_STI_EXT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; IN_INTER] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u0:complex->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    STRIP_TAC] THEN
  MATCH_MP_TAC MOI_PDG_IMM_VCHART THEN
  MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                        `uedge:real^N->(real^N->bool)->complex`;
                        `uart:real^N->(real^N->bool)->complex`; `w:real^N`;
                        `(u0:complex->bool) INTER ball(vec 0,(R1:real^N->real) w)`;
                        `moi_pdg_sti ((f:real^N->real^3->real^3) w) o
                         (V:real^N->complex->complex) w`] THEN
  ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL];
    REWRITE_TAC[IN_INTER; IN_BALL_0] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cball(vec 0:complex,(R1:real^N->real) w) SUBSET u0` THEN
    REWRITE_TAC[SUBSET; IN_CBALL_0] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball(vec 0:complex,(R1:real^N->real) w)` THEN
    REWRITE_TAC[INTER_SUBSET] THEN ASM_SIMP_TAC[SUBSET_BALL; REAL_LT_IMP_LE]]);;

let MOI_PDG_IMM_OFFRAY = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ {w} IN L /\
      x IN U w /\ norm(phi w x) < rho w /\ ~(phi w x = vec 0) /\
      (!e t. e IN L /\ aff_dim e = &1 /\ w IN e /\ &0 < t
             ==> ~(phi w x = Cx t * uedge w e)) /\
      (!s t. s IN L /\ aff_dim s = &2 /\ w IN s /\ &0 < t
             ==> ~(phi w x = Cx t * uart w s))
      ==> moi_pdg_imm_at sigma (moi_pdg_mmap L U phi rho f V h) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_vp]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(phi:real^N->real^N->real^2) w x` o check (fun th ->
    is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
    can (find_term (fun t -> t = `(uart:real^N->(real^N->bool)->complex) w`)) (concl th) &&
    can (find_term (fun t -> t = `(uedge:real^N->(real^N->bool)->complex) w`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`(f:real^N->real^3->real^3) w`; `(V:real^N->complex->complex) w`;
                 `ball((phi:real^N->real^N->real^2) w x,r)`] MOI_PDG_STI_EXT) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_PDG_IMM_VCHART THEN
  MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                        `uedge:real^N->(real^N->bool)->complex`;
                        `uart:real^N->(real^N->bool)->complex`; `w:real^N`;
                        `ball((phi:real^N->real^N->real^2) w x,r)`;
                        `moi_pdg_sti ((f:real^N->real^3->real^3) w) o
                         (V:real^N->complex->complex) w`] THEN
  ASM_REWRITE_TAC[o_THM; OPEN_BALL; CENTRE_IN_BALL] THEN ASM_MESON_TAC[]);;

let MOI_PDG_DET_FROM_SIDES = prove
 (`!(G:complex->complex) g1 g2 t r.
      smooth_map_on (ball(Cx t,r)) G /\
      smooth_map_on (ball(Cx t,r)) g1 /\ smooth_map_on (ball(Cx t,r)) g2 /\
      (!x. x IN ball(Cx t,r) /\ &0 <= Im x ==> g1 x = G x) /\
      (!x. x IN ball(Cx t,r) /\ Im x <= &0 ==> g2 x = G x) /\
      (!x. x IN ball(Cx t,r) ==> &0 < det(jacobian g1 (at x))) /\
      (!x. x IN ball(Cx t,r) ==> &0 < det(jacobian g2 (at x)))
      ==> !x. x IN ball(Cx t,r) ==> &0 < det(jacobian G (at x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t,r) /\ &0 < Im x
                    ==> (\x. lift(det(jacobian (G:complex->complex) (at x)))) x =
                        (\x. lift(det(jacobian (g1:complex->complex) (at x)))) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_PDG_JAC_LOCAL_EQ THEN
    EXISTS_TAC `ball(Cx t,r) INTER {z:complex | Im z > &0}` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_HALFSPACE_IM_GT; IN_INTER; IN_ELIM_THM;
                 real_gt] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:complex` THEN STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `g1:complex->complex`)) (concl th) &&
        can (find_term (fun t -> t = `&0 <= Im x`)) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(Cx t,r)` THEN ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t,r) /\ &0 < -- &1 * Im x
                    ==> (\x. lift(det(jacobian (G:complex->complex) (at x)))) x =
                        (\x. lift(det(jacobian (g2:complex->complex) (at x)))) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_PDG_JAC_LOCAL_EQ THEN
    EXISTS_TAC `ball(Cx t,r) INTER {z:complex | Im z < &0}` THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_HALFSPACE_IM_LT; IN_INTER; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:complex` THEN STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `g2:complex->complex`)) (concl th) &&
        can (find_term (fun t -> t = `Im x <= &0`)) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(Cx t,r)` THEN ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(det(jacobian (G:complex->complex) (at x)))`;
                 `\x. lift(det(jacobian (g1:complex->complex) (at x)))`;
                 `Cx t`; `r:real`] MOI_PDG_HALF_CLOSURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_JAC_DET_CONT THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[LIFT_EQ] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`\x. lift(det(jacobian (G:complex->complex) (at x)))`;
                 `\x. lift(det(jacobian (g2:complex->complex) (at x)))`;
                 `t:real`; `r:real`; `-- &1`] MOI_PDG_HALF_CLOSURE_SG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_JAC_DET_CONT THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[LIFT_EQ] THEN DISCH_TAC] THEN
  X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `&0 <= Im(x:complex) \/ &0 <= -- &1 * Im x`) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
      can (find_term (fun t -> t = `g1:complex->complex`)) (concl th) &&
      can (find_term (fun t -> t = `&0 <= Im x`)) (concl th) &&
      can (find_term (fun t -> name_of t = "det")) (concl th)));
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
      can (find_term (fun t -> t = `g2:complex->complex`)) (concl th) &&
      can (find_term (fun t -> t = `&0 <= -- &1 * Im x`)) (concl th) &&
      can (find_term (fun t -> name_of t = "det")) (concl th)))] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[]);;

let MOI_PDG_IMM_ROT = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w x v t r.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ {w} IN L /\
      x IN U w /\ norm v = &1 /\ phi w x = Cx t * v /\ &0 < r /\
      smooth_map_on (ball(Cx t,r)) (\y. V w (v * y)) /\
      (!y. y IN ball(Cx t,r) ==> v * y IN ball(vec 0,rho w)) /\
      (!y. y IN ball(Cx t,r) ==> &0 < det(jacobian (\y. V w (v * y)) (at y)))
      ==> moi_pdg_imm_at sigma (moi_pdg_mmap L U phi rho f V h) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_vp]) THEN
  ABBREV_TAC `G = \y. (V:real^N->complex->complex) w (v * y)` THEN
  MP_TAC(ISPECL [`(f:real^N->real^3->real^3) w`; `G:complex->complex`;
                 `ball(Cx t,r)`] MOI_PDG_STI_EXT) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(cnj v = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[CNJ_EQ_0] THEN DISCH_TAC THEN UNDISCH_TAC `norm(v:complex) = &1` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_IMM_VCHART THEN
  MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                        `uedge:real^N->(real^N->bool)->complex`;
                        `uart:real^N->(real^N->bool)->complex`; `w:real^N`;
                        `{y:complex | cnj v * y IN ball(Cx t,r)}`;
                        `(moi_pdg_sti ((f:real^N->real^3->real^3) w) o G) o
                         (\y:complex. cnj v * y)`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN REWRITE_TAC[OPEN_BALL] THEN
    GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
      REWRITE_TAC[LINEAR_COMPLEX_MUL; REWRITE_RULE[ETA_AX] (ISPEC `cnj v` LINEAR_COMPLEX_MUL)];
    REWRITE_TAC[COMPLEX_RING `cnj v * (Cx t * v) = Cx t * (cnj v * v)`; COMPLEX_MUL_CNJ] THEN
    ASM_REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_MUL_RID; CENTRE_IN_BALL];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    UNDISCH_TAC `!y. y IN ball(Cx t,r) ==> v * y IN ball(vec 0,(rho:real^N->real) w)` THEN
    DISCH_THEN(MP_TAC o SPEC `cnj v * y:complex`) THEN
    ASM_SIMP_TAC[MOI_PDG_UNIT_ROT];
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `ball(Cx t,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN REWRITE_TAC[OPEN_BALL] THEN
      GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
      REWRITE_TAC[LINEAR_COMPLEX_MUL; REWRITE_RULE[ETA_AX] (ISPEC `cnj v` LINEAR_COMPLEX_MUL)];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[];
      MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN REWRITE_TAC[LINEAR_COMPLEX_MUL] THEN
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN REWRITE_TAC[OPEN_BALL] THEN
      GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
      REWRITE_TAC[LINEAR_COMPLEX_MUL; REWRITE_RULE[ETA_AX] (ISPEC `cnj v` LINEAR_COMPLEX_MUL)]];
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    EXPAND_TAC "G" THEN ASM_SIMP_TAC[MOI_PDG_UNIT_ROT];
    MAP_EVERY X_GEN_TAC [`y:complex`; `d:complex`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\y:complex. cnj v * y`; `moi_pdg_sti ((f:real^N->real^3->real^3) w) o
                   (G:complex->complex)`; `y:complex`] MOI_PDG_DERIV_COMPOSE_INJ) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN REWRITE_TAC[LINEAR_COMPLEX_MUL];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(Cx t,r)` THEN
        ASM_REWRITE_TAC[OPEN_BALL];
        GEN_TAC THEN
        SUBGOAL_THEN `frechet_derivative (\y:complex. cnj v * y) (at y) = (\y. cnj v * y)`
        SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
          MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_COMPLEX_MUL];
          ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ENTIRE]];
        GEN_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> name_of t = "frechet_derivative")) (concl th) &&
          can (find_term (fun t -> t = `G:complex->complex`)) (concl th))) THEN
        EXISTS_TAC `cnj v * y:complex` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let MOI_PDG_IMM_ARTRAY = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w s x t.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ {w} IN L /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\ x IN U w /\
      rho w / &4 <= t /\ t < rho w /\ phi w x = Cx t * uart w s
      ==> moi_pdg_imm_at sigma (moi_pdg_mmap L U phi rho f V h) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> LABEL_TAC "vp" th THEN
    STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [moi_pdg_vp] th)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `w:real^N`; `delta:real`;
                 `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`;
                 `(rho:real^N->real) w`; `(R1:real^N->real) w`;
                 `(f:real^N->real^3->real^3) w`; `(V:real^N->complex->complex) w`;
                 `(uedge:real^N->(real^N->bool)->complex) w`;
                 `(uart:real^N->(real^N->bool)->complex) w`;
                 `(uart:real^N->(real^N->bool)->complex) w s`; `t:real`]
         MOI_PDG_VP_ONE_SIDED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `g1:complex->complex` STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `r2:real` (X_CHOOSE_THEN `g2:complex->complex` STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `t:real`] o check (fun th ->
    is_forall (concl th) && length(fst(strip_forall(concl th))) = 2 &&
    can (find_term (fun t -> t = `(rho:real^N->real) w / &4`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min r0 (min r1 r2)` THEN
  SUBGOAL_THEN `&0 < r /\ ball(Cx t,r) SUBSET ball(Cx t,r0) /\
                ball(Cx t,r) SUBSET ball(Cx t,r1) /\ ball(Cx t,r) SUBSET ball(Cx t,r2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_BALL THEN EXPAND_TAC "r" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(Cx t,r)
                    ==> y IN ball(Cx t,r0) /\ y IN ball(Cx t,r1) /\ y IN ball(Cx t,r2)`
  (LABEL_TAC "bl") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY (fun tm -> MP_TAC(SPEC `y:complex` (REWRITE_RULE[SUBSET] (ASSUME tm))))
      [`ball(Cx t,r) SUBSET ball(Cx t,r0)`; `ball(Cx t,r) SUBSET ball(Cx t,r1)`;
       `ball(Cx t,r) SUBSET ball(Cx t,r2)`] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(Cx t,r))
     (\y. (V:real^N->complex->complex) w ((uart:real^N->(real^N->bool)->complex) w s * y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r0)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_IMM_ROT THEN
  MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                        `uedge:real^N->(real^N->bool)->complex`;
                        `uart:real^N->(real^N->bool)->complex`; `w:real^N`;
                        `(uart:real^N->(real^N->bool)->complex) w s`; `t:real`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `r0:real`)) (concl th))) THEN
    USE_THEN "bl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `y IN ball(Cx t,r)`)));
    MATCH_MP_TAC MOI_PDG_DET_FROM_SIDES THEN
    MAP_EVERY EXISTS_TAC [`g1:complex->complex`; `g2:complex->complex`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r1)` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t,r2)` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
      USE_THEN "bl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `y IN ball(Cx t,r)`))) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `g1:complex->complex`)) (concl th) &&
        can (find_term (fun t -> t = `&0 <= Im x`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
      USE_THEN "bl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `y IN ball(Cx t,r)`))) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `g2:complex->complex`)) (concl th) &&
        can (find_term (fun t -> t = `Im x <= &0`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
      USE_THEN "bl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `y IN ball(Cx t,r)`))) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `g1:complex->complex`)) (concl th) &&
        can (find_term (fun t -> name_of t = "det")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
      USE_THEN "bl" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `y IN ball(Cx t,r)`))) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `g2:complex->complex`)) (concl th) &&
        can (find_term (fun t -> name_of t = "det")) (concl th))) THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_PDG_IMM_TRI = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart s x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      s IN L /\ aff_dim s = &2 /\ x IN relative_interior s /\
      ~(?w. {w} IN L /\ x IN U w /\ norm(phi w x) < rho w)
      ==> moi_pdg_imm_at sigma (moi_pdg_mmap L U phi rho f V h) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  USE_THEN "set" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS L` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `x:real^N`]
         MOI_PDG_OUTER_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_PDG_IMM_AT_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`UNIONS L:real^N->bool`; `h:real^N->real^3`; `O:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?U' phi'. (U',phi') IN (sigma:((real^N->bool)#(real^N->real^2))->bool) /\
                          (x:real^N) IN U'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `smooth_manifold_atlas (subtopology euclidean (UNIONS L:real^N->bool))
                   (sigma:((real^N->bool)#(real^N->real^2))->bool)` THEN
    REWRITE_TAC[smooth_manifold_atlas; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(GEN_REWRITE_RULE I [moi_smo_conical_pd]
    (ASSUME `moi_smo_conical_pd L sigma (h:real^N->real^3)`))))) THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `U':real^N->bool`; `phi':real^N->real^2`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^3` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_pdg_imm_at] THEN
  MAP_EVERY EXISTS_TAC [`U':real^N->bool`; `phi':real^N->real^2`;
                        `IMAGE (phi':real^N->real^2) (U' INTER relative_interior s)`;
                        `g:real^2->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CHART_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`subtopology euclidean (UNIONS L:real^N->bool)`;
                          `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `U':real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                     `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `U':real^N->bool`; `phi':real^N->real^2`]
             SMOOTH_MANIFOLD_ATLAS_CHART) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC MOI_PDG_TRI_OPEN THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z':real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `z:real^N = z'` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                           `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                           `U':real^N->bool`; `phi':real^N->real^2`]
                          SMOOTH_MANIFOLD_ATLAS_CHART_INJ) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z':real^N) IN U' INTER relative_interior s` THEN SIMP_TAC[IN_INTER];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `g:real^2->real^3`)) (concl th) &&
      can (find_term (fun t -> t = `h:real^N->real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_PDG_R1_DISC_UNIQUE = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart w w' x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      {w} IN L /\ x IN U w /\ norm(phi w x) < rho w /\
      {w'} IN L /\ x IN U w' /\ norm(phi w' x) < R1 w'
      ==> w' = w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w':real^N`]
         MOI_PDG_SETTING_VP) THEN
  ASM_REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w':real^N`; `w:real^N`; `x:real^N`]
         MOI_PDG_DISC_UNIQUE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let MOI_PDG_IMM_OFF = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart x.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\ x IN UNIONS L /\
      (!e. e IN L /\ aff_dim e = &1 /\ x IN relative_interior e
           ==> ?w. {w} IN L /\ x IN U w /\ norm(phi w x) < R1 w) /\
      (!w s t. {w} IN L /\ s IN L /\ aff_dim s = &2 /\ w IN s /\
               R1 w / &2 + min (R1 w / &4) ((rho w - R1 w) / &10) < t /\
               t < rho w / &2 - min (R1 w / &4) ((rho w - R1 w) / &10)
               ==> ~(x = chart_inv (U w,phi w) (vec 0 + uart w s * Cx t)))
      ==> moi_pdg_imm_at sigma (moi_pdg_mmap L U phi rho f V h) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "hedge") (LABEL_TAC "hart")))) THEN
  USE_THEN "set" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  ASM_CASES_TAC `?w. {w} IN L /\ x IN (U:real^N->real^N->bool) w /\
                     norm((phi:real^N->real^N->real^2) w x) < (rho:real^N->real) w` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `norm((phi:real^N->real^N->real^2) w x) < (R1:real^N->real) w` THENL
     [MATCH_MP_TAC MOI_PDG_IMM_INNER THEN
      MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                            `uedge:real^N->(real^N->bool)->complex`;
                            `uart:real^N->(real^N->bool)->complex`; `w:real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                   `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                   `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
           MOI_PDG_SETTING_VP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> LABEL_TAC "vp" th THEN
      STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [moi_pdg_vp] th)) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `w:real^N`; `delta:real`;
                   `(U:real^N->real^N->bool) w`; `(phi:real^N->real^N->real^2) w`;
                   `(rho:real^N->real) w`; `(R1:real^N->real) w`;
                   `(f:real^N->real^3->real^3) w`; `(V:real^N->complex->complex) w`;
                   `(uedge:real^N->(real^N->bool)->complex) w`;
                   `(uart:real^N->(real^N->bool)->complex) w`; `x:real^N`]
           MOI_PDG_VP_DISC) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
    SUBGOAL_THEN `~((phi:real^N->real^N->real^2) w x = vec 0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(norm((phi:real^N->real^N->real^2) w x) < (R1:real^N->real) w)` THEN
      ASM_REWRITE_TAC[NORM_0];
      ALL_TAC] THEN
    ASM_CASES_TAC `?e t. e IN L /\ aff_dim e = &1 /\ w IN e /\ &0 < t /\
                         (phi:real^N->real^N->real^2) w x =
                         Cx t * (uedge:real^N->(real^N->bool)->complex) w e` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `t:real`
        STRIP_ASSUME_TAC)) THEN
      FIRST_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> t = `(uedge:real^N->(real^N->bool)->complex) w`)) (concl th) &&
        not (can (find_term (fun t -> t = `(uart:real^N->(real^N->bool)->complex) w`))
                 (concl th)))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ein") ASSUME_TAC)) THEN
      SUBGOAL_THEN `norm((phi:real^N->real^N->real^2) w x) = t` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) IN e` ASSUME_TAC THENL
       [UNDISCH_TAC `chart_inv((U:real^N->real^N->bool) w,(phi:real^N->real^N->real^2) w)
                       (phi w x) = x` THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        USE_THEN "ein" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `~(x:real^N = w)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((phi:real^N->real^N->real^2) w w = vec 0)` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) IN relative_interior e` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_PDG_EDGE_NEAR_RELINT THEN
        MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `w:real^N`; `delta:real`] THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(x:real^N) IN ball(w,delta)` THEN REWRITE_TAC[IN_BALL];
        ALL_TAC] THEN
      USE_THEN "hedge" (MP_TAC o SPEC `e:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `w':real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                     `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                     `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                     `rho:real^N->real`; `R1:real^N->real`; `f:real^N->real^3->real^3`;
                     `V:real^N->complex->complex`; `uedge:real^N->(real^N->bool)->complex`;
                     `uart:real^N->(real^N->bool)->complex`; `w:real^N`; `w':real^N`;
                     `x:real^N`] MOI_PDG_R1_DISC_UNIQUE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
      UNDISCH_TAC `~(norm((phi:real^N->real^N->real^2) w x) < (R1:real^N->real) w)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `?s t. s IN L /\ aff_dim s = &2 /\ w IN s /\ &0 < t /\
                         (phi:real^N->real^N->real^2) w x =
                         Cx t * (uart:real^N->(real^N->bool)->complex) w s` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `t:real`
        STRIP_ASSUME_TAC)) THEN
      FIRST_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
        is_forall (concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> t = `(uart:real^N->(real^N->bool)->complex) w`)) (concl th) &&
        not (can (find_term (fun t -> t = `(uedge:real^N->(real^N->bool)->complex) w`))
                 (concl th)))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `norm((phi:real^N->real^N->real^2) w x) = t` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `t < (rho:real^N->real) w / &2 -
                         min ((R1:real^N->real) w / &4) ((rho w - R1 w) / &10)` THENL
       [USE_THEN "hart" (MP_TAC o SPECL [`w:real^N`; `s:real^N->bool`; `t:real`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `x = chart_inv((U:real^N->real^N->bool) w,(phi:real^N->real^N->real^2) w)
                            (vec 0 + (uart:real^N->(real^N->bool)->complex) w s * Cx t)`
        (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[VECTOR_ADD_LID] THEN ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `(phi:real^N->real^N->real^2) w x =
                      Cx t * (uart:real^N->(real^N->bool)->complex) w s`)) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_PDG_IMM_ARTRAY THEN
        MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                              `uedge:real^N->(real^N->bool)->complex`;
                              `uart:real^N->(real^N->bool)->complex`; `w:real^N`;
                              `s:real^N->bool`; `t:real`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_PDG_IMM_OFFRAY THEN
    MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`; `w:real^N`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(?e t. e IN L /\ aff_dim e = &1 /\ w IN e /\ &0 < t /\
                          (phi:real^N->real^N->real^2) w x =
                          Cx t * (uedge:real^N->(real^N->bool)->complex) w e)` THEN
      MESON_TAC[];
      UNDISCH_TAC `~(?s t. s IN L /\ aff_dim s = &2 /\ w IN s /\ &0 < t /\
                          (phi:real^N->real^N->real^2) w x =
                          Cx t * (uart:real^N->(real^N->bool)->complex) w s)` THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `x:real^N`] MOI_PDG_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &2 \/ aff_dim s = &1 \/ aff_dim s = &0 \/
                aff_dim s = -- &1` MP_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(s:real^N->bool) IN L`) o check (fun th ->
      concl th = `!t:real^N->bool. t IN L ==> aff_dim t <= &2`)) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC MOI_PDG_IMM_TRI THEN
    MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`; `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "hedge" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                   `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                   `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `w:real^N`]
           MOI_PDG_SETTING_VP) THEN
    ASM_REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(?w. {w} IN L /\ x IN (U:real^N->real^N->bool) w /\
                       norm((phi:real^N->real^N->real^2) w x) < (rho:real^N->real) w)` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN EXISTS_TAC `w:real^N` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [AFF_DIM_EQ_0]) THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior {a}` THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                   `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                   `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                   `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                   `uedge:real^N->(real^N->bool)->complex`;
                   `uart:real^N->(real^N->bool)->complex`; `a:real^N`]
           MOI_PDG_SETTING_VP) THEN
    ASM_REWRITE_TAC[moi_pdg_vp] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(?w. {w} IN L /\ a IN (U:real^N->real^N->bool) w /\
                       norm((phi:real^N->real^N->real^2) w a) < (rho:real^N->real) w)` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(SUBST_ALL_TAC o GEN_REWRITE_RULE I [AFF_DIM_EQ_MINUS1]) THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior {}` THEN
    REWRITE_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY]]);;


(* The crease index set and the assembly of the crease data (MOI_PDG_ASSEMBLE) *)

let moi_pdg_vsel = new_definition
 `moi_pdg_vsel (i:(real^N->bool)#(real^N->bool)) = @w:real^N. SND i = {w}`;;

let MOI_PDG_VSEL = prove
 (`!(s:real^N->bool) w:real^N. moi_pdg_vsel(s,{w}) = w`,
  REWRITE_TAC[moi_pdg_vsel; SND] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_PDG_RELINT_DISJ = prove
 (`!L s t x:real^N.
      simplicial_complex L /\ s IN L /\ t IN L /\
      x IN relative_interior s /\ x IN relative_interior t
      ==> s = t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_PDG_REL_FACE THEN
  MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `x:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_IX_FORALL = prove
 (`!(L:(real^N->bool)->bool) P.
      (!i. i IN {(s,{w}) | s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s} UNION
                {(e,e) | e IN L /\ aff_dim e = &1} ==> P i) <=>
      (!s w. s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s ==> P(s,{w})) /\
      (!e. e IN L /\ aff_dim e = &1 ==> P(e,e))`,
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_PDG_IX_EXISTS2 = prove
 (`!(L:(real^N->bool)->bool) (P:(real^N->bool)#(real^N->bool)->real->bool).
      (?i t. i IN {(s,{w}) | s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s} UNION
                  {(e,e) | e IN L /\ aff_dim e = &1} /\ P i t) <=>
      (?s w t. s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s /\ P (s,{w}) t) \/
      (?e t. e IN L /\ aff_dim e = &1 /\ P (e,e) t)`,
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_PDG_IX_FINITE = prove
 (`!L:(real^N->bool)->bool.
      FINITE L
      ==> FINITE({(s,{w}) | s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s} UNION
                 {(e,e) | e IN L /\ aff_dim e = &1})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(L:(real^N->bool)->bool) CROSS L` THEN ASM_SIMP_TAC[FINITE_CROSS] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_UNION; IN_ELIM_THM; PAIR_EQ] THEN
  MESON_TAC[]);;

let MOI_PDG_PAIR_EXT = prove
 (`!p q:A#B. FST p = FST q /\ SND p = SND q ==> p = q`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

let MOI_PDG_ASM_CREASE = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart Ued phied z0e ce ae be eee Ui phii z0i ci ai bi ei.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      (!e. e IN L /\ aff_dim e = &1
           ==> moi_pdg_crease sigma (moi_pdg_mmap L U phi rho f V h) (Ued e) (phied e) (z0e e) (ce e)
                              (ae e) (be e) (eee e) /\
               (!t. ae e <= t /\ t <= be e
                    ==> chart_inv(Ued e,phied e)(z0e e + ce e * Cx t) IN relative_interior e) /\
               (!x. x IN relative_interior e /\
                    ~(?t. ae e + eee e < t /\ t < be e - eee e /\
                          x = chart_inv(Ued e,phied e)(z0e e + ce e * Cx t))
                    ==> ?w. {w} IN L /\ w IN e /\ x IN U w /\ norm(phi w x) < R1 w)) /\
      (!s w. aff_dim s = &2
             ==> Ui(s,{w}) = U w /\ phii(s,{w}) = phi w /\ z0i(s,{w}) = vec 0 /\
                 ci(s,{w}) = uart w s /\ ai(s,{w}) = R1 w / &2 /\ bi(s,{w}) = rho w / &2 /\
                 ei(s,{w}) = min (R1 w / &4) ((rho w - R1 w) / &10)) /\
      (!e. aff_dim e = &1
           ==> Ui(e,e) = Ued e /\ phii(e,e) = phied e /\ z0i(e,e) = z0e e /\
               ci(e,e) = ce e /\ ai(e,e) = ae e /\ bi(e,e) = be e /\ ei(e,e) = eee e)
      ==> !i. i IN ({(s,{w}) | s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s} UNION
                 {(e,e) | e IN L /\ aff_dim e = &1})
              ==> moi_pdg_crease sigma (moi_pdg_mmap L U phi rho f V h) (Ui i) (phii i) (z0i i) (ci i)
                                 (ai i) (bi i) (ei i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (CONJUNCTS_THEN2 (LABEL_TAC "ec")
    (CONJUNCTS_THEN2 (LABEL_TAC "ha") (LABEL_TAC "he")))) THEN
  REWRITE_TAC[MOI_PDG_IX_FORALL] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `w:real^N`] THEN STRIP_TAC THEN
    USE_THEN "ha" (fun th -> REWRITE_TAC[MATCH_MP (SPECL [`s:real^N->bool`; `w:real^N`] th)
      (ASSUME `aff_dim(s:real^N->bool) = &2`)]) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`; `s:real^N->bool`] MOI_PDG_ART_CREASE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "he" (fun th -> REWRITE_TAC[MATCH_MP (SPEC `e:real^N->bool` th)
      (ASSUME `aff_dim(e:real^N->bool) = &1`)]) THEN
    USE_THEN "ec" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(e:real^N->bool) IN L`) (ASSUME `aff_dim(e:real^N->bool) = &1`)))) THEN
    SIMP_TAC[]]);;

let MOI_PDG_ASM_LOC = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart Ued phied z0e ce ae be eee Ui phii z0i ci ai bi ei.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      (!e. e IN L /\ aff_dim e = &1
           ==> moi_pdg_crease sigma (moi_pdg_mmap L U phi rho f V h) (Ued e) (phied e) (z0e e) (ce e)
                              (ae e) (be e) (eee e) /\
               (!t. ae e <= t /\ t <= be e
                    ==> chart_inv(Ued e,phied e)(z0e e + ce e * Cx t) IN relative_interior e) /\
               (!x. x IN relative_interior e /\
                    ~(?t. ae e + eee e < t /\ t < be e - eee e /\
                          x = chart_inv(Ued e,phied e)(z0e e + ce e * Cx t))
                    ==> ?w. {w} IN L /\ w IN e /\ x IN U w /\ norm(phi w x) < R1 w)) /\
      (!s w. aff_dim s = &2
             ==> Ui(s,{w}) = U w /\ phii(s,{w}) = phi w /\ z0i(s,{w}) = vec 0 /\
                 ci(s,{w}) = uart w s /\ ai(s,{w}) = R1 w / &2 /\ bi(s,{w}) = rho w / &2 /\
                 ei(s,{w}) = min (R1 w / &4) ((rho w - R1 w) / &10)) /\
      (!e. aff_dim e = &1
           ==> Ui(e,e) = Ued e /\ phii(e,e) = phied e /\ z0i(e,e) = z0e e /\
               ci(e,e) = ce e /\ ai(e,e) = ae e /\ bi(e,e) = be e /\ ei(e,e) = eee e)
      ==> !i. i IN ({(s,{w}) | s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s} UNION
                 {(e,e) | e IN L /\ aff_dim e = &1})
              ==> !t. ai i <= t /\ t <= bi i
                ==> FST i IN L /\ chart_inv (Ui i,phii i) (z0i i + ci i * Cx t) IN relative_interior(FST i) /\
                    (aff_dim(FST i) = &2
                     ==> SND i = {moi_pdg_vsel i} /\ {moi_pdg_vsel i} IN L /\
                         chart_inv (Ui i,phii i) (z0i i + ci i * Cx t) IN U(moi_pdg_vsel i) /\
                         norm(phi (moi_pdg_vsel i) (chart_inv (Ui i,phii i) (z0i i + ci i * Cx t))) < rho(moi_pdg_vsel i)) /\
                    (aff_dim(FST i) = &1 ==> SND i = FST i) /\
                    (aff_dim(FST i) = &2 \/ aff_dim(FST i) = &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (CONJUNCTS_THEN2 (LABEL_TAC "ec")
    (CONJUNCTS_THEN2 (LABEL_TAC "ha") (LABEL_TAC "he")))) THEN
  REWRITE_TAC[MOI_PDG_IX_FORALL] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `w:real^N`] THEN STRIP_TAC THEN
    USE_THEN "ha" (fun th -> REWRITE_TAC[MATCH_MP (SPECL [`s:real^N->bool`; `w:real^N`] th)
      (ASSUME `aff_dim(s:real^N->bool) = &2`)]) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`; `w:real^N`; `s:real^N->bool`] MOI_PDG_ART_CREASE) THEN
    ASM_REWRITE_TAC[FST; SND; MOI_PDG_VSEL] THEN
    CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "he" (fun th -> REWRITE_TAC[MATCH_MP (SPEC `e:real^N->bool` th)
      (ASSUME `aff_dim(e:real^N->bool) = &1`)]) THEN
    USE_THEN "ec" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(e:real^N->bool) IN L`) (ASSUME `aff_dim(e:real^N->bool) = &1`)))) THEN
    ASM_REWRITE_TAC[FST; SND] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]]);;

let MOI_PDG_ASM_DISJ = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart Ued phied z0e ce ae be eee Ui phii z0i ci ai bi ei.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      (!e. e IN L /\ aff_dim e = &1
           ==> moi_pdg_crease sigma (moi_pdg_mmap L U phi rho f V h) (Ued e) (phied e) (z0e e) (ce e)
                              (ae e) (be e) (eee e) /\
               (!t. ae e <= t /\ t <= be e
                    ==> chart_inv(Ued e,phied e)(z0e e + ce e * Cx t) IN relative_interior e) /\
               (!x. x IN relative_interior e /\
                    ~(?t. ae e + eee e < t /\ t < be e - eee e /\
                          x = chart_inv(Ued e,phied e)(z0e e + ce e * Cx t))
                    ==> ?w. {w} IN L /\ w IN e /\ x IN U w /\ norm(phi w x) < R1 w)) /\
      (!s w. aff_dim s = &2
             ==> Ui(s,{w}) = U w /\ phii(s,{w}) = phi w /\ z0i(s,{w}) = vec 0 /\
                 ci(s,{w}) = uart w s /\ ai(s,{w}) = R1 w / &2 /\ bi(s,{w}) = rho w / &2 /\
                 ei(s,{w}) = min (R1 w / &4) ((rho w - R1 w) / &10)) /\
      (!e. aff_dim e = &1
           ==> Ui(e,e) = Ued e /\ phii(e,e) = phied e /\ z0i(e,e) = z0e e /\
               ci(e,e) = ce e /\ ai(e,e) = ae e /\ bi(e,e) = be e /\ ei(e,e) = eee e)
      ==> !i j s t. i IN ({(s,{w}) | s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s} UNION
                 {(e,e) | e IN L /\ aff_dim e = &1}) /\
                    j IN ({(s,{w}) | s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s} UNION
                 {(e,e) | e IN L /\ aff_dim e = &1}) /\
                    ~(i = j) /\ ai i <= s /\ s <= bi i /\ ai j <= t /\ t <= bi j
                    ==> ~(chart_inv (Ui i,phii i) (z0i i + ci i * Cx s) = chart_inv (Ui j,phii j) (z0i j + ci j * Cx t))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "loc" o REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] o
    MATCH_MP MOI_PDG_ASM_LOC) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (LABEL_TAC "set") ASSUME_TAC) THEN
  USE_THEN "set" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  MAP_EVERY X_GEN_TAC [`i:(real^N->bool)#(real^N->bool)`; `j:(real^N->bool)#(real^N->bool)`;
                       `p:real`; `q:real`] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  USE_THEN "loc" (MP_TAC o SPECL [`i:(real^N->bool)#(real^N->bool)`; `p:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "i2") (CONJUNCTS_THEN2 (LABEL_TAC "i1") ASSUME_TAC)))) THEN
  USE_THEN "loc" (MP_TAC o SPECL [`j:(real^N->bool)#(real^N->bool)`; `q:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "j2") (CONJUNCTS_THEN2 (LABEL_TAC "j1") ASSUME_TAC)))) THEN
  SUBGOAL_THEN `FST(i:(real^N->bool)#(real^N->bool)) = FST(j:(real^N->bool)#(real^N->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_RELINT_DISJ THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`;
                          `chart_inv ((Ui:(real^N->bool)#(real^N->bool)->real^N->bool) j,
                                     (phii:(real^N->bool)#(real^N->bool)->real^N->real^2) j)
                            ((z0i:(real^N->bool)#(real^N->bool)->complex) j +
                             (ci:(real^N->bool)#(real^N->bool)->complex) j * Cx q)`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `p:real`)) (concl th) &&
      can (find_term (fun t -> t = `q:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(i:(real^N->bool)#(real^N->bool) = j)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_PDG_PAIR_EXT THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term (fun t -> t = `i:(real^N->bool)#(real^N->bool)`)) (concl th))) THENL
   [USE_THEN "i2" (MP_TAC o C MP (ASSUME `aff_dim(FST(i:(real^N->bool)#(real^N->bool))) = &2`)) THEN
    USE_THEN "j2" (MP_TAC o C MP (ASSUME `aff_dim(FST(i:(real^N->bool)#(real^N->bool))) = &2`) o
      REWRITE_RULE[GSYM(ASSUME `FST(i:(real^N->bool)#(real^N->bool)) = FST(j:(real^N->bool)#(real^N->bool))`)]) THEN
    STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `!a b:real^N. {a} = {b} <=> a = b`] THEN
    MATCH_MP_TAC MOI_PDG_DISC_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                          `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                          `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                          `R1:real^N->real`; `f:real^N->real^3->real^3`;
                          `V:real^N->complex->complex`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`;
                          `chart_inv ((Ui:(real^N->bool)#(real^N->bool)->real^N->bool) j,
                                     (phii:(real^N->bool)#(real^N->bool)->real^N->real^2) j)
                            ((z0i:(real^N->bool)#(real^N->bool)->complex) j +
                             (ci:(real^N->bool)#(real^N->bool)->complex) j * Cx q)`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term (fun t -> t = `p:real`)) (concl th) &&
      can (find_term (fun t -> t = `q:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "i1" (MP_TAC o C MP (ASSUME `aff_dim(FST(i:(real^N->bool)#(real^N->bool))) = &1`)) THEN
    USE_THEN "j1" (MP_TAC o C MP (ASSUME `aff_dim(FST(i:(real^N->bool)#(real^N->bool))) = &1`) o
      REWRITE_RULE[GSYM(ASSUME `FST(i:(real^N->bool)#(real^N->bool)) = FST(j:(real^N->bool)#(real^N->bool))`)]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let MOI_PDG_ASM_IMM = prove
 (`!L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart Ued phied z0e ce ae be eee Ui phii z0i ci ai bi ei.
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      (!e. e IN L /\ aff_dim e = &1
           ==> moi_pdg_crease sigma (moi_pdg_mmap L U phi rho f V h) (Ued e) (phied e) (z0e e) (ce e)
                              (ae e) (be e) (eee e) /\
               (!t. ae e <= t /\ t <= be e
                    ==> chart_inv(Ued e,phied e)(z0e e + ce e * Cx t) IN relative_interior e) /\
               (!x. x IN relative_interior e /\
                    ~(?t. ae e + eee e < t /\ t < be e - eee e /\
                          x = chart_inv(Ued e,phied e)(z0e e + ce e * Cx t))
                    ==> ?w. {w} IN L /\ w IN e /\ x IN U w /\ norm(phi w x) < R1 w)) /\
      (!s w. aff_dim s = &2
             ==> Ui(s,{w}) = U w /\ phii(s,{w}) = phi w /\ z0i(s,{w}) = vec 0 /\
                 ci(s,{w}) = uart w s /\ ai(s,{w}) = R1 w / &2 /\ bi(s,{w}) = rho w / &2 /\
                 ei(s,{w}) = min (R1 w / &4) ((rho w - R1 w) / &10)) /\
      (!e. aff_dim e = &1
           ==> Ui(e,e) = Ued e /\ phii(e,e) = phied e /\ z0i(e,e) = z0e e /\
               ci(e,e) = ce e /\ ai(e,e) = ae e /\ bi(e,e) = be e /\ ei(e,e) = eee e)
      ==> !x. x IN UNIONS L /\
              ~(?i t. i IN ({(s,{w}) | s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s} UNION
                 {(e,e) | e IN L /\ aff_dim e = &1}) /\
                      ai i + ei i < t /\ t < bi i - ei i /\
                      x = chart_inv (Ui i,phii i) (z0i i + ci i * Cx t))
              ==> moi_pdg_imm_at sigma (moi_pdg_mmap L U phi rho f V h) x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "set") (CONJUNCTS_THEN2 (LABEL_TAC "ec")
    (CONJUNCTS_THEN2 (LABEL_TAC "ha") (LABEL_TAC "he")))) THEN
  X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[MOI_PDG_IX_EXISTS2] THEN
  REWRITE_TAC[TAUT `~(p \/ q) <=> ~p /\ ~q`; NOT_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "nart") (LABEL_TAC "nedge"))) THEN
  MATCH_MP_TAC MOI_PDG_IMM_OFF THEN
  MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `delta:real`; `R1:real^N->real`;
                        `uedge:real^N->(real^N->bool)->complex`;
                        `uart:real^N->(real^N->bool)->complex`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "ec" (fun th -> MP_TAC(CONJUNCT2(CONJUNCT2(MATCH_MP th
      (CONJ (ASSUME `(e:real^N->bool) IN L`) (ASSUME `aff_dim(e:real^N->bool) = &1`)))))) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `t:real` THEN
      USE_THEN "nedge" (MP_TAC o SPECL [`e:real^N->bool`; `t:real`]) THEN
      USE_THEN "he" (fun th -> REWRITE_TAC[MATCH_MP (SPEC `e:real^N->bool` th)
      (ASSUME `aff_dim(e:real^N->bool) = &1`)]) THEN ASM_REWRITE_TAC[];
      MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`w:real^N`; `s:real^N->bool`; `t:real`] THEN STRIP_TAC THEN
    USE_THEN "nart" (MP_TAC o SPECL [`s:real^N->bool`; `w:real^N`; `t:real`]) THEN
    USE_THEN "ha" (fun th -> REWRITE_TAC[MATCH_MP (SPECL [`s:real^N->bool`; `w:real^N`] th)
      (ASSUME `aff_dim(s:real^N->bool) = &2`)]) THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_ASSEMBLE = prove
 (`!(u:N->bool) L sigma (h:real^N->real^3) h' delta U phi rho R1 f V uedge uart
    Ued phied z0e ce ae be eee.
      MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT u /\
      moi_pdg_setting L sigma h h' delta U phi rho R1 f V uedge uart /\
      (!e. e IN L /\ aff_dim e = &1
           ==> moi_pdg_crease sigma (moi_pdg_mmap L U phi rho f V h) (Ued e) (phied e) (z0e e) (ce e)
                              (ae e) (be e) (eee e) /\
               (!t. ae e <= t /\ t <= be e
                    ==> chart_inv(Ued e,phied e)(z0e e + ce e * Cx t) IN relative_interior e) /\
               (!x. x IN relative_interior e /\
                    ~(?t. ae e + eee e < t /\ t < be e - eee e /\
                          x = chart_inv(Ued e,phied e)(z0e e + ce e * Cx t))
                    ==> ?w. {w} IN L /\ w IN e /\ x IN U w /\ norm(phi w x) < R1 w))
      ==> ?(M:real^N->real^3) M' (ix:(real^N->bool)#(real^N->bool)->bool)
           Ui phii z0i ci ai bi ei.
            homeomorphism (UNIONS L,sphere(vec 0,&1)) (M,M') /\ FINITE ix /\
            (!i. i IN ix
                 ==> moi_pdg_crease sigma M (Ui i) (phii i) (z0i i) (ci i)
                                    (ai i) (bi i) (ei i)) /\
            (!i j s t. i IN ix /\ j IN ix /\ ~(i = j) /\
                       ai i <= s /\ s <= bi i /\ ai j <= t /\ t <= bi j
                       ==> ~(chart_inv (Ui i,phii i) (z0i i + ci i * Cx s) =
                             chart_inv (Ui j,phii j) (z0i j + ci j * Cx t))) /\
            (!x. x IN UNIONS L /\
                 ~(?i t. i IN ix /\ ai i + ei i < t /\ t < bi i - ei i /\
                         x = chart_inv (Ui i,phii i) (z0i i + ci i * Cx t))
                 ==> moi_pdg_imm_at sigma M x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "set") (LABEL_TAC "ec"))) THEN
  USE_THEN "set" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_pdg_setting]) THEN
  MP_TAC(ISPECL ([`u:N->bool`] @ [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`]) MOI_PDG_MMAP_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `M':real^3->real^N`) THEN
  MAP_EVERY EXISTS_TAC ([`moi_pdg_mmap L U phi rho f V (h:real^N->real^3)`; `M':real^3->real^N`;
                         `{(s,{w}) | s IN (L:(real^N->bool)->bool) /\ aff_dim s = &2 /\ {w} IN L /\ w IN s} UNION
                 {(e,e) | e IN L /\ aff_dim e = &1}`] @ [`(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (U:real^N->real^N->bool)(moi_pdg_vsel i) else (Ued:(real^N->bool)->real^N->bool)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (phi:real^N->real^N->real^2)(moi_pdg_vsel i) else (phied:(real^N->bool)->real^N->real^2)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then vec 0 else (z0e:(real^N->bool)->complex)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (uart:real^N->(real^N->bool)->complex)(moi_pdg_vsel i) (FST i) else (ce:(real^N->bool)->complex)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (R1:real^N->real)(moi_pdg_vsel i) / &2 else (ae:(real^N->bool)->real)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (rho:real^N->real)(moi_pdg_vsel i) / &2 else (be:(real^N->bool)->real)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then min ((R1:real^N->real)(moi_pdg_vsel i) / &4) (((rho:real^N->real)(moi_pdg_vsel i) - R1(moi_pdg_vsel i)) / &10) else (eee:(real^N->bool)->real)(FST i))`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PDG_IX_FINITE THEN
    UNDISCH_TAC `simplicial_complex (L:(real^N->bool)->bool)` THEN SIMP_TAC[simplicial_complex];
    MP_TAC(ISPECL ([`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`] @ [`Ued:(real^N->bool)->real^N->bool`; `phied:(real^N->bool)->real^N->real^2`;
                   `z0e:(real^N->bool)->complex`; `ce:(real^N->bool)->complex`;
                   `ae:(real^N->bool)->real`; `be:(real^N->bool)->real`; `eee:(real^N->bool)->real`] @ [`(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (U:real^N->real^N->bool)(moi_pdg_vsel i) else (Ued:(real^N->bool)->real^N->bool)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (phi:real^N->real^N->real^2)(moi_pdg_vsel i) else (phied:(real^N->bool)->real^N->real^2)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then vec 0 else (z0e:(real^N->bool)->complex)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (uart:real^N->(real^N->bool)->complex)(moi_pdg_vsel i) (FST i) else (ce:(real^N->bool)->complex)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (R1:real^N->real)(moi_pdg_vsel i) / &2 else (ae:(real^N->bool)->real)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (rho:real^N->real)(moi_pdg_vsel i) / &2 else (be:(real^N->bool)->real)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then min ((R1:real^N->real)(moi_pdg_vsel i) / &4) (((rho:real^N->real)(moi_pdg_vsel i) - R1(moi_pdg_vsel i)) / &10) else (eee:(real^N->bool)->real)(FST i))`]) MOI_PDG_ASM_CREASE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[FST; SND; MOI_PDG_VSEL] THEN CONJ_TAC THEN
      SIMP_TAC[INT_ARITH `~(&1:int = &2)`];
      REWRITE_TAC[]];
    MP_TAC(ISPECL ([`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`] @ [`Ued:(real^N->bool)->real^N->bool`; `phied:(real^N->bool)->real^N->real^2`;
                   `z0e:(real^N->bool)->complex`; `ce:(real^N->bool)->complex`;
                   `ae:(real^N->bool)->real`; `be:(real^N->bool)->real`; `eee:(real^N->bool)->real`] @ [`(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (U:real^N->real^N->bool)(moi_pdg_vsel i) else (Ued:(real^N->bool)->real^N->bool)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (phi:real^N->real^N->real^2)(moi_pdg_vsel i) else (phied:(real^N->bool)->real^N->real^2)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then vec 0 else (z0e:(real^N->bool)->complex)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (uart:real^N->(real^N->bool)->complex)(moi_pdg_vsel i) (FST i) else (ce:(real^N->bool)->complex)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (R1:real^N->real)(moi_pdg_vsel i) / &2 else (ae:(real^N->bool)->real)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (rho:real^N->real)(moi_pdg_vsel i) / &2 else (be:(real^N->bool)->real)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then min ((R1:real^N->real)(moi_pdg_vsel i) / &4) (((rho:real^N->real)(moi_pdg_vsel i) - R1(moi_pdg_vsel i)) / &10) else (eee:(real^N->bool)->real)(FST i))`]) MOI_PDG_ASM_DISJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[FST; SND; MOI_PDG_VSEL] THEN CONJ_TAC THEN
      SIMP_TAC[INT_ARITH `~(&1:int = &2)`];
      REWRITE_TAC[]];
    MP_TAC(ISPECL ([`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                 `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`; `rho:real^N->real`;
                 `R1:real^N->real`; `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                 `uedge:real^N->(real^N->bool)->complex`;
                 `uart:real^N->(real^N->bool)->complex`] @ [`Ued:(real^N->bool)->real^N->bool`; `phied:(real^N->bool)->real^N->real^2`;
                   `z0e:(real^N->bool)->complex`; `ce:(real^N->bool)->complex`;
                   `ae:(real^N->bool)->real`; `be:(real^N->bool)->real`; `eee:(real^N->bool)->real`] @ [`(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (U:real^N->real^N->bool)(moi_pdg_vsel i) else (Ued:(real^N->bool)->real^N->bool)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (phi:real^N->real^N->real^2)(moi_pdg_vsel i) else (phied:(real^N->bool)->real^N->real^2)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then vec 0 else (z0e:(real^N->bool)->complex)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (uart:real^N->(real^N->bool)->complex)(moi_pdg_vsel i) (FST i) else (ce:(real^N->bool)->complex)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (R1:real^N->real)(moi_pdg_vsel i) / &2 else (ae:(real^N->bool)->real)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then (rho:real^N->real)(moi_pdg_vsel i) / &2 else (be:(real^N->bool)->real)(FST i))`; `(\i:(real^N->bool)#(real^N->bool). if aff_dim(FST i) = &2 then min ((R1:real^N->real)(moi_pdg_vsel i) / &4) (((rho:real^N->real)(moi_pdg_vsel i) - R1(moi_pdg_vsel i)) / &10) else (eee:(real^N->bool)->real)(FST i))`]) MOI_PDG_ASM_IMM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[FST; SND; MOI_PDG_VSEL] THEN CONJ_TAC THEN
      SIMP_TAC[INT_ARITH `~(&1:int = &2)`];
      REWRITE_TAC[]]]);;

(* fs: stage 1 (the map M with its fading creases) and the 2D theorem from the vertex package *)

let MOI_PDG_STAGE1 = prove
 (`!(u:N->bool) L sigma (h:real^N->real^3) h'.
      moi_pdg_vp_statement u /\
      MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT u /\
      MOI_SMO_SURFACE_COMPLEX_STATEMENT u /\
      simplicial_complex L /\
      smooth_manifold_atlas (subtopology euclidean (UNIONS L)) sigma /\
      homeomorphism (UNIONS L,sphere(vec 0,&1)) (h,h') /\
      moi_smo_conical_pd L sigma h
      ==> ?(M:real^N->real^3) M' (ix:(real^N->bool)#(real^N->bool)->bool)
           U phi z0 c a b e.
            homeomorphism (UNIONS L,sphere(vec 0,&1)) (M,M') /\ FINITE ix /\
            (!i. i IN ix
                 ==> moi_pdg_crease sigma M (U i) (phi i) (z0 i) (c i)
                                    (a i) (b i) (e i)) /\
            (!i j s t. i IN ix /\ j IN ix /\ ~(i = j) /\
                       a i <= s /\ s <= b i /\ a j <= t /\ t <= b j
                       ==> ~(chart_inv (U i,phi i) (z0 i + c i * Cx s) =
                             chart_inv (U j,phi j) (z0 j + c j * Cx t))) /\
            (!x. x IN UNIONS L /\
                 ~(?i t. i IN ix /\ a i + e i < t /\ t < b i - e i /\
                         x = chart_inv (U i,phi i) (z0 i + c i * Cx t))
                 ==> moi_pdg_imm_at sigma M x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `L:(real^N->bool)->bool` (GEN_REWRITE_RULE I [MOI_SMO_SURFACE_COMPLEX_STATEMENT]
    (ASSUME `MOI_SMO_SURFACE_COMPLEX_STATEMENT (u:N->bool)`))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `h':real^3->real^N`] THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_PDG_DELTA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?U phi rho R1 f V uedge uart.
                  moi_pdg_vfam L sigma (h:real^N->real^3) delta U phi rho R1 f V uedge uart`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_pdg_vfam; GSYM SKOLEM_THM] THEN X_GEN_TAC `w:real^N` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_pdg_vp_statement (u:N->bool)` THEN
    REWRITE_TAC[moi_pdg_vp_statement] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `h':real^3->real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_pdg_setting L sigma (h:real^N->real^3) h' delta U phi rho R1 f V
                  uedge uart`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[moi_pdg_setting]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?(Ued:(real^N->bool)->real^N->bool) (phied:(real^N->bool)->real^N->real^2)
     (z0e:(real^N->bool)->complex) (ce:(real^N->bool)->complex)
     (ae:(real^N->bool)->real) (be:(real^N->bool)->real) (eee:(real^N->bool)->real).
      (!e:real^N->bool. e IN L /\ aff_dim e = &1
           ==> moi_pdg_crease sigma (moi_pdg_mmap L U phi rho f V h) (Ued e) (phied e) (z0e e) (ce e)
                              (ae e) (be e) (eee e) /\
               (!t. ae e <= t /\ t <= be e
                    ==> chart_inv(Ued e,phied e)(z0e e + ce e * Cx t) IN relative_interior e) /\
               (!x. x IN relative_interior e /\
                    ~(?t. ae e + eee e < t /\ t < be e - eee e /\
                          x = chart_inv(Ued e,phied e)(z0e e + ce e * Cx t))
                    ==> ?w. {w} IN L /\ w IN e /\ x IN U w /\ norm(phi w x) < R1 w))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_PDG_EDGE_CREASE THEN
    MAP_EVERY EXISTS_TAC [`h':real^3->real^N`; `delta:real`;
                          `uedge:real^N->(real^N->bool)->complex`;
                          `uart:real^N->(real^N->bool)->complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_ASSEMBLE THEN
  MAP_EVERY EXISTS_TAC [`u:N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `delta:real`;
                        `U:real^N->real^N->bool`; `phi:real^N->real^N->real^2`;
                        `rho:real^N->real`; `R1:real^N->real`;
                        `f:real^N->real^3->real^3`; `V:real^N->complex->complex`;
                        `uedge:real^N->(real^N->bool)->complex`;
                        `uart:real^N->(real^N->bool)->complex`;
                        `Ued:(real^N->bool)->real^N->bool`;
                        `phied:(real^N->bool)->real^N->real^2`;
                        `z0e:(real^N->bool)->complex`; `ce:(real^N->bool)->complex`;
                        `ae:(real^N->bool)->real`; `be:(real^N->bool)->real`;
                        `eee:(real^N->bool)->real`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_PD2_FROM_VP = prove
 (`!u:N->bool. moi_pdg_vp_statement u /\
              MOI_SMO_CREASE_STATEMENT /\ MOI_SMO_CREASE_ORIENT_STATEMENT /\
              MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT u /\
              MOI_SMO_SURFACE_COMPLEX_STATEMENT u
              ==> MOI_SMO_PD2_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MOI_SMO_PD2_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`L:(real^N->bool)->bool`;
    `sigma:((real^N->bool)#(real^N->real^2))->bool`;
    `h:real^N->real^3`; `h':real^3->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`u:N->bool`; `L:(real^N->bool)->bool`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`] MOI_PDG_STAGE1) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`M:real^N->real^3`; `M':real^3->real^N`;
    `ix:(real^N->bool)#(real^N->bool)->bool`;
    `U:(real^N->bool)#(real^N->bool)->real^N->bool`;
    `phi:(real^N->bool)#(real^N->bool)->real^N->real^2`;
    `z0:(real^N->bool)#(real^N->bool)->complex`;
    `c:(real^N->bool)#(real^N->bool)->complex`;
    `a:(real^N->bool)#(real^N->bool)->real`;
    `b:(real^N->bool)#(real^N->bool)->real`;
    `e:(real^N->bool)#(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `M:real^N->real^3`; `M':real^3->real^N`;
                 `ix:(real^N->bool)#(real^N->bool)->bool`;
                 `U:(real^N->bool)#(real^N->bool)->real^N->bool`;
                 `phi:(real^N->bool)#(real^N->bool)->real^N->real^2`;
                 `z0:(real^N->bool)#(real^N->bool)->complex`;
                 `c:(real^N->bool)#(real^N->bool)->complex`;
                 `a:(real^N->bool)#(real^N->bool)->real`;
                 `b:(real^N->bool)#(real^N->bool)->real`;
                 `e:(real^N->bool)#(real^N->bool)->real`] MOI_PDG_STAGE2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`u:N->bool`; `UNIONS L:real^N->bool`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `M2:real^N->real^3`] MOI_PDG_FINAL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `h:real^N->real^3`;
                 `h':real^3->real^N`] MOI_PDG_X_PROPS) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Planar tools for the vertex package: angle maps moi_pdg_angf (polar form, norm, homogeneity, smoothness, Jacobian k), 2-cones moi_pdg_cone2 (coordinates, closed, convex, conic, angular description) *)

let moi_pdg_tk = new_definition
 `moi_pdg_tk (k:real) (w:complex) = Cx(Re w) + ii * Cx(k * Im w)`;;

let moi_pdg_angf = new_definition
 `moi_pdg_angf (k:real) (c:real) (y:complex) =
    cexp(ii * Cx(k * c)) * cexp(moi_pdg_tk k (clog(cexp(--(ii * Cx c)) * y)))`;;

let moi_pdg_cone2 = new_definition
 `moi_pdg_cone2 (u:complex) (v:complex) = {a % u + b % v | &0 <= a /\ &0 <= b}`;;

let MOI_PDG_ANGF_POLAR = prove
 (`!k c r t. &0 < r /\ --pi < t /\ t <= pi
             ==> moi_pdg_angf k c (Cx r * cexp(ii * Cx(c + t))) =
                 Cx r * cexp(ii * Cx(k * (c + t)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_angf] THEN
  SUBGOAL_THEN `cexp(--(ii * Cx c)) * Cx r * cexp(ii * Cx(c + t)) =
                cexp(Cx(log r) + ii * Cx t)` SUBST1_TAC THENL
   [REWRITE_TAC[CEXP_ADD; GSYM CX_EXP; CX_ADD; COMPLEX_ADD_LDISTRIB] THEN
    ASM_SIMP_TAC[EXP_LOG] THEN
    MP_TAC(SPEC `ii * Cx c` CEXP_NEG_LMUL) THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `clog(cexp(Cx(log r) + ii * Cx t)) = Cx(log r) + ii * Cx t` SUBST1_TAC THENL
   [MATCH_MP_TAC CLOG_CEXP THEN
    ASM_REWRITE_TAC[IM_ADD; IM_CX; IM_MUL_II; RE_CX; REAL_ADD_LID];
    ALL_TAC] THEN
  REWRITE_TAC[moi_pdg_tk; RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_II; IM_MUL_II] THEN
  REWRITE_TAC[REAL_NEG_0; REAL_ADD_RID; REAL_ADD_LID] THEN
  REWRITE_TAC[CEXP_ADD; GSYM CX_EXP] THEN ASM_SIMP_TAC[EXP_LOG] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  CONV_TAC COMPLEX_RING);;

let MOI_PDG_POLAR_FORM = prove
 (`!c y. ~(y = Cx(&0))
         ==> ?t. --pi < t /\ t <= pi /\ y = Cx(norm y) * cexp(ii * Cx(c + t))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u = cexp(--(ii * Cx c)) * y` THEN
  SUBGOAL_THEN `~(u = Cx(&0)) /\ norm(u:complex) = norm(y:complex)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN ASM_REWRITE_TAC[COMPLEX_ENTIRE; CEXP_NZ; COMPLEX_NORM_MUL] THEN
    REWRITE_TAC[NORM_CEXP; RE_NEG; RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0;
                REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `y = cexp(ii * Cx c) * u` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN MP_TAC(SPEC `ii * Cx c` CEXP_NEG_RMUL) THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(SPEC `u:complex` CLOG_WORKS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `Im(clog u)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; REAL_MUL_LID] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(ASSUME `cexp(clog u) = u`)] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
  ASM_SIMP_TAC[RE_CLOG; CEXP_ADD; GSYM CX_EXP; EXP_LOG; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN CONV_TAC COMPLEX_RING);;

let MOI_PDG_ANGF_NORM = prove
 (`!k c y. ~(y = Cx(&0)) ==> norm(moi_pdg_angf k c y) = norm y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `y:complex`] MOI_PDG_POLAR_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  ASM_SIMP_TAC[MOI_PDG_ANGF_POLAR; COMPLEX_NORM_NZ] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ABS_NORM]);;

let MOI_PDG_ANGF_HOMOG = prove
 (`!k c s y. &0 < s /\ ~(y = Cx(&0))
             ==> moi_pdg_angf k c (Cx s * y) = Cx s * moi_pdg_angf k c y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `y:complex`] MOI_PDG_POLAR_FORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
  ASM_SIMP_TAC[MOI_PDG_ANGF_POLAR; COMPLEX_NORM_NZ; REAL_LT_MUL] THEN
  REWRITE_TAC[CX_MUL; COMPLEX_MUL_ASSOC]);;

let MOI_PDG_ANG_EQ_ANGF = prove
 (`!k b y. ~(y = Cx(&0)) /\ &0 <= Im(cexp(--(ii * Cx b)) * y)
           ==> moi_smo_ang k b y = moi_pdg_angf k (b + pi / &2) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_smo_ang] THEN
  ABBREV_TAC `v = cexp(--(ii * Cx b)) * y` THEN
  SUBGOAL_THEN `y = cexp(ii * Cx b) * v` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN MP_TAC(SPEC `ii * Cx b` CEXP_NEG_RMUL) THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Arg v /\ Arg v <= pi` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARG_LE_PI; ARG]; ALL_TAC] THEN
  SUBGOAL_THEN `y = Cx(norm y) * cexp(ii * Cx((b + pi / &2) + (Arg v - pi / &2)))`
  (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th -> concl th = `y = cexp(ii * Cx b) * v`)) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; REAL_MUL_LID] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONJUNCT2(CONJUNCT2(SPEC `v:complex` ARG))] THEN
    REWRITE_TAC[REAL_ARITH `(b + pi / &2) + (a - pi / &2) = b + a`] THEN
    REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real`; `b + pi / &2`; `norm(y:complex)`; `Arg v - pi / &2`]
         MOI_PDG_ANGF_POLAR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_NORM_NZ] THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(b + pi / &2) + (a - pi / &2) = b + a`]);;

let MOI_PDG_LINEAR_TK = prove
 (`!k. linear(moi_pdg_tk k)`,
  GEN_TAC THEN
  REWRITE_TAC[linear; moi_pdg_tk; COMPLEX_CMUL; RE_ADD; IM_ADD; RE_MUL_CX; IM_MUL_CX;
              CX_ADD; CX_MUL; REAL_ADD_LDISTRIB] THEN
  CONV_TAC COMPLEX_RING);;

let MOI_PDG_SLIT_OPEN = prove
 (`open {u:complex | Im u = &0 ==> &0 < Re u}`,
  REWRITE_TAC[OPEN_CLOSED] THEN
  SUBGOAL_THEN `(:complex) DIFF {u:complex | Im u = &0 ==> &0 < Re u} =
                {z | real z} INTER {z | Re z <= &0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_INTER; IN_ELIM_THM; real] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[CLOSED_REAL_SET; CLOSED_HALFSPACE_RE_LE]]);;

let MOI_PDG_ANGF_COMP = prove
 (`!k c. moi_pdg_angf k c =
         (\x. cexp(ii * Cx(k * c)) * x) o cexp o moi_pdg_tk k o clog o
         (\y. cexp(--(ii * Cx c)) * y)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; moi_pdg_angf]);;

let MOI_PDG_ANGF_SMOOTH = prove
 (`!k c s. open s /\
           (!y. y IN s /\ Im(cexp(--(ii * Cx c)) * y) = &0
                ==> &0 < Re(cexp(--(ii * Cx c)) * y))
           ==> smooth_map_on s (moi_pdg_angf k c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_PDG_ANGF_COMP] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:complex)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN REWRITE_TAC[OPEN_UNIV; LINEAR_COMPLEX_MUL]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:complex)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_PDG_HOLO_SMOOTH THEN REWRITE_TAC[OPEN_UNIV; HOLOMORPHIC_ON_CEXP]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:complex)` THEN
  ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN REWRITE_TAC[OPEN_UNIV; MOI_PDG_LINEAR_TK]] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `{u:complex | Im u = &0 ==> &0 < Re u}` THEN
  ASM_REWRITE_TAC[MOI_PDG_SLIT_OPEN] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[LINEAR_COMPLEX_MUL];
    MATCH_MP_TAC MOI_PDG_HOLO_SMOOTH THEN REWRITE_TAC[MOI_PDG_SLIT_OPEN] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_CLOG THEN SIMP_TAC[IN_ELIM_THM]]);;

let MOI_PDG_JAC_LINEAR = prove
 (`!(f:real^M->real^N) x. linear f ==> jacobian f (at x) = matrix f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[jacobian] THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR]);;

let MOI_PDG_DET_TK = prove
 (`!k x. det(jacobian (moi_pdg_tk k) (at x)) = k`,
  REPEAT GEN_TAC THEN SIMP_TAC[MOI_PDG_JAC_LINEAR; MOI_PDG_LINEAR_TK] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOI_PDG_DET_FIX1 o lhand o snd) THEN
  REWRITE_TAC[MOI_PDG_LINEAR_TK; moi_pdg_tk; RE_CX; IM_CX; RE_II; IM_II] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_MUL_RZERO; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IM_ADD; IM_CX; IM_MUL_II; RE_CX; REAL_MUL_RID; REAL_ADD_LID]]);;

let MOI_PDG_DET_CMUL = prove
 (`!c x. det(jacobian (\z:complex. c * z) (at x)) = norm(c) pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC JACOBIAN_COMPLEX_DERIVATIVE THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_LINEAR]);;

let MOI_PDG_DET_CEXP = prove
 (`!z. det(jacobian cexp (at z)) = norm(cexp z) pow 2`,
  GEN_TAC THEN MATCH_MP_TAC JACOBIAN_COMPLEX_DERIVATIVE THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CEXP]);;

let MOI_PDG_ANGF_DET = prove
 (`!k c y. (Im(cexp(--(ii * Cx c)) * y) = &0 ==> &0 < Re(cexp(--(ii * Cx c)) * y))
           ==> det(jacobian (moi_pdg_angf k c) (at y)) = k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_PDG_ANGF_COMP] THEN
  ABBREV_TAC `u = cexp(--(ii * Cx c)) * y` THEN
  ABBREV_TAC `f1 = \y:complex. cexp(--(ii * Cx c)) * y` THEN
  SUBGOAL_THEN `(f1:complex->complex) y = u` ASSUME_TAC THENL
   [EXPAND_TAC "f1" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(u = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `Im u = &0 ==> &0 < Re u` THEN
    ASM_REWRITE_TAC[RE_CX; IM_CX; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(clog has_complex_derivative inv u) (at u)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_CLOG THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `det(jacobian clog (at u)) = norm(inv u) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC JACOBIAN_COMPLEX_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `clog differentiable at u` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE THEN
    REWRITE_TAC[complex_differentiable] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f1:complex->complex) differentiable at y /\
                det(jacobian f1 (at y)) = &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f1" THEN
    SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_COMPLEX_MUL; MOI_PDG_DET_CMUL] THEN
    REWRITE_TAC[NORM_CEXP; RE_NEG; RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `w = moi_pdg_tk k (clog u)` THEN
  SUBGOAL_THEN `norm(cexp w) = norm(u:complex)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    REWRITE_TAC[NORM_CEXP; moi_pdg_tk; RE_ADD; RE_CX; RE_MUL_II; IM_CX; REAL_NEG_0;
                REAL_ADD_RID] THEN
    ASM_SIMP_TAC[RE_CLOG; EXP_LOG; COMPLEX_NORM_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f1:complex->complex`; `clog`; `y:complex`] MOI_PDG_DET_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[JACOBIAN_COMPLEX_DERIVATIVE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(clog o (f1:complex->complex)) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`clog o (f1:complex->complex)`; `moi_pdg_tk k`; `y:complex`]
         MOI_PDG_DET_CHAIN) THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; MOI_PDG_LINEAR_TK; MOI_PDG_DET_TK] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(moi_pdg_tk k o clog o (f1:complex->complex)) differentiable at y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; MOI_PDG_LINEAR_TK];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_pdg_tk k o clog o (f1:complex->complex)`; `cexp`; `y:complex`]
         MOI_PDG_DET_CHAIN) THEN
  ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_AT_CEXP;
               MOI_PDG_DET_CEXP; o_THM] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(cexp o moi_pdg_tk k o clog o (f1:complex->complex)) differentiable at y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN
    ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE;
                 COMPLEX_DIFFERENTIABLE_AT_CEXP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cexp o moi_pdg_tk k o clog o (f1:complex->complex)`;
                 `\x. cexp(ii * Cx(k * c)) * x`; `y:complex`] MOI_PDG_DET_CHAIN) THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; LINEAR_COMPLEX_MUL; MOI_PDG_DET_CMUL] THEN
  REWRITE_TAC[NORM_CEXP_II] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[o_THM] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_INV] THEN
  UNDISCH_TAC `~(u = Cx(&0))` THEN REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN
  CONV_TAC REAL_FIELD);;

let MOI_PDG_IM_CNJ_MUL = prove
 (`!u v:complex. Im(cnj u * v) = Re u * Im v - Im u * Re v`,
  REWRITE_TAC[cnj; complex_mul; RE; IM] THEN REAL_ARITH_TAC);;

let MOI_PDG_CONE2_COORDS = prove
 (`!u v x:complex.
      ~(Im(cnj u * v) = &0)
      ==> x = (Im(cnj v * x) / Im(cnj v * u)) % u + (Im(cnj u * x) / Im(cnj u * v)) % v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_PDG_IM_CNJ_MUL] THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; COMPLEX_CMUL; RE_MUL_CX; IM_MUL_CX] THEN
  CONJ_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

let MOI_PDG_IM_CNJ_LIN = prove
 (`!w u v:complex a b.
      Im(cnj w * (a % u + b % v)) = a * Im(cnj w * u) + b * Im(cnj w * v)`,
  REWRITE_TAC[MOI_PDG_IM_CNJ_MUL; COMPLEX_CMUL; RE_ADD; IM_ADD; RE_MUL_CX; IM_MUL_CX] THEN
  REAL_ARITH_TAC);;

let MOI_PDG_IM_CNJ_SELF = prove
 (`!v:complex. Im(cnj v * v) = &0`,
  REWRITE_TAC[MOI_PDG_IM_CNJ_MUL] THEN REAL_ARITH_TAC);;

let MOI_PDG_IN_CONE2 = prove
 (`!u v x:complex.
      ~(Im(cnj u * v) = &0)
      ==> (x IN moi_pdg_cone2 u v <=>
           &0 <= Im(cnj v * x) / Im(cnj v * u) /\ &0 <= Im(cnj u * x) / Im(cnj u * v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(Im(cnj v * u) = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(Im(cnj u * v) = &0)` THEN REWRITE_TAC[MOI_PDG_IM_CNJ_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_pdg_cone2; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[MOI_PDG_IM_CNJ_LIN; MOI_PDG_IM_CNJ_SELF] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_ADD_LID] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(y = &0) ==> (a * y) / y = a`];
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Im(cnj v * x) / Im(cnj v * u)`; `Im(cnj u * x) / Im(cnj u * v)`] THEN
    ASM_SIMP_TAC[GSYM MOI_PDG_CONE2_COORDS]]);;

let MOI_PDG_CONE2_CONIC = prove
 (`!u v:complex. conic(moi_pdg_cone2 u v)`,
  REWRITE_TAC[conic; moi_pdg_cone2; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`c * a:real`; `c * b:real`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL] THEN VECTOR_ARITH_TAC);;

let MOI_PDG_CONE2_CONVEX = prove
 (`!u v:complex. convex(moi_pdg_cone2 u v)`,
  REWRITE_TAC[convex; moi_pdg_cone2; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`u' * a + v' * a':real`; `u' * b + v' * b':real`] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL] THEN VECTOR_ARITH_TAC);;

let MOI_PDG_CLOSED_IMCNJ = prove
 (`!w:complex d. closed {x:complex | &0 <= Im(cnj w * x) / d}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x:complex | &0 <= Im(cnj w * x) / d} =
                {x | vector[--(Im w / d); Re w / d] dot x >= &0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_2; VECTOR_2; MOI_PDG_IM_CNJ_MUL;
                RE_DEF; IM_DEF; real_div] THEN REAL_ARITH_TAC;
    REWRITE_TAC[CLOSED_HALFSPACE_GE]]);;

let MOI_PDG_CONE2_CLOSED = prove
 (`!u v:complex. ~(Im(cnj u * v) = &0) ==> closed(moi_pdg_cone2 u v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_pdg_cone2 u v =
                {x:complex | &0 <= Im(cnj v * x) / Im(cnj v * u)} INTER
                {x:complex | &0 <= Im(cnj u * x) / Im(cnj u * v)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN ASM_SIMP_TAC[MOI_PDG_IN_CONE2];
    MATCH_MP_TAC CLOSED_INTER THEN REWRITE_TAC[MOI_PDG_CLOSED_IMCNJ]]);;

let MOI_PDG_CNJ_CEXP_II = prove
 (`!a. cnj(cexp(ii * Cx a)) = cexp(--(ii * Cx a))`,
  REWRITE_TAC[CNJ_CEXP; CNJ_MUL; CNJ_II; CNJ_CX; COMPLEX_MUL_LNEG]);;

let MOI_PDG_IM_CNJ_POLAR = prove
 (`!a b r. Im(cnj(cexp(ii * Cx a)) * (Cx r * cexp(ii * Cx b))) = r * sin(b - a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_PDG_CNJ_CEXP_II] THEN
  SUBGOAL_THEN `cexp(--(ii * Cx a)) * (Cx r * cexp(ii * Cx b)) =
                Cx r * cexp(ii * Cx(b - a))` SUBST1_TAC THENL
   [REWRITE_TAC[CX_SUB; complex_sub; COMPLEX_ADD_LDISTRIB; COMPLEX_MUL_RNEG; CEXP_ADD] THEN
    CONV_TAC COMPLEX_RING;
    REWRITE_TAC[IM_MUL_CX; IM_CEXP; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID]]);;

let MOI_PDG_DIV_SIGN = prove
 (`!x s. &0 < s ==> ((&0 <= x / s <=> &0 <= x) /\ (&0 <= x / --s <=> x <= &0))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_RNEG] THEN REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= --a <=> a <= &0`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]);;

let MOI_PDG_CONE2_ANGLE = prove
 (`!a d x. &0 < d /\ d < pi
           ==> (x IN moi_pdg_cone2 (cexp(ii * Cx a)) (cexp(ii * Cx(a + d))) <=>
                x = Cx(&0) \/
                ?r t. &0 < r /\ &0 <= t /\ t <= d /\ x = Cx r * cexp(ii * Cx(a + t)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sin d` ASSUME_TAC THENL
   [MATCH_MP_TAC SIN_POS_PI THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `Im(cnj(cexp(ii * Cx a)) * cexp(ii * Cx(a + d))) = sin d /\
                Im(cnj(cexp(ii * Cx(a + d))) * cexp(ii * Cx a)) = --sin d`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real`; `a + d:real`; `&1`] MOI_PDG_IM_CNJ_POLAR) THEN
    MP_TAC(ISPECL [`a + d:real`; `a:real`; `&1`] MOI_PDG_IM_CNJ_POLAR) THEN
    REWRITE_TAC[COMPLEX_MUL_LID; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ARITH `a - (a + d) = --d /\ (a + d) - a = d`; SIN_NEG] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Im(cnj(cexp(ii * Cx a)) * cexp(ii * Cx(a + d))) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_PDG_IN_CONE2] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOI_PDG_DIV_SIGN] THEN EQ_TAC THENL
   [ASM_CASES_TAC `x = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`a:real`; `x:complex`] MOI_PDG_POLAR_FORM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < norm(x:complex)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
    ABBREV_TAC `r = norm(x:complex)` THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `x:complex`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MOI_PDG_IM_CNJ_POLAR;
      REAL_ARITH `(a + t) - a = t /\ (a + t) - (a + d) = t - d`]) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
     [MP_TAC(SPEC `--t` SIN_POS_PI) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SIN_NEG] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`r:real`; `--sin t`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `t - d` SIN_POS_PI) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN
      MP_TAC(SPECL [`r:real`; `sin(t - d)`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    STRIP_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; IM_CX; REAL_LE_REFL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[MOI_PDG_IM_CNJ_POLAR] THEN
    REWRITE_TAC[REAL_ARITH `(a + t) - a = t /\ (a + t) - (a + d) = --(d - t)`; SIN_NEG] THEN
    SUBGOAL_THEN `&0 <= sin t /\ &0 <= sin(d - t)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SIN_POS_PI_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_RNEG; REAL_ARITH `--a <= &0 <=> &0 <= a`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;


(* The corner of a triangle (vertex package): parametrisation moi_pdg_tpar, edge directions, local inverse at the corner (MOI_PDG_CORNER_LOCAL), compactness and edge onto lemmas, MOI_PDG_CORNER_PREP *)

let moi_pdg_tpar = new_definition
 `moi_pdg_tpar (w:real^N) v1 v2 (y:complex) = w + Re y % (v1 - w) + Im y % (v2 - w)`;;

let MOI_PDG_TPAR_HULL = prove
 (`!(w:real^N) v1 v2 x.
      x IN convex hull {w,v1,v2} <=>
      ?y. &0 <= Re y /\ &0 <= Im y /\ Re y + Im y <= &1 /\ moi_pdg_tpar w v1 v2 y = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_3_ALT; IN_ELIM_THM; moi_pdg_tpar] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `complex(a,b)` THEN ASM_REWRITE_TAC[RE; IM];
    DISCH_THEN(X_CHOOSE_THEN `y:complex` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`Re y`; `Im y`] THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_TPAR_0 = prove
 (`!(w:real^N) v1 v2. moi_pdg_tpar w v1 v2 (vec 0) = w`,
  REWRITE_TAC[moi_pdg_tpar; COMPLEX_VEC_0; RE_CX; IM_CX] THEN VECTOR_ARITH_TAC);;

let MOI_PDG_TPAR_DERIV = prove
 (`!(w:real^N) v1 v2 y.
      (moi_pdg_tpar w v1 v2 has_derivative (\y. Re y % (v1 - w) + Im y % (v2 - w))) (at y)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `moi_pdg_tpar (w:real^N) v1 v2 =
                (\y. w + (\y. Re y % (v1 - w) + Im y % (v2 - w)) y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_pdg_tpar]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_AFFINE_DERIV THEN REWRITE_TAC[MOI_PDG_LIN_RE_IM]);;

let MOI_PDG_TPAR_SMOOTH = prove
 (`!(w:real^N) v1 v2 s. open s ==> smooth_map_on s (moi_pdg_tpar w v1 v2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_pdg_tpar (w:real^N) v1 v2 =
                (\y. w + (\y. Re y % (v1 - w) + Im y % (v2 - w)) y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_pdg_tpar]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_AFFINE_SMOOTH THEN ASM_REWRITE_TAC[MOI_PDG_LIN_RE_IM]);;

let MOI_PDG_TPAR_LIN_INJ = prove
 (`!(w:real^N) v1 v2.
      ~(v1 = w) /\ ~(v2 = w) /\ ~(v1 = v2) /\ ~(affine_dependent {w,v1,v2})
      ==> !y. Re y % (v1 - w) + Im y % (v2 - w) = vec 0 ==> y = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_LIN_INDEP_TRI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`Re y`; `Im y`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_EQ; COMPLEX_VEC_0; RE_CX; IM_CX]);;

let MOI_PDG_TPAR_INJ = prove
 (`!(w:real^N) v1 v2 y y'.
      ~(v1 = w) /\ ~(v2 = w) /\ ~(v1 = v2) /\ ~(affine_dependent {w,v1,v2}) /\
      moi_pdg_tpar w v1 v2 y = moi_pdg_tpar w v1 v2 y'
      ==> y = y'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_TPAR_LIN_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y - y':complex`) THEN
  REWRITE_TAC[RE_SUB; IM_SUB; VECTOR_SUB_RDISTRIB; VECTOR_SUB_EQ] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `moi_pdg_tpar (w:real^N) v1 v2 y = moi_pdg_tpar w v1 v2 y'` THEN
  REWRITE_TAC[moi_pdg_tpar] THEN VECTOR_ARITH_TAC);;

let MOI_PDG_TPAR_BOUND = prove
 (`!(w:real^N) v1 v2.
      ~(v1 = w) /\ ~(v2 = w) /\ ~(v1 = v2) /\ ~(affine_dependent {w,v1,v2})
      ==> ?B. &0 < B /\ !y. B * norm y <= norm(moi_pdg_tpar w v1 v2 y - w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\y:complex. Re y % (v1 - w) + Im y % (v2 - w:real^N)`
    LINEAR_INJECTIVE_BOUNDED_BELOW_POS) THEN
  REWRITE_TAC[MOI_PDG_LIN_RE_IM] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:complex`; `y':complex`] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_PDG_TPAR_INJ THEN
    MAP_EVERY EXISTS_TAC [`w:real^N`; `v1:real^N`; `v2:real^N`] THEN
    ASM_REWRITE_TAC[moi_pdg_tpar] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `B:real` THEN
    ASM_REWRITE_TAC[moi_pdg_tpar; VECTOR_ARITH `(w + a) - w:real^N = a`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_TPAR_EDGES = prove
 (`!(w:real^N) v1 v2 t.
      &0 <= t /\ t <= &1
      ==> moi_pdg_tpar w v1 v2 (Cx t) IN segment[w,v1] /\
          moi_pdg_tpar w v1 v2 (ii * Cx t) IN segment[w,v2]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_tpar; IN_SEGMENT] THEN
  EXISTS_TAC `t:real` THEN
  ASM_REWRITE_TAC[RE_CX; IM_CX; RE_MUL_II; IM_MUL_II; REAL_NEG_0] THEN VECTOR_ARITH_TAC);;

let MOI_PDG_EDGE_DIR = prove
 (`!(G:complex->complex) D a v d.
      (G has_derivative D) (at (vec 0)) /\ G(vec 0) = vec 0 /\ ~(a = vec 0) /\
      &0 < d /\ (!t. &0 <= t /\ t < d ==> ?s. &0 <= s /\ G(t % v) = s % a) /\
      ~(D v = vec 0)
      ==> ?c. &0 < c /\ D v = c % a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t. &0 < t /\ t < d
                    ==> Im(cnj a * (G:complex->complex)(t % v)) = &0 /\
                        &0 <= Re(cnj a * G(t % v))` (LABEL_TAC "ray") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `d:real`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_CMUL; COMPLEX_RING `cnj a * Cx s * a = Cx s * (cnj a * a)`] THEN
    REWRITE_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW; GSYM CX_MUL; RE_CX; IM_CX] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `Im(cnj a * (D:complex->complex) v) = &0` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x = &0 <=> ~(&0 < x) /\ ~(&0 < --x)`] THEN CONJ_TAC THEN
    DISCH_TAC THENL
     [MP_TAC(ISPECL [`G:complex->complex`; `D:complex->complex`; `v:complex`;
                     `--ii * cnj a`] MOI_PDG_FIRST_ORDER);
      MP_TAC(ISPECL [`G:complex->complex`; `D:complex->complex`; `v:complex`;
                     `ii * cnj a`] MOI_PDG_FIRST_ORDER)] THEN
    REWRITE_TAC[COMPLEX_RING `(--ii * c) * x = --(ii * (c * x))`;
                COMPLEX_RING `(ii * c) * x = ii * (c * x)`; RE_NEG; RE_MUL_II;
                REAL_NEG_NEG] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t0"))) THEN
    USE_THEN "t0" (MP_TAC o SPEC `min (t0 / &2) (d / &2)`) THEN
    USE_THEN "ray" (MP_TAC o SPEC `min (t0 / &2) (d / &2)`) THEN
    REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Re(cnj a * (D:complex->complex) v)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:complex->complex`; `D:complex->complex`; `v:complex`;
                   `--cnj a`] MOI_PDG_FIRST_ORDER) THEN
    REWRITE_TAC[COMPLEX_MUL_LNEG; RE_NEG] THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < --x <=> x < &0`] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t0"))) THEN
    USE_THEN "t0" (MP_TAC o SPEC `min (t0 / &2) (d / &2)`) THEN
    USE_THEN "ray" (MP_TAC o SPEC `min (t0 / &2) (d / &2)`) THEN
    REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = Re(cnj a * (D:complex->complex) v)` THEN
  SUBGOAL_THEN `cnj a * (D:complex->complex) v = Cx r` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(a:complex)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(D:complex->complex) v = Cx(r / norm a pow 2) * a` ASSUME_TAC THENL
   [SUBGOAL_THEN `Cx(norm(a:complex)) pow 2 * (D:complex->complex) v = Cx r * a` MP_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_MUL_CNJ] THEN
      FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) o
        check (fun th -> concl th = `cnj a * (D:complex->complex) v = Cx r`)) THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    REWRITE_TAC[CX_DIV; CX_POW] THEN
    SUBGOAL_THEN `~(Cx(norm(a:complex)) pow 2 = Cx(&0))` MP_TAC THENL
     [REWRITE_TAC[COMPLEX_POW_EQ_0; CX_INJ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  EXISTS_TAC `r / norm(a:complex) pow 2` THEN ASM_REWRITE_TAC[COMPLEX_CMUL] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((D:complex->complex) v = vec 0)` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `&0 = r`)) THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]);;

let MOI_PDG_LIN_COORD_INJ = prove
 (`!u1 u2:complex a b.
      ~(Im(cnj u1 * u2) = &0) /\ a % u1 + b % u2 = vec 0 ==> a = &0 /\ b = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o AP_TERM `\x:complex. Im(cnj u1 * x)`) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\x:complex. Im(cnj u2 * x)`) THEN
  REWRITE_TAC[MOI_PDG_IM_CNJ_LIN; MOI_PDG_IM_CNJ_SELF; COMPLEX_VEC_0;
              COMPLEX_MUL_RZERO; IM_CX] THEN
  UNDISCH_TAC `~(Im(cnj u1 * u2) = &0)` THEN
  REWRITE_TAC[MOI_PDG_IM_CNJ_MUL] THEN CONV_TAC REAL_FIELD);;

let MOI_PDG_CORNER_LOCAL = prove
 (`!(G:complex->complex) P r1 u1 u2 c1 c2.
      open P /\ &0 < r1 /\ ball(vec 0,r1) SUBSET P /\ smooth_map_on P G /\
      G(vec 0) = vec 0 /\
      &0 < c1 /\ &0 < c2 /\ ~(Im(cnj u1 * u2) = &0) /\
      frechet_derivative G (at (vec 0)) (Cx(&1)) = Cx c1 * u1 /\
      frechet_derivative G (at (vec 0)) ii = Cx c2 * u2 /\
      (!p. &0 <= p /\ p < r1 ==> ?t. &0 <= t /\ G(Cx p) = Cx t * u1) /\
      (!p. &0 <= p /\ p < r1 ==> ?t. &0 <= t /\ G(ii * Cx p) = Cx t * u2)
      ==> ?rho ginv r.
            &0 < rho /\ smooth_map_on (ball(vec 0,rho)) ginv /\
            (!y. y IN ball(vec 0,rho) ==> norm(ginv y) < r1 /\ G(ginv y) = y) /\
            (!y z. y IN ball(vec 0,rho) /\ frechet_derivative ginv (at y) z = vec 0
                   ==> z = vec 0) /\
            (!y. y IN ball(vec 0,rho)
                 ==> (y IN moi_pdg_cone2 u1 u2 <=>
                      &0 <= Re(ginv y) /\ &0 <= Im(ginv y))) /\
            &0 < r /\ (!x. norm x < r ==> norm(G x) < rho /\ ginv(G x) = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(G:complex->complex) differentiable at (vec 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `P:complex->bool` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ball(vec 0:complex,r1) SUBSET P` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `DG = frechet_derivative (G:complex->complex) (at (vec 0))` THEN
  SUBGOAL_THEN `linear(DG:complex->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "DG" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (DG:complex->complex) z = (Re z * c1) % u1 + (Im z * c2) % u2`
  (LABEL_TAC "dg") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `z = Re z % Cx(&1) + Im z % ii`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; COMPLEX_CMUL; RE_MUL_CX; IM_MUL_CX;
                  RE_CX; IM_CX; RE_II; IM_II] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
    ASM_REWRITE_TAC[COMPLEX_CMUL; CX_MUL] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (Re z * c1) % u1 + (Im z * c2) % u2 = vec 0 ==> z = vec 0`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`u1:complex`; `u2:complex`; `Re z * c1`; `Im z * c2`]
      MOI_PDG_LIN_COORD_INJ) THEN
    ASM_REWRITE_TAC[REAL_ENTIRE] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[COMPLEX_EQ; COMPLEX_VEC_0; RE_CX; IM_CX] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (DG:complex->complex) z = vec 0 ==> z = vec 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(det(matrix(DG:complex->complex)) = &0)` ASSUME_TAC THENL
   [EXPAND_TAC "DG" THEN REWRITE_TAC[GSYM jacobian] THEN
    MATCH_MP_TAC MOI_PDG_DET_NZ_INJ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:complex->complex`; `ball(vec 0:complex,r1)`; `vec 0:complex`]
         SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `P:complex->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:complex->bool` (X_CHOOSE_THEN `u:complex->bool`
    (X_CHOOSE_THEN `ginv:complex->complex`
      (STRIP_ASSUME_TAC o REWRITE_RULE[diffeomorphism_on])))) THEN
  SUBGOAL_THEN `vec 0:complex IN u` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:complex` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> concl th = `open(u:complex->bool)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(ginv:complex->complex)(vec 0) = vec 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(ginv:complex->complex)((G:complex->complex)(vec 0)) = vec 0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `t:complex->bool`)) (concl th) &&
        can (find_term ((=) `ginv:complex->complex`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN u ==> (ginv:complex->complex) differentiable at y` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `u:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN t ==> (G:complex->complex) differentiable at x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `t:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Linv = frechet_derivative (ginv:complex->complex) (at (vec 0))` THEN
  SUBGOAL_THEN `linear(Linv:complex->complex) /\ (ginv has_derivative Linv) (at (vec 0))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Linv" THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE; REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. (Linv:complex->complex)((DG:complex->complex) z) = z` (LABEL_TAC "li") THENL
   [MP_TAC(ISPECL [`G:complex->complex`; `ginv:complex->complex`; `t:complex->bool`;
                   `vec 0:complex`] MOI_PDG_DERIV_LEFT_INV) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Linv:complex->complex) u1 = Cx(inv c1) /\
                (Linv:complex->complex) u2 = Cx(inv c2) * ii` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `u1 = inv c1 % (DG:complex->complex)(Cx(&1))` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
        SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; ASSUME `&0 < c1`; COMPLEX_MUL_LID];
        ALL_TAC];
      SUBGOAL_THEN `u2 = inv c2 % (DG:complex->complex) ii` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
        SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; ASSUME `&0 < c2`; COMPLEX_MUL_LID];
        ALL_TAC]] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    USE_THEN "li" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(vec 0,rho)
                    ==> y IN (u:complex->bool) /\ (ginv:complex->complex) y IN t /\
                        norm(ginv y) < r1 /\ (G:complex->complex)(ginv y) = y`
  (LABEL_TAC "bp") THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `y IN (u:complex->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(vec 0:complex,rho) SUBSET u` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ginv:complex->complex) y IN t` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (ginv:complex->complex) u = t` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `t SUBSET ball(vec 0:complex,r1)` THEN
      REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `u:complex->bool`)) (concl th) &&
        can (find_term ((=) `G:complex->complex`)) (concl th) &&
        not (can (find_term ((=) `t:complex->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ginv:complex->complex`; `Linv:complex->complex`; `rho:real`;
                 `Cx c1 * u1 + Cx c2 * u2`] MOI_PDG_CORNER_TOP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:complex->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON];
      SUBGOAL_THEN `Cx c1 * u1 + Cx c2 * u2 = (DG:complex->complex)(Cx(&1)) + DG ii`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear(Linv:complex->complex)`)] THEN
      USE_THEN "li" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
      USE_THEN "bp" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `y IN ball(vec 0:complex,rho)`))) THEN
      SUBGOAL_THEN `(ginv:complex->complex) y = Cx(Re(ginv y))` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `Re((ginv:complex->complex) y)` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `u1:complex`)) (concl th) &&
        can (find_term ((=) `r1:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `norm((ginv:complex->complex) y) < r1` THEN
        FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
        REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `y = Cx tau * u1` SUBST1_TAC THENL
       [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o check (fun th ->
          concl th = `(G:complex->complex)(ginv y) = y`)) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
      REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME `linear(Linv:complex->complex)`)] THEN
      ASM_REWRITE_TAC[COMPLEX_CMUL; GSYM CX_MUL; RE_CX; IM_CX] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
      USE_THEN "bp" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `y IN ball(vec 0:complex,rho)`))) THEN
      SUBGOAL_THEN `(ginv:complex->complex) y = ii * Cx(Im(ginv y))` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_EQ; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX; REAL_NEG_0];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `Im((ginv:complex->complex) y)` o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `u2:complex`)) (concl th) &&
        can (find_term ((=) `r1:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `norm((ginv:complex->complex) y) < r1` THEN
        FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
        REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_II; COMPLEX_NORM_CX; REAL_MUL_LID] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `y = Cx tau * u2` SUBST1_TAC THENL
       [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o check (fun th ->
          concl th = `(G:complex->complex)(ginv y) = y`)) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
      REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME `linear(Linv:complex->complex)`)] THEN
      ASM_REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_ASSOC; GSYM CX_MUL; RE_MUL_II; IM_MUL_II;
                      RE_CX; IM_CX; REAL_NEG_0] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]];
    DISCH_THEN(LABEL_TAC "ct")] THEN
  SUBGOAL_THEN `!y. (Linv:complex->complex) y =
                    Cx((Im(cnj u2 * y) / Im(cnj u2 * u1)) / c1) +
                    ii * Cx((Im(cnj u1 * y) / Im(cnj u1 * u2)) / c2)` (LABEL_TAC "lic") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`u1:complex`; `u2:complex`; `y:complex`] MOI_PDG_CONE2_COORDS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
    ASM_REWRITE_TAC[COMPLEX_CMUL; real_div; CX_MUL; CX_INV] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ !x. norm x < r ==> x IN t /\ norm((G:complex->complex) x) < rho`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(G:complex->complex) continuous at (vec 0)` MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN
    ASM_REWRITE_TAC[DIST_0; VECTOR_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `vec 0:complex` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open(t:complex->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    SIMP_TAC[ASSUME `!x:complex. norm x < d1 ==> norm((G:complex->complex) x) < rho`;
             ASSUME `norm(x:complex) < d1`] THEN
    UNDISCH_TAC `ball(vec 0:complex,d2) SUBSET t` THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`rho:real`; `ginv:complex->complex`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    USE_THEN "bp" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `y IN ball(vec 0:complex,rho)`))) THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`y:complex`; `z:complex`] THEN STRIP_TAC THEN
    USE_THEN "bp" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `y IN ball(vec 0:complex,rho)`))) THEN
    MP_TAC(ISPECL [`ginv:complex->complex`; `G:complex->complex`; `u:complex->bool`;
                   `y:complex`] MOI_PDG_DERIV_LEFT_INV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ASSUME `!y:complex. y IN u ==> (ginv:complex->complex) differentiable at y`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall (concl th) && can (find_term ((=) `t:complex->bool`)) (concl th) &&
        can (find_term (fun t -> name_of t = "differentiable")) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(ISPEC `frechet_derivative (G:complex->complex) (at (ginv(y:complex)))`
                   LINEAR_0) THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `t:complex->bool`)) (concl th) &&
      can (find_term (fun t -> name_of t = "differentiable")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    USE_THEN "ct" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `y IN ball(vec 0:complex,rho)`)]) THEN
    USE_THEN "lic" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_II; IM_MUL_II; REAL_NEG_0;
                REAL_ADD_RID; REAL_ADD_LID] THEN
    MP_TAC(ISPECL [`u1:complex`; `u2:complex`; `y:complex`] MOI_PDG_IN_CONE2) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[MOI_PDG_DIV_SIGN; ASSUME `&0 < c1`; ASSUME `&0 < c2`];
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `r:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall (concl th) && can (find_term ((=) `t:complex->bool`)) (concl th) &&
      can (find_term ((=) `ginv:complex->complex`)) (concl th) &&
      not (can (find_term (fun t -> name_of t = "differentiable")) (concl th)))) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_PDG_COMPACT_INJ_NEAR = prove
 (`!(Q:real^N->complex) s w d.
      compact s /\ Q continuous_on s /\
      (!x y. x IN s /\ y IN s /\ Q x = Q y ==> x = y) /\ w IN s /\ &0 < d
      ==> ?e. &0 < e /\ !x. x IN s /\ norm(Q x - Q w) < e ==> dist(w,x) < d`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Qinv = \y:complex. @x:real^N. x IN s /\ Q x = y` THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> Qinv((Q:real^N->complex) x) = x` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Qinv" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:real^N->complex`; `Qinv:complex->real^N`; `s:real^N->bool`]
         CONTINUOUS_ON_INVERSE) THEN
  ASM_REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `(Q:real^N->complex) w`) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(Q:real^N->complex) x`) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; dist] THEN MESON_TAC[NORM_SUB]);;

let MOI_PDG_SEG_PATH_CONT = prove
 (`!(Q:real^N->complex) s w v c.
      Q continuous_on s /\ segment[w,v] SUBSET s
      ==> (\l. Re(c * Q((&1 - l) % w + l % v))) real_continuous_on real_interval[&0,&1]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_ON] THEN
  SUBGOAL_THEN
   `lift o (\l. Re(c * (Q:real^N->complex)((&1 - l) % w + l % v))) o drop =
    (\z. lift(Re(c * Q z))) o (\u. (&1 - drop u) % w + drop u % v)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. lift(Re(c * (Q:real^N->complex) z))) =
                (\y. lift(y$1)) o (\y. c * y) o Q` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; RE_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `segment[w:real^N,v]` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_SEGMENT] THEN
      REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN
      X_GEN_TAC `l:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      EXISTS_TAC `l:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN REWRITE_TAC[CONTINUOUS_ON_ID]];
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    MATCH_MP_TAC LINEAR_LIFT_DOLLAR_COMPONENT THEN REWRITE_TAC[DIMINDEX_2] THEN
    ARITH_TAC]);;

let MOI_PDG_EDGE_ONTO = prove
 (`!(Q:real^N->complex) s w v u.
      Q continuous_on s /\ segment[w,v] SUBSET s /\ Q w = vec 0 /\ norm u = &1 /\
      (!x. x IN segment[w,v] ==> ?t. &0 <= t /\ Q x = Cx t * u)
      ==> !t. &0 <= t /\ t <= Re(cnj u * Q v)
              ==> ?x. x IN segment[w,v] /\ Q x = Cx t * u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN segment[w:real^N,v]
                    ==> (Q:real^N->complex) x = Cx(Re(cnj u * Q x)) * u` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `u:complex`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_RING `cnj u * Cx s0 * u = Cx s0 * (cnj u * u)`; COMPLEX_MUL_CNJ] THEN
    ASM_REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_MUL_RID; RE_CX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\l. Re(cnj u * (Q:real^N->complex)((&1 - l) % w + l % v))`;
                 `&0`; `&1`; `t:real`] REAL_IVT_INCREASING) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PDG_SEG_PATH_CONT THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_SUB_REFL; REAL_SUB_RZERO; VECTOR_MUL_LZERO; VECTOR_MUL_LID;
                  VECTOR_ADD_RID; VECTOR_ADD_LID] THEN
      ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO; RE_CX]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(&1 - l) % w + l % v:real^N` THEN
  SUBGOAL_THEN `(&1 - l) % w + l % v IN segment[w:real^N,v]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `l:real` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - l) % w + l % v:real^N` o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> name_of t = "Re")) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_TRI_SEGS = prove
 (`!(w:real^N) v1 v2.
      w IN convex hull {w,v1,v2} /\ v1 IN convex hull {w,v1,v2} /\
      v2 IN convex hull {w,v1,v2} /\
      segment[w,v1] SUBSET convex hull {w,v1,v2} /\
      segment[w,v2] SUBSET convex hull {w,v1,v2}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `w IN convex hull {w:real^N,v1,v2} /\ v1 IN convex hull {w,v1,v2} /\
                v2 IN convex hull {w,v1,v2}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MP_TAC(ISPEC `convex hull {w:real^N,v1,v2}` CONVEX_CONTAINS_SEGMENT) THEN
  REWRITE_TAC[CONVEX_CONVEX_HULL] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_TRI_TANGENT = prove
 (`!(w:real^N) v1 v2.
      span {v1 - w, v2 - w} SUBSET moi_smo_tangent (convex hull {w,v1,v2})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_smo_tangent] THEN MATCH_MP_TAC SPAN_MONO THEN
  REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_TRI_SEGS) THEN
  STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

let MOI_PDG_LIN_IN_SPAN = prove
 (`!(w:real^N) v1 v2 y. Re y % (v1 - w) + Im y % (v2 - w) IN span {v1 - w, v2 - w}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN SET_TAC[]);;

let MOI_PDG_IM_CNJ_SCALE = prove
 (`!p q u v:complex. Im(cnj(Cx p * u) * (Cx q * v)) = p * q * Im(cnj u * v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CNJ_MUL; CNJ_CX] THEN
  SUBGOAL_THEN `(Cx p * cnj u) * (Cx q * v) = Cx(p * q) * (cnj u * v)` SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[IM_MUL_CX] THEN REAL_ARITH_TAC);;

let MOI_PDG_PAR_DEP = prove
 (`!d1 d2:complex. ~(d1 = vec 0) /\ Im(cnj d1 * d2) = &0
                   ==> d2 = (Re(cnj d1 * d2) / norm d1 pow 2) % d1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `cnj d1 * d2 = Cx(Re(cnj d1 * d2))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_EQ; RE_CX; IM_CX]; ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(norm(d1:complex)) pow 2 = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_POW_EQ_0; CX_INJ; ARITH] THEN
    ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  MP_TAC(CONJUNCT2(SPEC `d1:complex` COMPLEX_MUL_CNJ)) THEN
  REWRITE_TAC[COMPLEX_CMUL; CX_DIV; CX_POW] THEN
  ABBREV_TAC `r = Re(cnj d1 * d2)` THEN
  UNDISCH_TAC `cnj d1 * d2 = Cx r` THEN
  UNDISCH_TAC `~(Cx(norm(d1:complex)) pow 2 = Cx(&0))` THEN
  CONV_TAC COMPLEX_FIELD);;

let MOI_PDG_CORNER_PREP = prove
 (`!(w:real^N) v1 v2 (Q:real^N->complex).
      ~(v1 = w) /\ ~(v2 = w) /\ ~(v1 = v2) /\ ~(affine_dependent {w,v1,v2}) /\
      moi_smo_cell_smooth (convex hull {w,v1,v2}) Q /\
      (!x y. x IN convex hull {w,v1,v2} /\ y IN convex hull {w,v1,v2} /\ Q x = Q y
             ==> x = y) /\
      Q w = vec 0 /\
      (?a. !x. x IN segment[w,v1] ==> ?t. &0 <= t /\ Q x = t % a) /\
      (?a. !x. x IN segment[w,v2] ==> ?t. &0 <= t /\ Q x = t % a)
      ==> ?g u0 u1 u2 c1 c2.
            open u0 /\ convex hull {w,v1,v2} SUBSET u0 /\ smooth_map_on u0 g /\
            (!x. x IN convex hull {w,v1,v2} ==> g x = Q x) /\
            (!x z. x IN convex hull {w,v1,v2} /\ z IN span {v1 - w, v2 - w} /\
                   frechet_derivative g (at x) z = vec 0 ==> z = vec 0) /\
            norm u1 = &1 /\ norm u2 = &1 /\ ~(Im(cnj u1 * u2) = &0) /\
            &0 < c1 /\ &0 < c2 /\
            frechet_derivative (\y. g(moi_pdg_tpar w v1 v2 y)) (at (vec 0)) (Cx(&1)) =
            Cx c1 * u1 /\
            frechet_derivative (\y. g(moi_pdg_tpar w v1 v2 y)) (at (vec 0)) ii =
            Cx c2 * u2 /\
            (!x. x IN segment[w,v1] ==> ?t. &0 <= t /\ Q x = Cx t * u1) /\
            (!x. x IN segment[w,v2] ==> ?t. &0 <= t /\ Q x = Cx t * u2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cs") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `a1:complex` (LABEL_TAC "e1"))
       (X_CHOOSE_THEN `a2:complex` (LABEL_TAC "e2")))))))))) THEN
  MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_TRI_SEGS) THEN
  STRIP_TAC THEN
  USE_THEN "cs" (MP_TAC o GEN_REWRITE_RULE I [moi_smo_cell_smooth]) THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^N->bool` (X_CHOOSE_THEN `g:real^N->complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tan"))))))) THEN
  SUBGOAL_THEN `!x z. x IN convex hull {w:real^N,v1,v2} /\ z IN span {v1 - w, v2 - w} /\
                      frechet_derivative (g:real^N->complex) (at x) z = vec 0 ==> z = vec 0`
  (LABEL_TAC "tan2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "tan" MATCH_MP_TAC THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_TRI_TANGENT) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->complex) differentiable at w` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `u0:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Dg = frechet_derivative (g:real^N->complex) (at w)` THEN
  SUBGOAL_THEN `((\y. (g:real^N->complex)(moi_pdg_tpar w v1 v2 y)) has_derivative
                 (\z. (Dg:real^N->complex)(Re z % (v1 - w) + Im z % (v2 - w)))) (at (vec 0))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. (g:real^N->complex)(moi_pdg_tpar w v1 v2 y)) =
                  g o moi_pdg_tpar w v1 v2 /\
                  (\z. (Dg:real^N->complex)(Re z % (v1 - w) + Im z % (v2 - w))) =
                  Dg o (\z. Re z % (v1 - w) + Im z % (v2 - w))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[MOI_PDG_TPAR_DERIV; MOI_PDG_TPAR_0] THEN
    EXPAND_TAC "Dg" THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (\y. (g:real^N->complex)(moi_pdg_tpar w v1 v2 y)) (at (vec 0)) =
                (\z. (Dg:real^N->complex)(Re z % (v1 - w) + Im z % (v2 - w)))`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a1:complex = vec 0) /\ ~(a2:complex = vec 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "e1" (fun th -> MP_TAC(MATCH_MP th
        (CONJUNCT2(ISPECL [`w:real^N`; `v1:real^N`] ENDS_IN_SEGMENT))));
      USE_THEN "e2" (fun th -> MP_TAC(MATCH_MP th
        (CONJUNCT2(ISPECL [`w:real^N`; `v2:real^N`] ENDS_IN_SEGMENT))))] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC `~(v1:real^N = w)`; UNDISCH_TAC `~(v2:real^N = w)`] THEN
    REWRITE_TAC[] THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->complex) w = vec 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
       can (find_term (fun t -> t = `Q:real^N->complex`)) (concl th) &&
       can (find_term (fun t -> t = `g:real^N->complex`)) (concl th)
     then MP_TAC(SPEC `w:real^N` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. (g:real^N->complex)(moi_pdg_tpar w v1 v2 y)`;
                 `\z. (Dg:real^N->complex)(Re z % (v1 - w) + Im z % (v2 - w))`;
                 `a1:complex`; `Cx(&1)`; `&1`] MOI_PDG_EDGE_DIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; MOI_PDG_TPAR_0] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `t % Cx(&1) = Cx t` SUBST1_TAC THENL
       [REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID]; ALL_TAC] THEN
      SUBGOAL_THEN `moi_pdg_tpar (w:real^N) v1 v2 (Cx t) IN segment[w,v1]` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`; `t:real`] MOI_PDG_TPAR_EDGES) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^N->complex)(moi_pdg_tpar w v1 v2 (Cx t)) =
                    Q(moi_pdg_tpar w v1 v2 (Cx t))` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `Q:real^N->complex`)) (concl th) &&
          can (find_term (fun t -> t = `g:real^N->complex`)) (concl th))) THEN
        UNDISCH_TAC `segment[w:real^N,v1] SUBSET convex hull {w,v1,v2}` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "e1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[RE_CX; IM_CX; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      DISCH_TAC THEN USE_THEN "tan2" (MP_TAC o SPECL [`w:real^N`; `v1 - w:real^N`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_SUPERSET THEN SET_TAC[];
        ASM_REWRITE_TAC[VECTOR_SUB_EQ]]];
    DISCH_THEN(X_CHOOSE_THEN `k1:real` (STRIP_ASSUME_TAC o
      REWRITE_RULE[RE_CX; IM_CX; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID]))] THEN
  MP_TAC(ISPECL [`\y. (g:real^N->complex)(moi_pdg_tpar w v1 v2 y)`;
                 `\z. (Dg:real^N->complex)(Re z % (v1 - w) + Im z % (v2 - w))`;
                 `a2:complex`; `ii`; `&1`] MOI_PDG_EDGE_DIR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_01; MOI_PDG_TPAR_0] THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `t % ii = ii * Cx t` SUBST1_TAC THENL
       [REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_SYM]; ALL_TAC] THEN
      SUBGOAL_THEN `moi_pdg_tpar (w:real^N) v1 v2 (ii * Cx t) IN segment[w,v2]` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`; `t:real`] MOI_PDG_TPAR_EDGES) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^N->complex)(moi_pdg_tpar w v1 v2 (ii * Cx t)) =
                    Q(moi_pdg_tpar w v1 v2 (ii * Cx t))` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `Q:real^N->complex`)) (concl th) &&
          can (find_term (fun t -> t = `g:real^N->complex`)) (concl th))) THEN
        UNDISCH_TAC `segment[w:real^N,v2] SUBSET convex hull {w,v1,v2}` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "e2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[RE_II; IM_II; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
      DISCH_TAC THEN USE_THEN "tan2" (MP_TAC o SPECL [`w:real^N`; `v2 - w:real^N`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_SUPERSET THEN SET_TAC[];
        ASM_REWRITE_TAC[VECTOR_SUB_EQ]]];
    DISCH_THEN(X_CHOOSE_THEN `k2:real` (STRIP_ASSUME_TAC o
      REWRITE_RULE[RE_II; IM_II; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID]))] THEN
  SUBGOAL_THEN `linear(Dg:real^N->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "Dg" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Im(cnj a1 * a2) = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`a1:complex`; `a2:complex`] MOI_PDG_PAR_DEP) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `mu = Re(cnj a1 * a2) / norm(a1:complex) pow 2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(Dg:real^N->complex)((v2 - w) - (k2 * mu / k1) % (v1 - w)) = vec 0`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(Dg:real^N->complex)((v2 - w) - (k2 * mu / k1) % (v1 - w)) =
                    Dg(v2 - w) - (k2 * mu / k1) % Dg(v1 - w)` SUBST1_TAC THENL
       [REWRITE_TAC[MATCH_MP LINEAR_SUB (ASSUME `linear(Dg:real^N->complex)`);
                    MATCH_MP LINEAR_CMUL (ASSUME `linear(Dg:real^N->complex)`)];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `(k2 * mu / k1) * k1 = k2 * mu` (fun th -> REWRITE_TAC[th; VECTOR_SUB_REFL]) THEN
      UNDISCH_TAC `&0 < k1` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    USE_THEN "tan2" (MP_TAC o SPECL
      [`w:real^N`; `(v2 - w) - (k2 * mu / k1) % (v1 - w):real^N`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_SUB THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC SPAN_MUL) THEN MATCH_MP_TAC SPAN_SUPERSET THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `Re(complex(--(k2 * mu / k1),&1)) % (v1 - w) +
                  Im(complex(--(k2 * mu / k1),&1)) % (v2 - w) = vec 0:real^N`
    ASSUME_TAC THENL
     [REWRITE_TAC[RE; IM] THEN
      UNDISCH_TAC `(v2 - w) - (k2 * mu / k1) % (v1 - w):real^N = vec 0` THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_TPAR_LIN_INJ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `complex(--(k2 * mu / k1),&1)`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_EQ; COMPLEX_VEC_0; RE_CX; IM_CX; RE; IM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(a1:complex) /\ &0 < norm(a2:complex)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`g:real^N->complex`; `u0:real^N->bool`;
                        `inv(norm(a1:complex)) % a1`; `inv(norm(a2:complex)) % a2`;
                        `k1 * norm(a1:complex)`; `k2 * norm(a2:complex)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    REWRITE_TAC[COMPLEX_CMUL; MOI_PDG_IM_CNJ_SCALE; REAL_ENTIRE; REAL_INV_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ASM_SIMP_TAC[REAL_LT_MUL];
    ASM_SIMP_TAC[REAL_LT_MUL];
    REWRITE_TAC[RE_CX; IM_CX; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[COMPLEX_CMUL; CX_MUL; CX_INV] THEN
    SUBGOAL_THEN `~(Cx(norm(a1:complex)) = Cx(&0))` MP_TAC THENL
     [ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ]; CONV_TAC COMPLEX_FIELD];
    REWRITE_TAC[RE_II; IM_II; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
    ASM_REWRITE_TAC[COMPLEX_CMUL; CX_MUL; CX_INV] THEN
    SUBGOAL_THEN `~(Cx(norm(a2:complex)) = Cx(&0))` MP_TAC THENL
     [ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ]; CONV_TAC COMPLEX_FIELD];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "e1" (fun th -> MP_TAC(MATCH_MP th (ASSUME `x IN segment[w:real^N,v1]`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t * norm(a1:complex)` THEN ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN
    REWRITE_TAC[COMPLEX_CMUL; CX_MUL; CX_INV] THEN
    SUBGOAL_THEN `~(Cx(norm(a1:complex)) = Cx(&0))` MP_TAC THENL
     [ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ]; CONV_TAC COMPLEX_FIELD];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "e2" (fun th -> MP_TAC(MATCH_MP th (ASSUME `x IN segment[w:real^N,v2]`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t * norm(a2:complex)` THEN ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN
    REWRITE_TAC[COMPLEX_CMUL; CX_MUL; CX_INV] THEN
    SUBGOAL_THEN `~(Cx(norm(a2:complex)) = Cx(&0))` MP_TAC THENL
     [ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ]; CONV_TAC COMPLEX_FIELD]]);;


let MOI_PDG_CORNER = prove
 (`!(w:real^N) v1 v2 (Q:real^N->complex) d.
      &0 < d /\
      ~(v1 = w) /\ ~(v2 = w) /\ ~(v1 = v2) /\ ~(affine_dependent {w,v1,v2}) /\
      moi_smo_cell_smooth (convex hull {w,v1,v2}) Q /\
      (!x y. x IN convex hull {w,v1,v2} /\ y IN convex hull {w,v1,v2} /\ Q x = Q y
             ==> x = y) /\
      Q w = vec 0 /\
      (?a. !x. x IN segment[w,v1] ==> ?t. &0 <= t /\ Q x = t % a) /\
      (?a. !x. x IN segment[w,v2] ==> ?t. &0 <= t /\ Q x = t % a)
      ==> ?u1 u2 e R.
            norm u1 = &1 /\ norm u2 = &1 /\ ~(Im(cnj u1 * u2) = &0) /\ &0 < e /\
            smooth_map_on (ball(vec 0,e)) R /\
            (!y z. y IN ball(vec 0,e) /\ frechet_derivative R (at y) z = vec 0
                   ==> z = vec 0) /\
            (!y z. y IN ball(vec 0,e)
                   ==> frechet_derivative R (at y) z IN span {v1 - w, v2 - w}) /\
            (!y. y IN ball(vec 0,e) ==> dist(w,R y) < d) /\
            (!y. y IN ball(vec 0,e) INTER moi_pdg_cone2 u1 u2
                 ==> R y IN convex hull {w,v1,v2} /\ Q(R y) = y) /\
            (!x. x IN convex hull {w,v1,v2} /\ norm(Q x) < e
                 ==> Q x IN moi_pdg_cone2 u1 u2 /\ R(Q x) = x) /\
            (!t. &0 <= t /\ t < e
                 ==> R(Cx t * u1) IN segment[w,v1] /\ R(Cx t * u2) IN segment[w,v2]) /\
            (!x. x IN segment[w,v1] ==> ?t. &0 <= t /\ Q x = Cx t * u1) /\
            (!x. x IN segment[w,v2] ==> ?t. &0 <= t /\ Q x = Cx t * u2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC(MATCH_MP MOI_PDG_CORNER_PREP th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->complex` (X_CHOOSE_THEN `u0:real^N->bool`
    (X_CHOOSE_THEN `u1:complex` (X_CHOOSE_THEN `u2:complex`
    (X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `c2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "gq") (CONJUNCTS_THEN2 (LABEL_TAC "tan2")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "r1") (LABEL_TAC "r2")))))))))))))))))))) THEN
  MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_TRI_SEGS) THEN
  STRIP_TAC THEN
  ABBREV_TAC `s = convex hull {w:real^N,v1,v2}` THEN
  SUBGOAL_THEN `(Q:real^N->complex) continuous_on s` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN EXISTS_TAC `g:real^N->complex` THEN CONJ_TAC THENL
     [USE_THEN "gq" (fun th -> SIMP_TAC[th]);
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u0:real^N->bool` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `P0 = {y:complex | moi_pdg_tpar (w:real^N) v1 v2 y IN u0 INTER ball(w,d)}` THEN
  SUBGOAL_THEN `open(P0:complex->bool) /\ vec 0 IN P0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P0" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN CONJ_TAC THENL
       [GEN_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
        REWRITE_TAC[differentiable] THEN
        EXISTS_TAC `\y:complex. Re y % (v1 - w) + Im y % (v2 - w:real^N)` THEN
        REWRITE_TAC[ETA_AX; MOI_PDG_TPAR_DERIV];
        MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_BALL] THEN FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[IN_ELIM_THM; MOI_PDG_TPAR_0; IN_INTER; CENTRE_IN_BALL] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `s SUBSET (u0:real^N->bool)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `vec 0:complex` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
    check (fun th -> concl th = `open(P0:complex->bool)`)) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r1 = min r0 (&1 / &2)` THEN
  SUBGOAL_THEN `&0 < r1 /\ r1 <= &1 / &2 /\ ball(vec 0:complex,r1) SUBSET P0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r1" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:complex,r0)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN P0 ==> moi_pdg_tpar (w:real^N) v1 v2 y IN u0 /\
                                dist(w,moi_pdg_tpar w v1 v2 y) < d` (LABEL_TAC "p0") THENL
   [EXPAND_TAC "P0" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER; IN_BALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on P0 (\y. (g:real^N->complex)(moi_pdg_tpar w v1 v2 y))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\y. (g:real^N->complex)(moi_pdg_tpar w v1 v2 y)) =
                  g o moi_pdg_tpar w v1 v2` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u0:real^N->bool` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
      USE_THEN "p0" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `y IN (P0:complex->bool)`)]);
      MATCH_MP_TAC MOI_PDG_TPAR_SMOOTH THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->complex) w = vec 0` ASSUME_TAC THENL
   [USE_THEN "gq" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(w:real^N) IN s`)]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. (g:real^N->complex)(moi_pdg_tpar w v1 v2 y)`; `P0:complex->bool`;
                 `r1:real`; `u1:complex`; `u2:complex`; `c1:real`; `c2:real`]
         MOI_PDG_CORNER_LOCAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_PDG_TPAR_0] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN X_GEN_TAC `p:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`; `p:real`] MOI_PDG_TPAR_EDGES) THEN
    (ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC]) THENL
     [SUBGOAL_THEN `(g:real^N->complex)(moi_pdg_tpar w v1 v2 (Cx p)) =
                    Q(moi_pdg_tpar w v1 v2 (Cx p))` SUBST1_TAC THENL
       [USE_THEN "gq" MATCH_MP_TAC THEN UNDISCH_TAC `segment[w:real^N,v1] SUBSET s` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      USE_THEN "r1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      SUBGOAL_THEN `(g:real^N->complex)(moi_pdg_tpar w v1 v2 (ii * Cx p)) =
                    Q(moi_pdg_tpar w v1 v2 (ii * Cx p))` SUBST1_TAC THENL
       [USE_THEN "gq" MATCH_MP_TAC THEN UNDISCH_TAC `segment[w:real^N,v2] SUBSET s` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      USE_THEN "r2" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[]) THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (X_CHOOSE_THEN `ginv:complex->complex`
    (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "gi") (CONJUNCTS_THEN2 (LABEL_TAC "gd")
    (CONJUNCTS_THEN2 (LABEL_TAC "gc") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gr")))))))))) THEN
  MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_TPAR_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))) THEN
  MP_TAC(ISPECL [`Q:real^N->complex`; `s:real^N->bool`; `w:real^N`; `B * r`]
         MOI_PDG_COMPACT_INJ_NEAR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(Q:real^N->complex) w = vec 0`; VECTOR_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))) THEN
  SUBGOAL_THEN `&0 < Re(cnj u1 * (Q:real^N->complex) v1) /\ &0 < Re(cnj u2 * Q v2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "r1" (fun th -> MP_TAC(MATCH_MP th
        (CONJUNCT2(ISPECL [`w:real^N`; `v1:real^N`] ENDS_IN_SEGMENT))));
      USE_THEN "r2" (fun th -> MP_TAC(MATCH_MP th
        (CONJUNCT2(ISPECL [`w:real^N`; `v2:real^N`] ENDS_IN_SEGMENT))))] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (fun th -> ASSUME_TAC th THEN SUBST1_TAC th))) THEN
    REWRITE_TAC[COMPLEX_RING `cnj u * Cx t * u = Cx t * (cnj u * u)`; COMPLEX_MUL_CNJ] THEN
    ASM_REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_MUL_RID; RE_CX] THEN
    ASM_CASES_TAC `t = &0` THEN TRY ASM_REAL_ARITH_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_MUL_LZERO]) THENL
     [UNDISCH_TAC `~(v1:real^N = w)`; UNDISCH_TAC `~(v2:real^N = w)`] THEN
    REWRITE_TAC[REAL_LT_REFL] THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `Q:real^N->complex`)) (concl th))) THEN
    ASM_REWRITE_TAC[COMPLEX_VEC_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:real^N->complex`; `s:real^N->bool`; `w:real^N`; `v1:real^N`;
                 `u1:complex`] MOI_PDG_EDGE_ONTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "o1")] THEN
  MP_TAC(ISPECL [`Q:real^N->complex`; `s:real^N->bool`; `w:real^N`; `v2:real^N`;
                 `u2:complex`] MOI_PDG_EDGE_ONTO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "o2")] THEN
  ABBREV_TAC `e = min rho (min e0 (min (Re(cnj u1 * (Q:real^N->complex) v1))
                                       (Re(cnj u2 * Q v2))))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= rho /\ e <= e0 /\
                e <= Re(cnj u1 * (Q:real^N->complex) v1) /\ e <= Re(cnj u2 * Q v2)`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(vec 0,e) ==> y IN ball(vec 0:complex,rho)` (LABEL_TAC "be") THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:complex. y IN ball(vec 0,rho)
      ==> ((\y. moi_pdg_tpar (w:real^N) v1 v2 ((ginv:complex->complex) y)) has_derivative
           (\z. Re(frechet_derivative ginv (at y) z) % (v1 - w) +
                Im(frechet_derivative ginv (at y) z) % (v2 - w))) (at y)` (LABEL_TAC "rd") THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\y. moi_pdg_tpar (w:real^N) v1 v2 ((ginv:complex->complex) y)) =
                  moi_pdg_tpar w v1 v2 o ginv /\
                  (\z. Re(frechet_derivative (ginv:complex->complex) (at (y:complex)) z) %
                       (v1 - w) +
                       Im(frechet_derivative ginv (at y) z) % (v2 - w):real^N) =
                  (\z. Re z % (v1 - w) + Im z % (v2 - w)) o frechet_derivative ginv (at y)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN REWRITE_TAC[MOI_PDG_TPAR_DERIV] THEN
    REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:complex,rho)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN s /\ norm((Q:real^N->complex) x) < e
                    ==> Q x IN moi_pdg_cone2 u1 u2 /\ moi_pdg_tpar w v1 v2 (ginv(Q x)) = x`
  (LABEL_TAC "c10") THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`; `x:real^N`] MOI_PDG_TPAR_HULL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:complex` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "px"))))) THEN
    SUBGOAL_THEN `norm(p:complex) < r` ASSUME_TAC THENL
     [USE_THEN "near" (MP_TAC o SPEC `x:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "bd" (MP_TAC o SPEC `p:complex`) THEN
      USE_THEN "px" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[dist] THEN DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `B * norm(p:complex) < B * r` MP_TAC THENL
       [MP_TAC(ISPECL [`x:real^N`; `w:real^N`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_LMUL_EQ]];
      ALL_TAC] THEN
    USE_THEN "gr" (fun th -> MP_TAC(MATCH_MP th (ASSUME `norm(p:complex) < r`))) THEN
    USE_THEN "px" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "gq" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^N) IN s`)]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(Q:real^N->complex) x IN ball(vec 0,rho)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
    USE_THEN "gc" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(Q:real^N->complex) x IN ball(vec 0,rho)`)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u1:complex`; `u2:complex`; `e:real`;
                        `\y. moi_pdg_tpar (w:real^N) v1 v2 ((ginv:complex->complex) y)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\y. moi_pdg_tpar (w:real^N) v1 v2 ((ginv:complex->complex) y)) =
                  moi_pdg_tpar w v1 v2 o ginv` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `(:complex)` THEN
    REWRITE_TAC[OPEN_BALL; OPEN_UNIV; SUBSET_UNIV] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:complex,rho)` THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[SUBSET_BALL];
      MATCH_MP_TAC MOI_PDG_TPAR_SMOOTH THEN REWRITE_TAC[OPEN_UNIV]];
    MAP_EVERY X_GEN_TAC [`y:complex`; `z:complex`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `y IN ball(vec 0:complex,rho)` ASSUME_TAC THENL
     [USE_THEN "be" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "rd" (fun th -> MP_TAC(MATCH_MP th (ASSUME `y IN ball(vec 0:complex,rho)`))) THEN
    DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) THEN
    MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_TPAR_LIN_INJ) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `frechet_derivative (ginv:complex->complex) (at y) z`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "gd" MATCH_MP_TAC THEN EXISTS_TAC `y:complex` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`y:complex`; `z:complex`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `y IN ball(vec 0:complex,rho)` ASSUME_TAC THENL
     [USE_THEN "be" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "rd" (fun th -> MP_TAC(MATCH_MP th (ASSUME `y IN ball(vec 0:complex,rho)`))) THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    REWRITE_TAC[MOI_PDG_LIN_IN_SPAN];
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `y IN ball(vec 0:complex,rho)` ASSUME_TAC THENL
     [USE_THEN "be" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "gi" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `y IN ball(vec 0:complex,rho)`))) THEN
    SUBGOAL_THEN `(ginv:complex->complex) y IN P0` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(vec 0:complex,r1) SUBSET P0` THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "p0" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(ginv:complex->complex) y IN P0`)]);
    X_GEN_TAC `y:complex` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    SUBGOAL_THEN `y IN ball(vec 0:complex,rho)` ASSUME_TAC THENL
     [USE_THEN "be" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "gi" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `y IN ball(vec 0:complex,rho)`))) THEN
    USE_THEN "gc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `y IN ball(vec 0:complex,rho)`))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_pdg_tpar (w:real^N) v1 v2 ((ginv:complex->complex) y) IN s`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`;
                     `moi_pdg_tpar (w:real^N) v1 v2 ((ginv:complex->complex) y)`]
             MOI_PDG_TPAR_HULL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      EXISTS_TAC `(ginv:complex->complex) y` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `(ginv:complex->complex) y` COMPLEX_NORM_GE_RE_IM) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "gq" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `moi_pdg_tpar (w:real^N) v1 v2 ((ginv:complex->complex) y) IN s`))]) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "o1" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(Q:real^N->complex) x = Cx t * u1`)) THEN
      SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
       [UNDISCH_TAC `segment[w:real^N,v1] SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC];
      USE_THEN "o2" (MP_TAC o SPEC `t:real`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(Q:real^N->complex) x = Cx t * u2`)) THEN
      SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
       [UNDISCH_TAC `segment[w:real^N,v2] SUBSET s` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC]] THEN
    USE_THEN "c10" (MP_TAC o SPEC `x:real^N`) THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
       STRIP_TAC THEN ASM_REWRITE_TAC[]])]);;

(* Per-triangle data at a vertex w: the other vertices v1, v2, the             *)
(* developed angles th1 < th2 (MOI_PDG_DEV), one-sided derivative uniqueness on   *)
(* cones (MOI_PDG_DERIV_CONE) and the smooth local map H (MOI_PDG_TRI_H).         *)

let MOI_PDG_TRI_AT_VERTEX = prove
 (`!L s (w:real^N).
      simplicial_complex L /\ s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s
      ==> ?v1 v2. ~(v1 = w) /\ ~(v2 = w) /\ ~(v1 = v2) /\ ~(affine_dependent {w,v1,v2}) /\
                  s = convex hull {w,v1,v2} /\ segment[w,v1] IN L /\ segment[w,v2] IN L`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`] MOI_PDG_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(w:real^N) IN c` ASSUME_TAC THENL
   [SUBGOAL_THEN `{w:real^N} face_of s` MP_TAC THENL
     [SUBGOAL_THEN `{w:real^N} = s INTER {w}` SUBST1_TAC THENL
       [UNDISCH_TAC `(w:real^N) IN s` THEN SET_TAC[];
        MATCH_MP_TAC MOI_PDG_SC_INTER_FACE THEN
        EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[FACE_OF_SING] THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `s:real^N->bool`
                          then REWRITE_TAC[th] else NO_TAC) THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(c:real^N->bool) = 3` ASSUME_TAC THENL
   [UNDISCH_TAC `(&2:int) = &(CARD(c:real^N->bool)) - &1` THEN
    REWRITE_TAC[INT_ARITH `&2:int = x - &1 <=> x = &3`; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v1 v2:real^N. ~(v1 = w) /\ ~(v2 = w) /\ ~(v1 = v2) /\ c = {w,v1,v2}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(c:real^N->bool) HAS_SIZE 3` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` (X_CHOOSE_THEN `e:real^N`
      STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `(w:real^N) IN c` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [MAP_EVERY EXISTS_TAC [`b:real^N`; `e:real^N`] THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`a:real^N`; `e:real^N`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(SET_TAC[]) THEN ASM_MESON_TAC[];
      MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(SET_TAC[]) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v1:real^N`; `v2:real^N`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `c:real^N->bool`)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_PDG_SC_FACE_IN THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `s:real^N->bool`
                        then REWRITE_TAC[th] else NO_TAC) THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THENL
   [EXISTS_TAC `{w:real^N,v1}`; EXISTS_TAC `{w:real^N,v2}`] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN SET_TAC[]);;

let MOI_PDG_ANG_POLAR = prove
 (`!k b r t. &0 < r /\ &0 <= t /\ t <= pi
             ==> moi_smo_ang k b (Cx r * cexp(ii * Cx(b + t))) =
                 Cx r * cexp(ii * Cx(k * (b + t)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_smo_ang] THEN
  SUBGOAL_THEN `cexp(--(ii * Cx b)) * Cx r * cexp(ii * Cx(b + t)) = Cx r * cexp(ii * Cx t)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
    MP_TAC(SPEC `ii * Cx b` CEXP_NEG_LMUL) THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `Arg(Cx r * cexp(ii * Cx t)) = t` SUBST1_TAC THENL
   [MATCH_MP_TAC ARG_UNIQUE THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`]);;

let MOI_PDG_ANG_NORM = prove
 (`!k b y. norm(moi_smo_ang k b y) = norm y`,
  REWRITE_TAC[moi_smo_ang; COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX;
              REAL_MUL_RID; REAL_ABS_NORM]);;

let MOI_PDG_ARG_POS = prove
 (`!z. &0 <= Arg z`,
  GEN_TAC THEN ACCEPT_TAC(CONJUNCT1(SPEC `z:complex` ARG)));;

let MOI_PDG_DEV_ANGLES = prove
 (`!b u1 u2. norm u1 = &1 /\ norm u2 = &1 /\ &0 < Im(cnj u1 * u2) /\
             &0 <= Im(cexp(--(ii * Cx b)) * u1) /\ &0 <= Im(cexp(--(ii * Cx b)) * u2)
             ==> ?th1 th2. u1 = cexp(ii * Cx(b + th1)) /\ u2 = cexp(ii * Cx(b + th2)) /\
                           &0 <= th1 /\ th1 < th2 /\ th2 <= pi /\ th2 - th1 < pi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!u. norm u = &1 ==> u = cexp(ii * Cx(b + Arg(cexp(--(ii * Cx b)) * u)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(CONJUNCT2(CONJUNCT2(SPEC `cexp(--(ii * Cx b)) * u` ARG))) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP; RE_NEG; RE_MUL_II; IM_CX; REAL_NEG_0;
                REAL_EXP_0; REAL_MUL_LID] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN
    REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    MP_TAC(SPEC `ii * Cx b` CEXP_NEG_RMUL) THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Arg(cexp(--(ii * Cx b)) * u1)`; `Arg(cexp(--(ii * Cx b)) * u2)`] THEN
  CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `t1 = Arg(cexp(--(ii * Cx b)) * u1)` THEN
  ABBREV_TAC `t2 = Arg(cexp(--(ii * Cx b)) * u2)` THEN
  SUBGOAL_THEN `&0 <= t1 /\ t1 <= pi /\ &0 <= t2 /\ t2 <= pi` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["t1"; "t2"] THEN ASM_REWRITE_TAC[ARG_LE_PI; MOI_PDG_ARG_POS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `Im(cnj u1 * u2) = sin(t2 - t1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `u1 = cexp(ii * Cx(b + t1)) /\ u2 = Cx(&1) * cexp(ii * Cx(b + t2))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[COMPLEX_MUL_LID] THEN CONJ_TAC THEN MAP_EVERY EXPAND_TAC ["t1"; "t2"] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_PDG_IM_CNJ_POLAR; REAL_MUL_LID;
                  REAL_ARITH `(b + t2) - (b + t1) = t2 - t1`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1 < t2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPEC `t1 - t2` SIN_POS_PI_LE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `sin(t1 - t2) = --sin(t2 - t1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SIN_NEG] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `&0 < Im(cnj u1 * u2)` THEN
  ASM_REWRITE_TAC[SIN_PI; REAL_LT_REFL]);;

let MOI_PDG_CEXP_PERIOD = prove
 (`!x. cexp(ii * Cx(x + &2 * pi)) = cexp(ii * Cx x)`,
  GEN_TAC THEN REWRITE_TAC[CEXP_EQ] THEN EXISTS_TAC `&1` THEN
  REWRITE_TAC[INTEGER_CLOSED; CX_ADD; CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let MOI_PDG_DEV_KBOUND = prove
 (`!(top:(real^N)topology) sigma (U:real^N->bool) phi k b s (Q:real^N->complex) R e th1 th2.
      smooth_manifold_atlas top sigma /\ (U,phi) IN sigma /\ &0 < k /\ &0 < e /\
      &0 <= th1 /\ th1 < th2 /\ th2 <= pi /\ th2 - th1 < pi /\
      (!y. y IN ball(vec 0,e) INTER
               moi_pdg_cone2 (cexp(ii * Cx(b + th1))) (cexp(ii * Cx(b + th2)))
           ==> R y IN s /\ R y IN U /\ Q(R y) = y) /\
      (!x. x IN s INTER U ==> phi x = moi_smo_ang k b (Q x))
      ==> k * (th2 - th1) < &2 * pi`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rc") (LABEL_TAC "ang")))))))))) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `th' = th1 + (&2 * pi) / k` THEN
  SUBGOAL_THEN `th1 < th' /\ th' <= th2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th'" THEN
    SUBGOAL_THEN `&0 < (&2 * pi) / k /\ (&2 * pi) / k <= th2 - th1` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN MP_TAC PI_POS THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. &0 <= t /\ t <= th2 - th1
                    ==> Cx(e / &2) * cexp(ii * Cx(b + th1 + t)) IN ball(vec 0,e) INTER
                        moi_pdg_cone2 (cexp(ii * Cx(b + th1))) (cexp(ii * Cx(b + th2)))`
  (LABEL_TAC "inc") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_INTER; IN_BALL_0] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`b + th1:real`; `th2 - th1:real`;
                   `Cx(e / &2) * cexp(ii * Cx(b + th1 + t))`] MOI_PDG_CONE2_ANGLE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `(b + th1) + (th2 - th1) = b + th2`] THEN
    DISCH_THEN SUBST1_TAC THEN DISJ2_TAC THEN
    MAP_EVERY EXISTS_TAC [`e / &2`; `t:real`] THEN
    ASM_REWRITE_TAC[REAL_ADD_ASSOC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `y1 = Cx(e / &2) * cexp(ii * Cx(b + th1))` THEN
  ABBREV_TAC `y2 = Cx(e / &2) * cexp(ii * Cx(b + th'))` THEN
  SUBGOAL_THEN `(y1:complex) IN ball(vec 0,e) INTER
                moi_pdg_cone2 (cexp(ii * Cx(b + th1))) (cexp(ii * Cx(b + th2)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "y1" THEN USE_THEN "inc" (MP_TAC o SPEC `&0`) THEN
    REWRITE_TAC[REAL_ADD_RID] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y2:complex) IN ball(vec 0,e) INTER
                moi_pdg_cone2 (cexp(ii * Cx(b + th1))) (cexp(ii * Cx(b + th2)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "y2" THEN USE_THEN "inc" (MP_TAC o SPEC `th' - th1`) THEN
    REWRITE_TAC[REAL_ARITH `b + th1 + th' - th1 = b + th'`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:complex->real^N) y1 IN s /\ R y1 IN U /\ (Q:real^N->complex)(R y1) = y1 /\
                R y2 IN s /\ R y2 IN U /\ Q(R y2) = y2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^N->real^2) (R(y1:complex)) = phi (R y2)` ASSUME_TAC THENL
   [USE_THEN "ang" (fun th -> REWRITE_TAC[MATCH_MP (REWRITE_RULE[IN_INTER] th)
      (CONJ (ASSUME `(R:complex->real^N) y1 IN s`) (ASSUME `(R:complex->real^N) y1 IN U`))]) THEN
    USE_THEN "ang" (fun th -> REWRITE_TAC[MATCH_MP (REWRITE_RULE[IN_INTER] th)
      (CONJ (ASSUME `(R:complex->real^N) y2 IN s`) (ASSUME `(R:complex->real^N) y2 IN U`))]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `Cx(e / &2) * cexp(ii * Cx(b + th1)) = y1`)) THEN
    SUBST1_TAC(SYM(ASSUME `Cx(e / &2) * cexp(ii * Cx(b + th')) = y2`)) THEN
    SUBGOAL_THEN `&0 < e / &2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:real`; `b:real`; `e / &2`; `th1:real`] MOI_PDG_ANG_POLAR) THEN
    MP_TAC(ISPECL [`k:real`; `b:real`; `e / &2`; `th':real`] MOI_PDG_ANG_POLAR) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN EXPAND_TAC "th'" THEN
    SUBGOAL_THEN `k * (b + th1 + (&2 * pi) / k) = k * (b + th1) + &2 * pi` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD; REWRITE_TAC[MOI_PDG_CEXP_PERIOD]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:complex->real^N) y1 = R y2` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:(real^N)topology`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                         `U:real^N->bool`; `phi:real^N->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART_INJ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `y1:complex = y2` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `Cx(e / &2) * cexp(ii * Cx(b + th1)) = Cx(e / &2) * cexp(ii * Cx(b + th'))`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; CX_INJ] THEN
  SUBGOAL_THEN `~(e / &2 = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `ii * Cx(b + th1) = ii * Cx(b + th')` MP_TAC THENL
   [MATCH_MP_TAC COMPLEX_EQ_CEXP THEN ASM_REWRITE_TAC[IM_MUL_II; RE_CX] THEN
    MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; II_NZ; CX_INJ] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_CONE2_SYM = prove
 (`!u v:complex. moi_pdg_cone2 u v = moi_pdg_cone2 v u`,
  REWRITE_TAC[moi_pdg_cone2; EXTENSION; IN_ELIM_THM] THEN MESON_TAC[VECTOR_ADD_SYM]);;

let MOI_PDG_DEV_ORIENT = prove
 (`!L s (w:real^N) (Q:real^N->complex) d.
      simplicial_complex L /\ s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s /\ &0 < d /\
      moi_smo_cell_smooth s Q /\
      (!x y. x IN s /\ y IN s /\ Q x = Q y ==> x = y) /\
      Q w = vec 0 /\
      (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
           ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Q x = t % a)
      ==> ?v1 v2 u1 u2 e (R:complex->real^N).
            ~(v1 = w) /\ ~(v2 = w) /\ ~(v1 = v2) /\ ~(affine_dependent {w,v1,v2}) /\
            s = convex hull {w,v1,v2} /\ segment[w,v1] IN L /\ segment[w,v2] IN L /\
            norm u1 = &1 /\ norm u2 = &1 /\ &0 < Im(cnj u1 * u2) /\ &0 < e /\
            smooth_map_on (ball(vec 0,e)) R /\
            (!y z. y IN ball(vec 0,e) /\ frechet_derivative R (at y) z = vec 0 ==> z = vec 0) /\
            (!y z. y IN ball(vec 0,e)
                   ==> frechet_derivative R (at y) z IN span {v1 - w, v2 - w}) /\
            (!y. y IN ball(vec 0,e) ==> dist(w,R y) < d) /\
            (!y. y IN ball(vec 0,e) INTER moi_pdg_cone2 u1 u2
                 ==> R y IN s /\ Q(R y) = y) /\
            (!x. x IN s /\ norm(Q x) < e ==> Q x IN moi_pdg_cone2 u1 u2 /\ R(Q x) = x) /\
            (!t. &0 <= t /\ t < e
                 ==> R(Cx t * u1) IN segment[w,v1] /\ R(Cx t * u2) IN segment[w,v2]) /\
            (!x. x IN segment[w,v1] ==> ?t. &0 <= t /\ Q x = Cx t * u1) /\
            (!x. x IN segment[w,v2] ==> ?t. &0 <= t /\ Q x = Cx t * u2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`; `w:real^N`]
    MOI_PDG_TRI_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^N` (X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`w:real^N`; `x1:real^N`; `x2:real^N`] MOI_PDG_TRI_SEGS) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!v:real^N. ~(v = w) /\ segment[w,v] IN L /\ segment[w,v] SUBSET s
                ==> ?a. !x. x IN segment[w,v] ==> ?t. &0 <= t /\ (Q:real^N->complex) x = t % a`
  (LABEL_TAC "edge") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^N`; `x1:real^N`; `x2:real^N`; `Q:real^N->complex`; `d:real`]
    MOI_PDG_CORNER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `moi_smo_cell_smooth s (Q:real^N->complex)` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `!x y. x IN s /\ y IN s /\ (Q:real^N->complex) x = Q y ==> x = y` THEN
      ASM_REWRITE_TAC[];
      USE_THEN "edge" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      USE_THEN "edge" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:complex` (X_CHOOSE_THEN `a2:complex`
   (X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `R0:complex->real^N` STRIP_ASSUME_TAC)))) THEN
  ASM_CASES_TAC `&0 < Im(cnj a1 * a2)` THENL
   [MAP_EVERY EXISTS_TAC [`x1:real^N`; `x2:real^N`; `a1:complex`; `a2:complex`;
                          `e0:real`; `R0:complex->real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x2:real^N`; `x1:real^N`; `a2:complex`; `a1:complex`;
                        `e0:real`; `R0:complex->real^N`] THEN
  SUBGOAL_THEN `{w:real^N,x2,x1} = {w,x1,x2}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `span {x2 - w:real^N, x1 - w} = span {x1 - w, x2 - w}` SUBST1_TAC THENL
   [AP_TERM_TAC THEN SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[MOI_PDG_CONE2_SYM] THEN
  SUBGOAL_THEN `&0 < Im(cnj a2 * a1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `cnj a2 * a1 = cnj(cnj a1 * a2)` SUBST1_TAC THENL
     [REWRITE_TAC[CNJ_MUL; CNJ_CNJ] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    REWRITE_TAC[IM_CNJ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_PDG_DEV = prove
 (`!L (top:(real^N)topology) sigma U phi k b (Q:real^N->complex) s w d.
      simplicial_complex L /\ s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s /\
      smooth_manifold_atlas top sigma /\ (U,phi) IN sigma /\ &0 < k /\ &0 < d /\
      (!x. x IN s /\ dist(w,x) < d ==> x IN U) /\
      moi_smo_cell_smooth s Q /\
      (!x y. x IN s /\ y IN s /\ Q x = Q y ==> x = y) /\
      Q w = vec 0 /\
      (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx b)) * Q x)) /\
      (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
           ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Q x = t % a) /\
      (!x. x IN s INTER U ==> phi x = moi_smo_ang k b (Q x))
      ==> ?v1 v2 th1 th2 e (R:complex->real^N).
            ~(v1 = w) /\ ~(v2 = w) /\ ~(v1 = v2) /\ ~(affine_dependent {w,v1,v2}) /\
            s = convex hull {w,v1,v2} /\ segment[w,v1] IN L /\ segment[w,v2] IN L /\
            &0 <= th1 /\ th1 < th2 /\ th2 <= pi /\ th2 - th1 < pi /\
            k * (th2 - th1) < &2 * pi /\
            &0 < e /\ smooth_map_on (ball(vec 0,e)) R /\
            (!y z. y IN ball(vec 0,e) /\ frechet_derivative R (at y) z = vec 0 ==> z = vec 0) /\
            (!y z. y IN ball(vec 0,e)
                   ==> frechet_derivative R (at y) z IN span {v1 - w, v2 - w}) /\
            (!y. y IN ball(vec 0,e) ==> dist(w,R y) < d) /\
            (!y. y IN ball(vec 0,e) INTER
                     moi_pdg_cone2 (cexp(ii * Cx(b + th1))) (cexp(ii * Cx(b + th2)))
                 ==> R y IN s /\ R y IN U /\ Q(R y) = y) /\
            (!x. x IN s /\ norm(Q x) < e
                 ==> Q x IN moi_pdg_cone2 (cexp(ii * Cx(b + th1))) (cexp(ii * Cx(b + th2))) /\
                     R(Q x) = x) /\
            (!t. &0 <= t /\ t < e
                 ==> R(Cx t * cexp(ii * Cx(b + th1))) IN segment[w,v1] /\
                     R(Cx t * cexp(ii * Cx(b + th2))) IN segment[w,v2]) /\
            (!x. x IN segment[w,v1] ==> ?t. &0 <= t /\ Q x = Cx t * cexp(ii * Cx(b + th1))) /\
            (!x. x IN segment[w,v2] ==> ?t. &0 <= t /\ Q x = Cx t * cexp(ii * Cx(b + th2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`; `w:real^N`;
                 `Q:real^N->complex`; `d:real`] MOI_PDG_DEV_ORIENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `v2:real^N`
   (X_CHOOSE_THEN `u1:complex` (X_CHOOSE_THEN `u2:complex`
   (X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `R:complex->real^N` STRIP_ASSUME_TAC)))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s:real^N->bool`)) THEN
  SUBGOAL_THEN `!v u:complex. norm u = &1 /\ v IN convex hull {w,v1,v2} /\ ~(v = w:real^N) /\
                  (?t. &0 <= t /\ (Q:real^N->complex) v = Cx t * u)
                  ==> &0 <= Im(cexp(--(ii * Cx b)) * u)`
  (LABEL_TAC "half") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `~(t = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(Q:real^N->complex) v = Q w` MP_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Im(cexp(--(ii * Cx b)) * (Q:real^N->complex) v)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_RING `a * Cx t * u = Cx t * (a * u)`; IM_MUL_CX] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `t:real` THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_TRI_SEGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real`; `u1:complex`; `u2:complex`] MOI_PDG_DEV_ANGLES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "half" MATCH_MP_TAC THENL
     [EXISTS_TAC `v1:real^N`; EXISTS_TAC `v2:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `th1:real` (X_CHOOSE_THEN `th2:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`v1:real^N`; `v2:real^N`; `th1:real`; `th2:real`;
                        `e:real`; `R:complex->real^N`] THEN
  SUBGOAL_THEN
   `!y. y IN ball(vec 0,e) INTER
            moi_pdg_cone2 (cexp(ii * Cx(b + th1))) (cexp(ii * Cx(b + th2)))
        ==> (R:complex->real^N) y IN convex hull {w,v1,v2} /\ R y IN U /\ (Q:real^N->complex)(R y) = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(R:complex->real^N) y IN convex hull {w,v1,v2} /\ (Q:real^N->complex)(R y) = y` STRIP_ASSUME_TAC
    THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `dist(w:real^N,x)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN convex hull {w,v1,v2} /\ norm((Q:real^N->complex) x) < e
                  ==> Q x IN moi_pdg_cone2 (cexp(ii * Cx(b + th1))) (cexp(ii * Cx(b + th2))) /\
                      (R:complex->real^N)(Q x) = x`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`top:(real^N)topology`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
       `U:real^N->bool`; `phi:real^N->real^2`; `k:real`; `b:real`; `convex hull {w:real^N,v1,v2}`;
       `Q:real^N->complex`; `R:complex->real^N`; `e:real`; `th1:real`; `th2:real`]
       MOI_PDG_DEV_KBOUND) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(ASSUME `u1 = cexp(ii * Cx(b + th1))`);
              GSYM(ASSUME `u2 = cexp(ii * Cx(b + th2))`)] THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_FD_CHAIN = prove
 (`!(f:real^M->real^N) (g:real^N->real^P) x.
      f differentiable at x /\ g differentiable at (f x)
      ==> frechet_derivative (g o f) (at x) =
          frechet_derivative g (at (f x)) o frechet_derivative f (at x)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
  MATCH_MP_TAC DIFF_CHAIN_AT THEN ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]);;

let MOI_PDG_DERIV_DIR = prove
 (`!(f:complex->real^M) g y u e.
      f differentiable at y /\ g differentiable at y /\ &0 < e /\
      (!t. &0 <= t /\ t < e ==> f(y + Cx t * u) = g(y + Cx t * u))
      ==> frechet_derivative f (at y) u = frechet_derivative g (at y) u`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `l = \x:real^1. Cx(drop x) * (u:complex)` THEN
  SUBGOAL_THEN `linear (l:real^1->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL;
      COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k:complex->real^M. k differentiable at y
      ==> ((\x. k(y + (l:real^1->complex) x)) has_derivative (frechet_derivative k (at y) o l))
          (at (vec 0))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\x. (k:complex->real^M)(y + (l:real^1->complex) x)) = k o (\x. y + (l:real^1->complex) x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real^1. y:complex`; `\h:real^1. vec 0:complex`;
                     `l:real^1->complex`; `l:real^1->complex`; `at (vec 0:real^1)`]
        HAS_DERIVATIVE_ADD) THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_LINEAR; VECTOR_ADD_LID; ETA_AX];
      REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME `linear (l:real^1->complex)`); VECTOR_ADD_RID] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(frechet_derivative (f:complex->real^M) (at y) o (l:real^1->complex)) =
                (frechet_derivative g (at y) o l)` MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC [`\x. (f:complex->real^M)(y + (l:real^1->complex) x)`; `vec 0:real^1`;
                          `vec 0:real^1`; `lift(e / &2)`] THEN
    SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,lift(e / &2)]` ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[VEC_COMPONENT; LIFT_COMPONENT] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
      MAP_EVERY EXISTS_TAC [`\x. (g:complex->real^M)(y + (l:real^1->complex) x)`; `&1`] THEN
      ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        STRIP_TAC THEN EXPAND_TAC "l" THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `(f:complex->real^M)(y + Cx t * u)`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN EXPAND_TAC "l" THEN
  REWRITE_TAC[o_THM; LIFT_DROP; COMPLEX_MUL_LID]);;

let MOI_PDG_DERIV_CONE = prove
 (`!(f:complex->real^M) g u1 u2 e y.
      ~(Im(cnj u1 * u2) = &0) /\ f differentiable at y /\ g differentiable at y /\
      y IN ball(vec 0,e) INTER moi_pdg_cone2 u1 u2 /\
      (!z. z IN ball(vec 0,e) INTER moi_pdg_cone2 u1 u2 ==> f z = g z)
      ==> frechet_derivative f (at y) = frechet_derivative g (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!u:complex. (u = u1 \/ u = u2) ==>
       frechet_derivative (f:complex->real^M) (at y) u = frechet_derivative g (at y) u`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_PDG_DERIV_DIR THEN
    EXISTS_TAC `(e - norm(y:complex)) / (norm(u:complex) + &1)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `y IN ball(vec 0:complex,e) INTER moi_pdg_cone2 u1 u2` THEN
    REWRITE_TAC[IN_INTER; IN_BALL_0] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm(u:complex) + &1` ASSUME_TAC THENL
     [MP_TAC(ISPEC `u:complex` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTER; IN_BALL_0] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(y:complex) + t * norm(u:complex)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm(y:complex) + norm(Cx t * u)` THEN
        REWRITE_TAC[NORM_TRIANGLE; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
        ASM_REWRITE_TAC[real_abs; REAL_LE_REFL];
        UNDISCH_TAC `t < (e - norm(y:complex)) / (norm(u:complex) + &1)` THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
        MP_TAC(ISPEC `u:complex` NORM_POS_LE) THEN
        UNDISCH_TAC `&0 <= t` THEN CONV_TAC REAL_ARITH];
      UNDISCH_TAC `(y:complex) IN moi_pdg_cone2 u1 u2` THEN
      REWRITE_TAC[moi_pdg_cone2; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THENL
       [MAP_EVERY EXISTS_TAC [`a + t:real`; `b:real`];
        MAP_EVERY EXISTS_TAC [`a:real`; `b + t:real`]] THEN
      ASM_REWRITE_TAC[COMPLEX_CMUL; CX_ADD] THEN
      (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC COMPLEX_RING])];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:complex` THEN
  MP_TAC(ISPECL [`u1:complex`; `u2:complex`; `z:complex`] MOI_PDG_CONE2_COORDS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LINEAR_FRECHET_DERIVATIVE]);;

let MOI_PDG_TRI_H = prove
 (`!(f:real^3->real^3) (h:real^N->real^3) s w v1 v2 (R:complex->real^N) e u1 u2.
      orthogonal_transformation f /\ ~((f(h w))$3 = &1) /\
      moi_smo_cell_smooth s h /\ s = convex hull {w,v1,v2} /\
      (!x. x IN s ==> h x IN sphere(vec 0,&1)) /\
      ~(Im(cnj u1 * u2) = &0) /\ &0 < e /\ smooth_map_on (ball(vec 0,e)) R /\
      R(vec 0) = w /\
      (!y z. y IN ball(vec 0,e) /\ frechet_derivative R (at y) z = vec 0 ==> z = vec 0) /\
      (!y z. y IN ball(vec 0,e)
             ==> frechet_derivative R (at y) z IN span {v1 - w, v2 - w}) /\
      (!y. y IN ball(vec 0,e) INTER moi_pdg_cone2 u1 u2 ==> R y IN s)
      ==> ?e' H. &0 < e' /\ e' <= e /\ smooth_map_on (ball(vec 0,e')) (H:complex->complex) /\
                 H(vec 0) = moi_pdg_st f (h w) /\
                 (!y. y IN ball(vec 0,e') INTER moi_pdg_cone2 u1 u2
                      ==> H y = moi_pdg_st f (h(R y)) /\ ~((f(h(R y)))$3 = &1)) /\
                 (!y z. y IN ball(vec 0,e') INTER moi_pdg_cone2 u1 u2 /\
                        frechet_derivative H (at y) z = vec 0 ==> z = vec 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s:real^N->bool`)) THEN
  UNDISCH_TAC `moi_smo_cell_smooth (convex hull {w:real^N,v1,v2}) (h:real^N->real^3)` THEN
  REWRITE_TAC[moi_smo_cell_smooth] THEN
  DISCH_THEN(X_CHOOSE_THEN `u0:real^N->bool` (X_CHOOSE_THEN `g:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:real^N) IN convex hull {w,v1,v2}` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `O = {p:real^3 | ~(((f:real^3->real^3) p)$3 = &1)}` THEN
  SUBGOAL_THEN `linear (f:real^3->real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC ORTHOGONAL_TRANSFORMATION_LINEAR THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `open(O:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[MOI_PDG_ST_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (moi_pdg_st (f:real^3->real^3))` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN ASM_SIMP_TAC[MOI_PDG_ST_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `(R:complex->real^N) continuous_on ball(vec 0,e)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^3) continuous_on u0` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ABBREV_TAC `B1 = {y | y IN ball(vec 0:complex,e) /\ (R:complex->real^N) y IN u0}` THEN
  SUBGOAL_THEN `open(B1:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B1" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `B = {y | y IN B1 /\ ((g:real^N->real^3) o (R:complex->real^N)) y IN O}` THEN
  SUBGOAL_THEN `open(B:complex->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:complex,e)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "B1" THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u0:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "B1" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:complex) IN B` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["B"; "B1"; "O"] THEN
    REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL; o_THM] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(g:real^N->real^3) w = h w` SUBST1_TAC THENL
     [MATCH_MP_TAC(ASSUME `!x. x IN convex hull {w:real^N,v1,v2} ==> (g:real^N->real^3) x = h x`) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `convex hull {w:real^N,v1,v2} SUBSET u0` THEN
    UNDISCH_TAC `(w:real^N) IN convex hull {w,v1,v2}` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `B:complex->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y. y IN ball(vec 0,min e1 e)
                    ==> y IN ball(vec 0:complex,e) /\ (R:complex->real^N) y IN u0 /\
                        ~(((f:real^3->real^3)((g:real^N->real^3)(R y)))$3 = &1)`
  (LABEL_TAC "inB") THENL
   [X_GEN_TAC `y:complex` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:complex) IN B` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `ball(vec 0:complex,e1)`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_BALL];
      MAP_EVERY EXPAND_TAC ["B"; "B1"; "O"] THEN REWRITE_TAC[IN_ELIM_THM; o_THM; IN_BALL] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(vec 0,min e1 e)) ((g:real^N->real^3) o (R:complex->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `u0:real^N->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN USE_THEN "inB" (fun th -> MESON_TAC[th]);
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:complex,e)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN USE_THEN "inB" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  ABBREV_TAC `H = moi_pdg_st (f:real^3->real^3) o (g:real^N->real^3) o (R:complex->real^N)` THEN
  SUBGOAL_THEN `smooth_map_on (ball(vec 0,min e1 e)) (H:complex->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "H" THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN EXISTS_TAC `O:real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN
    EXPAND_TAC "O" THEN REWRITE_TAC[IN_ELIM_THM] THEN USE_THEN "inB" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`min e1 e`; `H:complex->complex`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; REAL_ARITH `min a b <= b`] THEN
  SUBGOAL_THEN `!y. y IN ball(vec 0,min e1 e) INTER moi_pdg_cone2 u1 u2
                    ==> (R:complex->real^N) y IN convex hull {w,v1,v2}` (LABEL_TAC "Rs") THENL
   [X_GEN_TAC `y:complex` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `moi_pdg_cone2 u1 u2`)) (concl th) &&
      can (find_term ((=) `(R:complex->real^N) y IN convex hull {w,v1,v2}`)) (concl th))) THEN
    USE_THEN "inB" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(y:complex) IN ball(vec 0,min e1 e)`))) THEN
    MP_TAC(ASSUME `(y:complex) IN moi_pdg_cone2 u1 u2`) THEN SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "H" THEN REWRITE_TAC[o_THM] THEN
    SIMP_TAC[ASSUME `(R:complex->real^N)(vec 0) = w`; ASSUME `!x. x IN convex hull {w:real^N,v1,v2} ==> (g:real^N->real^3) x = h x`;
             ASSUME `(w:real^N) IN convex hull {w,v1,v2}`];
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    USE_THEN "inB" (MP_TAC o SPEC `y:complex`) THEN ANTS_TAC THENL
     [MP_TAC(ASSUME `(y:complex) IN ball(vec 0,min e1 e) INTER moi_pdg_cone2 u1 u2`) THEN SIMP_TAC[IN_INTER]; STRIP_TAC] THEN
    SUBGOAL_THEN `(g:real^N->real^3)((R:complex->real^N) y) = h(R y)` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!x. x IN convex hull {w:real^N,v1,v2} ==> (g:real^N->real^3) x = h x`) THEN
      USE_THEN "Rs" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[o_THM] THEN
    MP_TAC(ASSUME `~(((f:real^3->real^3)((g:real^N->real^3)((R:complex->real^N) y)))$3 = &1)`) THEN
    REWRITE_TAC[ASSUME `(g:real^N->real^3)((R:complex->real^N) y) = h(R y)`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:complex`; `z:complex`] THEN STRIP_TAC THEN
  USE_THEN "inB" (MP_TAC o SPEC `y:complex`) THEN ANTS_TAC THENL
   [MP_TAC(ASSUME `(y:complex) IN ball(vec 0,min e1 e) INTER moi_pdg_cone2 u1 u2`) THEN SIMP_TAC[IN_INTER]; STRIP_TAC] THEN
  SUBGOAL_THEN `(R:complex->real^N) y IN convex hull {w,v1,v2}` ASSUME_TAC THENL
   [USE_THEN "Rs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(R:complex->real^N) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:complex,e)` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^3) differentiable at (R(y:complex))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `u0:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(H:complex->complex) differentiable at y` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `ball(vec 0:complex,min e1 e)` THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ASSUME `(y:complex) IN ball(vec 0,min e1 e) INTER moi_pdg_cone2 u1 u2`) THEN SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_pdg_sti (f:real^3->real^3) differentiable at ((H:complex->complex) y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; MOI_PDG_STI_SMOOTH];
    ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (moi_pdg_sti (f:real^3->real^3) o (H:complex->complex)) (at y) =
                frechet_derivative ((g:real^N->real^3) o (R:complex->real^N)) (at y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_DERIV_CONE THEN
    MAP_EVERY EXISTS_TAC [`u1:complex`; `u2:complex`; `min e1 e`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y':complex` THEN DISCH_TAC THEN
      USE_THEN "inB" (MP_TAC o SPEC `y':complex`) THEN ANTS_TAC THENL
       [MP_TAC(ASSUME `(y':complex) IN ball(vec 0,min e1 e) INTER moi_pdg_cone2 u1 u2`) THEN SIMP_TAC[IN_INTER]; STRIP_TAC] THEN
      SUBGOAL_THEN `(R:complex->real^N) y' IN convex hull {w,v1,v2}` ASSUME_TAC THENL
       [USE_THEN "Rs" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "H" THEN REWRITE_TAC[o_THM] THEN MATCH_MP_TAC MOI_PDG_STI_ST THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[ASSUME `!x. x IN convex hull {w:real^N,v1,v2} ==> (g:real^N->real^3) x = h x`; ASSUME `!x. x IN convex hull {w:real^N,v1,v2} ==> (h:real^N->real^3) x IN sphere(vec 0,&1)`;
               ASSUME `(R:complex->real^N) y' IN convex hull {w,v1,v2}`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (moi_pdg_sti (f:real^3->real^3))
                  (at ((H:complex->complex) y)))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative ((g:real^N->real^3) o (R:complex->real^N)) (at y) z = vec 0`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `moi_pdg_sti (f:real^3->real^3) o (H:complex->complex)`)) (concl th))) THEN
    SIMP_TAC[MOI_PDG_FD_CHAIN; o_THM; ASSUME `(H:complex->complex) differentiable at y`;
             ASSUME `moi_pdg_sti (f:real^3->real^3) differentiable at ((H:complex->complex) y)`;
             ASSUME `frechet_derivative (H:complex->complex) (at y) z = vec 0`] THEN
    MATCH_MP_TAC(ISPEC `frechet_derivative (moi_pdg_sti (f:real^3->real^3))
                          (at ((H:complex->complex) y))` LINEAR_0) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SIMP_TAC[MOI_PDG_FD_CHAIN; o_THM; ASSUME `(R:complex->real^N) differentiable at y`;
           ASSUME `(g:real^N->real^3) differentiable at (R(y:complex))`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `frechet_derivative (R:complex->real^N) (at y) z = vec 0` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `moi_smo_tangent:(real^N->bool)->real^N->bool`)) (concl th))) THEN
    EXISTS_TAC `(R:complex->real^N) y` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!a b x:real^N. x IN a /\ a SUBSET b ==> x IN b`) THEN
    EXISTS_TAC `span {v1 - w:real^N, v2 - w}` THEN
    REWRITE_TAC[MOI_PDG_TRI_TANGENT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `frechet_derivative (R:complex->real^N) (at y) z`)) (concl th) &&
    is_forall(concl th))) THEN
  EXISTS_TAC `y:complex` THEN ASM_REWRITE_TAC[]);;


(* Sectors in the chart and the inverse angle map moi_pdg_angz. *)

let moi_pdg_angz = new_definition
 `moi_pdg_angz (k:real) (c:real) (z:complex) =
    if z = Cx(&0) then Cx(&0) else moi_pdg_angf k c z`;;

let moi_pdg_sec = new_definition
 `moi_pdg_sec (k:real) (a:real) (t1:real) (t2:real) =
    {Cx r * cexp(ii * Cx(k * (a + t))) | &0 <= r /\ t1 <= t /\ t <= t2}`;;

let MOI_PDG_ANGZ_NORM = prove
 (`!k c z. norm(moi_pdg_angz k c z) = norm z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_angz] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MOI_PDG_ANGF_NORM]);;

let MOI_PDG_ANGZ_HOMOG = prove
 (`!k c s z. &0 <= s ==> moi_pdg_angz k c (Cx s * z) = Cx s * moi_pdg_angz k c z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_angz] THEN
  ASM_CASES_TAC `s = &0` THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO] THEN
  ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ENTIRE; CX_INJ] THEN
  MATCH_MP_TAC MOI_PDG_ANGF_HOMOG THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_ANGZ_POLAR = prove
 (`!k a t1 t2 r t.
      &0 < k /\ &0 <= r /\ t1 <= t /\ t <= t2 /\ k * (t2 - t1) < &2 * pi
      ==> moi_pdg_angz (inv k) (k * (a + (t1 + t2) / &2))
            (Cx r * cexp(ii * Cx(k * (a + t)))) =
          Cx r * cexp(ii * Cx(a + t))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r = &0` THENL
   [ASM_REWRITE_TAC[moi_pdg_angz; COMPLEX_MUL_LZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_pdg_angz; COMPLEX_ENTIRE; CX_INJ; CEXP_NZ] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`inv k`; `k * (a + (t1 + t2) / &2)`; `r:real`;
                 `k * (t - (t1 + t2) / &2)`] MOI_PDG_ANGF_POLAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs(k * (t - (t1 + t2) / &2)) <= k * ((t2 - t1) / &2)` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `k * (t2 - t1) < &2 * pi` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `k * (a + (t1 + t2) / &2) + k * (t - (t1 + t2) / &2) = k * (a + t)`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD);;

let MOI_PDG_ANG_POLAR0 = prove
 (`!k b r t. &0 <= r /\ &0 <= t /\ t <= pi
             ==> moi_smo_ang k b (Cx r * cexp(ii * Cx(b + t))) =
                 Cx r * cexp(ii * Cx(k * (b + t)))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r = &0` THENL
   [ASM_REWRITE_TAC[moi_smo_ang; COMPLEX_MUL_LZERO; COMPLEX_NORM_CX; REAL_ABS_0];
    MATCH_MP_TAC MOI_PDG_ANG_POLAR THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_CONE2_POLAR = prove
 (`!a d z. &0 < d /\ d < pi
           ==> (z IN moi_pdg_cone2 (cexp(ii * Cx a)) (cexp(ii * Cx(a + d))) <=>
                ?r t. &0 <= r /\ &0 <= t /\ t <= d /\ z = Cx r * cexp(ii * Cx(a + t)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_PDG_CONE2_ANGLE] THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&0`; `&0`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL; COMPLEX_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`r:real`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `r = &0` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`r:real`; `t:real`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

let MOI_PDG_CONE2_KPOLAR = prove
 (`!k a t1 t2 z.
      &0 < k /\ t1 < t2 /\ k * (t2 - t1) < pi
      ==> (z IN moi_pdg_cone2 (cexp(ii * Cx(k * (a + t1)))) (cexp(ii * Cx(k * (a + t2)))) <=>
           ?r t. &0 <= r /\ t1 <= t /\ t <= t2 /\ z = Cx r * cexp(ii * Cx(k * (a + t))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k * (a + t2) = k * (a + t1) + k * (t2 - t1)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < k * (t2 - t1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_PDG_CONE2_POLAR] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `t1 + u / k`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> t1 <= t1 + x`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= t2 - t1 ==> t1 + x <= t2`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD];
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `k * (t - t1)`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC]]);;

let MOI_PDG_SEC_CONIC = prove
 (`!k a t1 t2 z s. z IN moi_pdg_sec k a t1 t2 /\ &0 <= s
                   ==> Cx s * z IN moi_pdg_sec k a t1 t2`,
  REWRITE_TAC[moi_pdg_sec; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`s * r:real`; `t:real`] THEN ASM_REWRITE_TAC[CX_MUL] THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; CONV_TAC COMPLEX_RING]);;

let MOI_PDG_SEC_HALVES = prove
 (`!k a t1 t2.
      &0 < k /\ t1 < t2 /\ k * (t2 - t1) < &2 * pi
      ==> moi_pdg_sec k a t1 t2 =
          moi_pdg_cone2 (cexp(ii * Cx(k * (a + t1))))
                        (cexp(ii * Cx(k * (a + (t1 + t2) / &2)))) UNION
          moi_pdg_cone2 (cexp(ii * Cx(k * (a + (t1 + t2) / &2))))
                        (cexp(ii * Cx(k * (a + t2))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_UNION] THEN X_GEN_TAC `z:complex` THEN
  MP_TAC(ISPECL [`k:real`; `a:real`; `t1:real`; `(t1 + t2) / &2`; `z:complex`]
    MOI_PDG_CONE2_KPOLAR) THEN
  MP_TAC(ISPECL [`k:real`; `a:real`; `(t1 + t2) / &2`; `t2:real`; `z:complex`]
    MOI_PDG_CONE2_KPOLAR) THEN
  ASM_REWRITE_TAC[REAL_ARITH `t1 < (t1 + t2) / &2 <=> t1 < t2`;
                  REAL_ARITH `(t1 + t2) / &2 < t2 <=> t1 < t2`] THEN
  REWRITE_TAC[REAL_ARITH `t2 - (t1 + t2) / &2 = (t2 - t1) / &2`;
              REAL_ARITH `(t1 + t2) / &2 - t1 = (t2 - t1) / &2`] THEN
  SUBGOAL_THEN `k * (t2 - t1) / &2 < pi` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `k * (t2 - t1) < &2 * pi` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[moi_pdg_sec; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `t <= (t1 + t2) / &2` THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`r:real`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_PDG_TRI_EDGE_AT = prove
 (`!L s t (w:real^N) v1 v2.
      simplicial_complex L /\ s IN L /\ t IN L /\
      s = convex hull {w,v1,v2} /\ ~(affine_dependent {w,v1,v2}) /\
      ~(v1 = w) /\ ~(v2 = w) /\ aff_dim s = &2 /\
      aff_dim t = &1 /\ w IN t /\ t SUBSET s
      ==> t = segment[w,v1] \/ t = segment[w,v2]`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s:real^N->bool`)) THEN
  SUBGOAL_THEN `t face_of (convex hull {w:real^N,v1,v2})` MP_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `convex hull {w:real^N,v1,v2}`;
                   `t:real^N->bool`] MOI_PDG_SC_INTER_FACE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex hull {w:real^N,v1,v2} INTER t = t` SUBST1_TAC THENL
     [UNDISCH_TAC `t SUBSET convex hull {w:real^N,v1,v2}` THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N) IN c` ASSUME_TAC THENL
   [ASM_CASES_TAC `(w:real^N) IN c` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(affine_dependent {w:real^N,v1,v2})` THEN REWRITE_TAC[affine_dependent] THEN
    EXISTS_TAC `w:real^N` THEN REWRITE_TAC[IN_INSERT] THEN
    SUBGOAL_THEN `{w:real^N,v1,v2} DELETE w = {v1,v2}` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`~(v1:real^N = w)`; `~(v2:real^N = w)`] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!a b x:real^N. x IN a /\ a SUBSET b ==> x IN b`) THEN
    EXISTS_TAC `convex hull {v1:real^N,v2}` THEN REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    SUBGOAL_THEN `t SUBSET convex hull {v1:real^N,v2}` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN
      MAP_EVERY UNDISCH_TAC [`c SUBSET {w:real^N,v1,v2}`; `~((w:real^N) IN c)`] THEN
      SET_TAC[];
      UNDISCH_TAC `(w:real^N) IN t` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c = {w:real^N} \/ c = {w,v1} \/ c = {w,v2} \/ c = {w,v1,v2}` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`c SUBSET {w:real^N,v1,v2}`; `(w:real^N) IN c`] THEN
    ASM_CASES_TAC `(v1:real^N) IN c` THEN ASM_CASES_TAC `(v2:real^N) IN c` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `aff_dim(t:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_SING; AFF_DIM_SING] THEN INT_ARITH_TAC;
    DISJ1_TAC THEN ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL];
    DISJ2_TAC THEN ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL];
    UNDISCH_TAC `aff_dim(t:real^N->bool) = &1` THEN
    UNDISCH_TAC `aff_dim(convex hull {w:real^N,v1,v2}) = &2` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let MOI_PDG_DEV_RELINT = prove
 (`!L s (w:real^N) v1 v2 dl x.
      simplicial_complex L /\ s IN L /\ aff_dim s = &2 /\ {w} IN L /\
      s = convex hull {w,v1,v2} /\ ~(affine_dependent {w,v1,v2}) /\
      ~(v1 = w) /\ ~(v2 = w) /\
      (!w t x. {w} IN L /\ t IN L /\ ~(w IN t) /\ x IN t ==> dl <= dist(w,x)) /\
      x IN s /\ dist(w,x) < dl /\ ~(x = w) /\ ~(x IN segment[w,v1]) /\
      ~(x IN segment[w,v2])
      ==> x IN relative_interior s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s:real^N->bool`)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `x:real^N`] MOI_PDG_CARRIER) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `t SUBSET convex hull {w:real^N,v1,v2}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_REL_FACE THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `x:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN t` ASSUME_TAC THENL
   [ASM_CASES_TAC `(w:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `dl <= dist(w:real^N,x)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `dl:real`)) (concl th) && is_forall(concl th))) THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t:real^N->bool) = &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim(t:real^N->bool) <= &2` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `aff_dim(convex hull {w:real^N,v1,v2}) = &2`)) THEN
      MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `t:real^N->bool` AFF_DIM_GE) THEN
    REWRITE_TAC[IMP_IMP] THEN
    REWRITE_TAC[INT_ARITH `!a:int. -- &1 <= a /\ a <= &2 <=>
                           a = -- &1 \/ a = &0 \/ a = &1 \/ a = &2`] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC `aff_dim(t:real^N->bool) = -- &1` THEN REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN
      UNDISCH_TAC `(x:real^N) IN t` THEN SET_TAC[];
      UNDISCH_TAC `aff_dim(t:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `~(x:real^N = w)` THEN
      MAP_EVERY UNDISCH_TAC [`(x:real^N) IN {a}`; `(w:real^N) IN {a}`] THEN SET_TAC[];
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `convex hull {w:real^N,v1,v2}`; `t:real^N->bool`;
                     `w:real^N`; `v1:real^N`; `v2:real^N`] MOI_PDG_TRI_EDGE_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t = convex hull {w:real^N,v1,v2}` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC MOI_PDG_FACE_EQ THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_POLAR_NE = prove
 (`!r c t t'. &0 < r /\ &0 <= c /\ abs(t - t') < &2 * pi /\ ~(t = t')
              ==> ~(Cx r * cexp(ii * Cx t) = Cx c * cexp(ii * Cx t'))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r = c:real` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:complex->real`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cexp(ii * Cx t) = cexp(ii * Cx t')` ASSUME_TAC THENL
   [MATCH_MP_TAC(COMPLEX_FIELD `!a x y. ~(a = Cx(&0)) /\ a * x = a * y ==> x = y`) THEN
    EXISTS_TAC `Cx c` THEN ASM_REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ii * Cx t = ii * Cx t'` MP_TAC THENL
   [MATCH_MP_TAC COMPLEX_EQ_CEXP THEN ASM_REWRITE_TAC[IM_MUL_II; RE_CX];
    REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; II_NZ; CX_INJ] THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_IM_CNJ_UNIT = prove
 (`!a b. Im(cnj(cexp(ii * Cx a)) * cexp(ii * Cx b)) = sin(b - a)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`a:real`; `b:real`; `&1`] MOI_PDG_IM_CNJ_POLAR) THEN
  REWRITE_TAC[COMPLEX_MUL_LID; REAL_MUL_LID]);;

let MOI_PDG_STAR = prove
 (`!L (w:real^N) dl x.
      simplicial_complex L /\ {w} IN L /\
      (!s. s IN L /\ ~(s = {}) ==> ?t. t IN L /\ aff_dim t = &2 /\ s SUBSET t) /\
      (!w t x. {w} IN L /\ t IN L /\ ~(w IN t) /\ x IN t ==> dl <= dist(w,x)) /\
      x IN UNIONS L /\ dist(w,x) < dl
      ==> ?s. s IN L /\ aff_dim s = &2 /\ w IN s /\ x IN s`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS L` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N) IN t` ASSUME_TAC THENL
   [ASM_CASES_TAC `(w:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `dl <= dist(w:real^N,x)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `dl:real`)) (concl th) && is_forall(concl th))) THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
    can (find_term ((=) `aff_dim(t:real^N->bool) = &2`)) (concl th))) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM SET_TAC[]);;

let moi_pdg_vtri = new_definition
 `moi_pdg_vtri (L:(real^N->bool)->bool) (U:real^N->bool) (phi:real^N->real^2) (k:real)
               (f:real^3->real^3) (h:real^N->real^3) (w:real^N) (s:real^N->bool)
               (bs:real) (Qs:real^N->complex) (v1:real^N) (v2:real^N) (th1:real)
               (th2:real) (e:real) (R:complex->real^N) (H:complex->complex) <=>
    ~(v1 = w) /\ ~(v2 = w) /\ ~(v1 = v2) /\ ~(affine_dependent {w,v1,v2}) /\
    s = convex hull {w,v1,v2} /\ segment[w,v1] IN L /\ segment[w,v2] IN L /\
    &0 <= th1 /\ th1 < th2 /\ th2 <= pi /\ th2 - th1 < pi /\ k * (th2 - th1) < &2 * pi /\
    &0 < e /\ smooth_map_on (ball(vec 0,e)) H /\ H(vec 0) = vec 0 /\
    (!x. x IN s INTER U ==> phi x = moi_smo_ang k bs (Qs x)) /\
    (!y. y IN ball(vec 0,e) INTER
             moi_pdg_cone2 (cexp(ii * Cx(bs + th1))) (cexp(ii * Cx(bs + th2)))
         ==> R y IN s /\ R y IN U /\ Qs(R y) = y /\
             H y = moi_pdg_st f (h(R y)) /\ ~((f(h(R y)))$3 = &1) /\
             (!z. frechet_derivative H (at y) z = vec 0 ==> z = vec 0)) /\
    (!x. x IN s /\ norm(Qs x) < e
         ==> Qs x IN moi_pdg_cone2 (cexp(ii * Cx(bs + th1))) (cexp(ii * Cx(bs + th2))) /\
             R(Qs x) = x) /\
    (!t. &0 <= t /\ t < e
         ==> R(Cx t * cexp(ii * Cx(bs + th1))) IN segment[w,v1] /\
             R(Cx t * cexp(ii * Cx(bs + th2))) IN segment[w,v2]) /\
    (!x. x IN segment[w,v1] ==> ?t. &0 <= t /\ Qs x = Cx t * cexp(ii * Cx(bs + th1))) /\
    (!x. x IN segment[w,v2] ==> ?t. &0 <= t /\ Qs x = Cx t * cexp(ii * Cx(bs + th2))) /\
    (!r t. &0 < r /\ r < e /\ th1 < t /\ t < th2
           ==> R(Cx r * cexp(ii * Cx(bs + t))) IN relative_interior s)`;;

let MOI_PDG_ST_SOUTH = prove
 (`!(f:real^3->real^3) y. f y = --basis 3 ==> moi_pdg_st f y = vec 0 /\ ~((f y)$3 = &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[moi_pdg_st] THEN
  SIMP_TAC[VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT;
              VECTOR_MUL_COMPONENT; REAL_NEG_0; REAL_MUL_RZERO] THEN
  REAL_ARITH_TAC);;

let MOI_PDG_VTRI_EXISTS = prove
 (`!L sigma U phi k (f:real^3->real^3) (h:real^N->real^3) w s bs (Qs:real^N->real^2) d dl.
      simplicial_complex L /\ s IN L /\ aff_dim s = &2 /\ {w} IN L /\ w IN s /\
      smooth_manifold_atlas (subtopology euclidean (UNIONS L)) sigma /\ (U,phi) IN sigma /\
      &0 < k /\ &0 < d /\ d <= dl /\
      (!x. x IN s /\ dist(w,x) < d ==> x IN U) /\
      (!w t x. {w} IN L /\ t IN L /\ ~(w IN t) /\ x IN t ==> dl <= dist(w,x)) /\
      orthogonal_transformation f /\ f(h w) = --basis 3 /\
      moi_smo_cell_smooth s h /\ (!x. x IN s ==> h x IN sphere(vec 0,&1)) /\
      moi_smo_cell_smooth s Qs /\
      (!x y. x IN s /\ y IN s /\ Qs x = Qs y ==> x = y) /\
      Qs w = vec 0 /\
      (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx bs)) * Qs x)) /\
      (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
           ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Qs x = t % a) /\
      (!x. x IN s INTER U ==> phi x = moi_smo_ang k bs (Qs x))
      ==> ?v1 v2 th1 th2 e R H.
            moi_pdg_vtri L U phi k f h w s bs Qs v1 v2 th1 th2 e R H /\
            (!y. y IN ball(vec 0,e) ==> dist(w,R y) < d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `subtopology euclidean (UNIONS L:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`; `U:real^N->bool`;
                 `phi:real^N->real^2`; `k:real`; `bs:real`; `Qs:real^N->complex`;
                 `s:real^N->bool`; `w:real^N`; `d:real`] MOI_PDG_DEV) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:real^N` (X_CHOOSE_THEN `v2:real^N`
   (X_CHOOSE_THEN `th1:real` (X_CHOOSE_THEN `th2:real`
   (X_CHOOSE_THEN `e0:real` (X_CHOOSE_THEN `R:complex->real^N` STRIP_ASSUME_TAC)))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `s:real^N->bool`)) THEN
  SUBGOAL_THEN `(R:complex->real^N)(vec 0) = w` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
      can (find_term ((=) `(R:complex->real^N)((Qs:real^N->complex) x) = x`)) (concl th))) THEN
    ASM_REWRITE_TAC[NORM_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_pdg_st (f:real^3->real^3) (h(w:real^N)) = vec 0 /\
                ~((f(h w))$3 = &1)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_ST_SOUTH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `h:real^N->real^3`; `convex hull {w:real^N,v1,v2}`;
                 `w:real^N`; `v1:real^N`; `v2:real^N`; `R:complex->real^N`; `e0:real`;
                 `cexp(ii * Cx(bs + th1))`; `cexp(ii * Cx(bs + th2))`] MOI_PDG_TRI_H) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_PDG_IM_CNJ_UNIT] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN MATCH_MP_TAC SIN_POS_PI THEN
      ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `H:complex->complex`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!y:complex. y IN ball(vec 0,e1) ==> y IN ball(vec 0,e0)` (LABEL_TAC "sub")
  THENL
   [REWRITE_TAC[IN_BALL_0] THEN ASM_MESON_TAC[REAL_LTE_TRANS]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v1:real^N`; `v2:real^N`; `th1:real`; `th2:real`; `e1:real`;
                        `R:complex->real^N`; `H:complex->complex`] THEN
  SUBGOAL_THEN `(H:complex->complex)(vec 0) = vec 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(vec 0,e1) INTER
            moi_pdg_cone2 (cexp(ii * Cx(bs + th1))) (cexp(ii * Cx(bs + th2)))
        ==> (R:complex->real^N) y IN convex hull {w,v1,v2} /\ R y IN U /\
            (Qs:real^N->complex)(R y) = y /\
            (H:complex->complex) y = moi_pdg_st f (h(R y)) /\ ~((f(h(R y)))$3 = &1) /\
            (!z. frechet_derivative H (at y) z = vec 0 ==> z = vec 0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:complex) IN ball(vec 0,e0) INTER
         moi_pdg_cone2 (cexp(ii * Cx(bs + th1))) (cexp(ii * Cx(bs + th2)))` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:complex) IN ball(vec 0,e1) INTER
         moi_pdg_cone2 (cexp(ii * Cx(bs + th1))) (cexp(ii * Cx(bs + th2)))` THEN
      REWRITE_TAC[IN_INTER] THEN USE_THEN "sub" (fun th -> MESON_TAC[th]);
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN convex hull {w,v1,v2} /\ norm((Qs:real^N->complex) x) < e1
        ==> Qs x IN moi_pdg_cone2 (cexp(ii * Cx(bs + th1))) (cexp(ii * Cx(bs + th2))) /\
            (R:complex->real^N)(Qs x) = x` ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `(R:complex->real^N)((Qs:real^N->complex) x) = x`)) (concl th) &&
      can (find_term ((=) `e0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t < e1
        ==> (R:complex->real^N)(Cx t * cexp(ii * Cx(bs + th1))) IN segment[w,v1] /\
            R(Cx t * cexp(ii * Cx(bs + th2))) IN segment[w,v2]` ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `segment[w:real^N,v1]`)) (concl th) &&
      can (find_term ((=) `e0:real`)) (concl th))) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(vec 0,e1) ==> dist(w:real^N,(R:complex->real^N) y) < d`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `dist(w:real^N,(R:complex->real^N) y)`)) (concl th))) THEN
    USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r t. &0 < r /\ r < e1 /\ th1 < t /\ t < th2
          ==> (R:complex->real^N)(Cx r * cexp(ii * Cx(bs + t))) IN
              relative_interior (convex hull {w,v1,v2})` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`r:real`; `t:real`] THEN STRIP_TAC THEN
    ABBREV_TAC `y = Cx r * cexp(ii * Cx(bs + t))` THEN
    SUBGOAL_THEN `(y:complex) IN ball(vec 0,e1) INTER
       moi_pdg_cone2 (cexp(ii * Cx(bs + th1))) (cexp(ii * Cx(bs + th2)))` ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN
      REWRITE_TAC[IN_INTER; IN_BALL_0; COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`bs + th1`; `th2 - th1`; `Cx r * cexp(ii * Cx(bs + t))`]
        MOI_PDG_CONE2_POLAR) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ARITH `(bs + th1) + (th2 - th1) = bs + th2`] THEN
      DISCH_THEN SUBST1_TAC THEN MAP_EVERY EXISTS_TAC [`r:real`; `t - th1`] THEN
      REWRITE_TAC[REAL_ARITH `(bs + th1) + (t - th1) = bs + t`] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(R:complex->real^N) y IN convex hull {w,v1,v2} /\
                  (Qs:real^N->complex)(R y) = y /\ dist(w,R y) < d`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_PDG_DEV_RELINT THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `w:real^N`; `v1:real^N`; `v2:real^N`;
                          `dl:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      SUBGOAL_THEN `y = Cx(&0)` MP_TAC THENL
       [ASM_MESON_TAC[COMPLEX_VEC_0]; ALL_TAC] THEN
      SUBST1_TAC(SYM(ASSUME `Cx r * cexp(ii * Cx(bs + t)) = y`)) THEN
      REWRITE_TAC[COMPLEX_ENTIRE; CEXP_NZ; CX_INJ] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(R:complex->real^N) y` o check (fun th ->
        can (find_term ((=) `segment[w:real^N,v1]`)) (concl th) && is_forall(concl th) &&
        not (can (find_term ((=) `e0:real`)) (concl th)) &&
        not (can (find_term ((=) `e1:real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`r:real`; `c:real`; `bs + t`; `bs + th1`] MOI_PDG_POLAR_NE) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(R:complex->real^N) y` o check (fun th ->
        can (find_term ((=) `segment[w:real^N,v2]`)) (concl th) && is_forall(concl th) &&
        not (can (find_term ((=) `e0:real`)) (concl th)) &&
        not (can (find_term ((=) `e1:real`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`r:real`; `c:real`; `bs + t`; `bs + th2`] MOI_PDG_POLAR_NE) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_pdg_vtri] THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC));;

let moi_pdg_vs = new_definition
 `moi_pdg_vs (L:(real^N->bool)->bool) (sigma:((real^N->bool)#(real^N->real^2))->bool)
             (h:real^N->real^3) (w:real^N) (delta:real)
             (U:real^N->bool) (phi:real^N->real^2) (k:real) (b:(real^N->bool)->real)
             (Q:(real^N->bool)->real^N->real^2) (f:real^3->real^3)
             (v1:(real^N->bool)->real^N) (v2:(real^N->bool)->real^N)
             (th1:(real^N->bool)->real) (th2:(real^N->bool)->real)
             (e:(real^N->bool)->real) (R:(real^N->bool)->complex->real^N)
             (H:(real^N->bool)->complex->complex) (rho0:real) <=>
    simplicial_complex L /\
    smooth_manifold_atlas (subtopology euclidean (UNIONS L)) sigma /\
    (U,phi) IN sigma /\ w IN U /\ phi w = vec 0 /\ &0 < k /\ {w} IN L /\
    orthogonal_transformation f /\ f(h w) = --basis 3 /\
    h continuous_on UNIONS L /\ (!x. x IN UNIONS L ==> h x IN sphere(vec 0,&1)) /\
    (!x y. x IN UNIONS L /\ y IN UNIONS L /\ h x = h y ==> x = y) /\
    FINITE {s | s IN L /\ aff_dim s = &2 /\ w IN s} /\
    &0 < rho0 /\ cball(vec 0,rho0) SUBSET IMAGE phi U /\
    (!z. z IN cball(vec 0,rho0)
         ==> chart_inv(U,phi) z IN ball(w,delta) /\
             ?s. s IN L /\ aff_dim s = &2 /\ w IN s /\ chart_inv(U,phi) z IN s) /\
    (!E. E IN L /\ aff_dim E = &1 /\ w IN E
         ==> ?s. s IN L /\ aff_dim s = &2 /\ w IN s /\
                 (E = segment[w,v1 s] \/ E = segment[w,v2 s])) /\
    (!s. s IN L /\ aff_dim s = &2 /\ w IN s
         ==> rho0 < e s /\
             moi_pdg_vtri L U phi k f h w s (b s) (Q s) (v1 s) (v2 s) (th1 s) (th2 s)
                          (e s) (R s) (H s))`;;

let MOI_PDG_VS_EXISTS = prove
 (`!L sigma (h:real^N->real^3) h' w delta U phi k b Q f.
      simplicial_complex L /\
      smooth_manifold_atlas (subtopology euclidean (UNIONS L)) sigma /\
      homeomorphism (UNIONS L,sphere(vec 0,&1)) (h,h') /\
      (!s. s IN L /\ aff_dim s = &2 ==> moi_smo_cell_smooth s h) /\
      {w} IN L /\ &0 < delta /\
      (!s. s IN L /\ ~(s = {}) ==> ?t. t IN L /\ aff_dim t = &2 /\ s SUBSET t) /\
      (U,phi) IN sigma /\ w IN U /\ phi w = vec 0 /\ &0 < k /\
      (!s. s IN L /\ aff_dim s = &2 /\ w IN s
           ==> moi_smo_cell_smooth s ((Q:(real^N->bool)->real^N->real^2) s) /\
               (!x y. x IN s /\ y IN s /\ Q s x = Q s y ==> x = y) /\
               Q s w = vec 0 /\
               (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx(b s))) * Q s x)) /\
               (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
                    ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Q s x = t % a) /\
               (!x. x IN s INTER U ==> phi x = moi_smo_ang k (b s) (Q s x))) /\
      orthogonal_transformation f /\ f(h w) = --basis 3
      ==> ?v1 v2 th1 th2 e R H rho0.
            moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_PDG_DELTA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dl:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `U SUBSET UNIONS L:real^N->bool` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?dU. &0 < dU /\ !x:real^N. x IN UNIONS L /\ dist(w,x) < dU ==> x IN U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean (UNIONS L:real^N->bool)) U` THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `dU:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `dU:real` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `ball(w:real^N,dU)`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `d = min dl dU` THEN
  SUBGOAL_THEN `&0 < d /\ d <= dl /\ d <= dU` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN UNIONS L ==> (h:real^N->real^3) x IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (UNIONS L,sphere(vec 0,&1)) (h:real^N->real^3,h')` THEN
    REWRITE_TAC[homeomorphism] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. ?v1 v2 th1 th2 e R H.
        s IN L /\ aff_dim s = &2 /\ w IN s
        ==> moi_pdg_vtri L U phi k f h w s (b s) ((Q:(real^N->bool)->real^N->real^2) s)
                         v1 v2 th1 th2 e R H /\
            (!y. y IN ball(vec 0,e) ==> dist(w,R y) < d)`
  MP_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    MATCH_MP_TAC MOI_PDG_VTRI_EXISTS THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`; `dl:real`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      can (find_term ((=) `moi_smo_ang`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `dU:real`)) (concl th) && is_forall(concl th))) THEN
      CONJ_TAC THENL [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:(real^N->bool)->real^N` (X_CHOOSE_THEN
    `v2:(real^N->bool)->real^N` (X_CHOOSE_THEN `th1:(real^N->bool)->real` (X_CHOOSE_THEN
    `th2:(real^N->bool)->real` (X_CHOOSE_THEN `e:(real^N->bool)->real` (X_CHOOSE_THEN
    `R:(real^N->bool)->complex->real^N` (X_CHOOSE_THEN `H:(real^N->bool)->complex->complex`
    (LABEL_TAC "tri")))))))) THEN
  SUBGOAL_THEN `FINITE {s:real^N->bool | s IN L /\ aff_dim s = &2 /\ w IN s}` ASSUME_TAC
  THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`e:(real^N->bool)->real`;
                 `{s:real^N->bool | s IN L /\ aff_dim s = &2 /\ w IN s}`]
    MOI_PDG_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "tri" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `x IN L /\ aff_dim x = &2 /\ (w:real^N) IN x`))) THEN
    REWRITE_TAC[moi_pdg_vtri] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r1. &0 < r1 /\ ball(vec 0,r1) SUBSET IMAGE (phi:real^N->real^2) U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(IMAGE (phi:real^N->real^2) U)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] MOI_PDG_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?r2. &0 < r2 /\
                 !z. z IN IMAGE (phi:real^N->real^2) U /\ norm z < r2
                     ==> dist(chart_inv(U,phi) z,w) < min delta d`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `chart_inv(U,phi) continuous_on IMAGE (phi:real^N->real^2) U` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `min delta d`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN EXISTS_TAC `r2:real` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `chart_inv(U,phi) (vec 0:real^2) = (w:real^N)` (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[DIST_0];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v1:(real^N->bool)->real^N`; `v2:(real^N->bool)->real^N`;
    `th1:(real^N->bool)->real`; `th2:(real^N->bool)->real`; `e:(real^N->bool)->real`;
    `R:(real^N->bool)->complex->real^N`; `H:(real^N->bool)->complex->complex`;
    `min (m / &2) (min (r1 / &2) (r2 / &2))`] THEN
  REWRITE_TAC[moi_pdg_vs] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `rho0 = min (m / &2) (min (r1 / &2) (r2 / &2))` THEN
  SUBGOAL_THEN `&0 < rho0 /\ rho0 < m /\ rho0 < r1 /\ rho0 < r2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0,rho0) SUBSET IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_CBALL_0] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `ball(vec 0:real^2,r1)`)) (concl th))) THEN
    REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `homeomorphism (UNIONS L,sphere(vec 0,&1)) (h:real^N->real^3,h')` THEN
    REWRITE_TAC[homeomorphism] THEN MESON_TAC[];
    UNDISCH_TAC `homeomorphism (UNIONS L,sphere(vec 0,&1)) (h:real^N->real^3,h')` THEN
    REWRITE_TAC[homeomorphism] THEN MESON_TAC[];
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `z IN IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dist(chart_inv(U:real^N->bool,phi:real^N->real^2) z,w) < min delta d`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `z IN cball(vec 0:real^2,rho0)` THEN REWRITE_TAC[IN_CBALL_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_PDG_STAR THEN EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET];
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `E:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `E:real^N->bool` o check (fun th ->
      can (find_term ((=) `aff_dim(t:real^N->bool) = &2`)) (concl th) && is_forall(concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN
    SUBGOAL_THEN `(w:real^N) IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "tri" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(t:real^N->bool) IN L`) (CONJ (ASSUME `aff_dim(t:real^N->bool) = &2`)
            (ASSUME `(w:real^N) IN t`))))) THEN
    REWRITE_TAC[moi_pdg_vtri] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_PDG_TRI_EDGE_AT THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "tri" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s`))) THEN
    SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;


(* Consequences of the vertex setting moi_pdg_vs. *)

let MOI_PDG_RAY_DERIV = prove
 (`!(k:complex->real^M) a v. k differentiable at a
      ==> ((\x. k(a + Cx(drop x) * v)) has_derivative
           (frechet_derivative k (at a) o (\x:real^1. Cx(drop x) * v))) (at (vec 0))`,
   REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `linear (\x:real^1. Cx(drop x) * (v:complex))` ASSUME_TAC THENL
     [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x. (k:complex->real^M)(a + Cx(drop x) * v)) =
                  k o (\x:real^1. a + Cx(drop x) * v)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x:real^1. a:complex`; `\h:real^1. vec 0:complex`;
                     `\x:real^1. Cx(drop x) * (v:complex)`;
                     `\x:real^1. Cx(drop x) * (v:complex)`; `at (vec 0:real^1)`]
        HAS_DERIVATIVE_ADD) THEN
      ASM_SIMP_TAC[HAS_DERIVATIVE_CONST; HAS_DERIVATIVE_LINEAR; VECTOR_ADD_LID] THEN
      REWRITE_TAC[ETA_AX];
      REWRITE_TAC[DROP_VEC; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS]]);;

let MOI_PDG_DERIV_DIR2 = prove
 (`!(f:complex->real^M) g a a' u u' e.
      f differentiable at a /\ g differentiable at a' /\ &0 < e /\
      (!t. &0 <= t /\ t < e ==> f(a + Cx t * u) = g(a' + Cx t * u'))
      ==> frechet_derivative f (at a) u = frechet_derivative g (at a') u'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(frechet_derivative (f:complex->real^M) (at a) o
                 (\x:real^1. Cx(drop x) * u)) =
                (frechet_derivative g (at a') o (\x:real^1. Cx(drop x) * u'))` MP_TAC THENL
   [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN_CLOSED_INTERVAL THEN
    MAP_EVERY EXISTS_TAC [`\x. (f:complex->real^M)(a + Cx(drop x) * u)`; `vec 0:real^1`;
                          `vec 0:real^1`; `lift(e / &2)`] THEN
    SUBGOAL_THEN `(vec 0:real^1) IN interval[vec 0,lift(e / &2)]` ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 <= i /\ i <= 1 <=> i = 1`] THEN
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[VEC_COMPONENT; LIFT_COMPONENT] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[MOI_PDG_RAY_DERIV];
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_WITHIN THEN
      MAP_EVERY EXISTS_TAC [`\x. (g:complex->real^M)(a' + Cx(drop x) * u')`; `&1`] THEN
      ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
       [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
        STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `(f:complex->real^M)(a + Cx t * u)`)) (concl th))) THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN ASM_SIMP_TAC[MOI_PDG_RAY_DERIV]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `lift(&1)`) THEN
  REWRITE_TAC[o_THM; LIFT_DROP; COMPLEX_MUL_LID]);;

let MOI_PDG_VS_TRI = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 s.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      s IN L /\ aff_dim s = &2 /\ w IN s
      ==> &0 <= th1 s /\ th1 s < th2 s /\ th2 s <= pi /\ th2 s - th1 s < pi /\
          k * (th2 s - th1 s) < &2 * pi /\ rho0 < e s /\ &0 < e s /\
          smooth_map_on (ball(vec 0,e s)) (H s) /\ H s (vec 0) = vec 0 /\
          (!x. x IN s INTER U ==> phi x = moi_smo_ang k (b s) (Q s x)) /\
          (!y. y IN ball(vec 0,e s) INTER
                   moi_pdg_cone2 (cexp(ii * Cx(b s + th1 s))) (cexp(ii * Cx(b s + th2 s)))
               ==> R s y IN s /\ R s y IN U /\ Q s (R s y) = y /\
                   H s y = moi_pdg_st f (h(R s y)) /\ ~((f(h(R s y)))$3 = &1) /\
                   (!z. frechet_derivative (H s) (at y) z = vec 0 ==> z = vec 0)) /\
          (!x. x IN s /\ norm(Q s x) < e s
               ==> Q s x IN moi_pdg_cone2 (cexp(ii * Cx(b s + th1 s)))
                                          (cexp(ii * Cx(b s + th2 s))) /\
                   R s (Q s x) = x) /\
          (!t. &0 <= t /\ t < e s
               ==> R s (Cx t * cexp(ii * Cx(b s + th1 s))) IN segment[w,v1 s] /\
                   R s (Cx t * cexp(ii * Cx(b s + th2 s))) IN segment[w,v2 s]) /\
          (!x. x IN segment[w,v1 s]
               ==> ?t. &0 <= t /\ Q s x = Cx t * cexp(ii * Cx(b s + th1 s))) /\
          (!x. x IN segment[w,v2 s]
               ==> ?t. &0 <= t /\ Q s x = Cx t * cexp(ii * Cx(b s + th2 s))) /\
          (!r t. &0 < r /\ r < e s /\ th1 s < t /\ t < th2 s
                 ==> R s (Cx r * cexp(ii * Cx(b s + t))) IN relative_interior s) /\
          segment[w,v1 s] IN L /\ segment[w,v2 s] IN L /\
          segment[w,v1 s] SUBSET s /\ segment[w,v2 s] SUBSET s /\
          ~(v1 s = w) /\ ~(v2 s = w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_vs] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_pdg_vtri"))
      (concl th))) THEN
  ASM_REWRITE_TAC[moi_pdg_vtri] THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[w,(v1:(real^N->bool)->real^N) s] SUBSET s /\
                segment[w,(v2:(real^N->bool)->real^N) s] SUBSET s` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `s:real^N->bool`
                           then GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [th]
                           else NO_TAC) THEN
    REWRITE_TAC[MOI_PDG_TRI_SEGS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `s:real^N->bool`)) THEN
  ASM_REWRITE_TAC[]);;

let moi_pdg_gmap = new_definition
 `moi_pdg_gmap (k:real) (b:(real^N->bool)->real) (th1:(real^N->bool)->real)
               (th2:(real^N->bool)->real) (s:real^N->bool) =
    moi_pdg_angz (inv k) (k * (b s + (th1 s + th2 s) / &2))`;;

let moi_pdg_dcone = new_definition
 `moi_pdg_dcone (b:(real^N->bool)->real) (th1:(real^N->bool)->real)
                (th2:(real^N->bool)->real) (s:real^N->bool) =
    moi_pdg_cone2 (cexp(ii * Cx(b s + th1 s))) (cexp(ii * Cx(b s + th2 s)))`;;

let moi_pdg_ssec = new_definition
 `moi_pdg_ssec (k:real) (b:(real^N->bool)->real) (th1:(real^N->bool)->real)
               (th2:(real^N->bool)->real) (s:real^N->bool) =
    moi_pdg_sec k (b s) (th1 s) (th2 s)`;;

let MOI_PDG_DCONE_POLAR = prove
 (`!b th1 th2 (s:real^N->bool) y.
      th1 s < th2 s /\ th2 s - th1 s < pi
      ==> (y IN moi_pdg_dcone b th1 th2 s <=>
           ?r t. &0 <= r /\ th1 s <= t /\ t <= th2 s /\ y = Cx r * cexp(ii * Cx(b s + t)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_dcone] THEN
  MP_TAC(ISPECL [`b(s:real^N->bool) + th1 s`; `th2(s:real^N->bool) - th1 s`; `y:complex`]
    MOI_PDG_CONE2_POLAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(a + t1) + (t2 - t1) = a + t2:real`] THEN
  DISCH_THEN SUBST1_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `th1(s:real^N->bool) + t`] THEN
    ASM_REWRITE_TAC[REAL_ADD_ASSOC] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `t - th1(s:real^N->bool)`] THEN
    ASM_REWRITE_TAC[REAL_ARITH `(a + t1) + (t - t1) = a + t:real`] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_VS_BASIC = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> simplicial_complex L /\
          smooth_manifold_atlas (subtopology euclidean (UNIONS L)) sigma /\
          (U,phi) IN sigma /\ w IN U /\ phi w = vec 0 /\ &0 < k /\ {w} IN L /\
          orthogonal_transformation f /\ f(h w) = --basis 3 /\
          h continuous_on UNIONS L /\ (!x. x IN UNIONS L ==> h x IN sphere(vec 0,&1)) /\
          (!x y. x IN UNIONS L /\ y IN UNIONS L /\ h x = h y ==> x = y) /\
          FINITE {s | s IN L /\ aff_dim s = &2 /\ w IN s} /\
          &0 < rho0 /\ cball(vec 0,rho0) SUBSET IMAGE phi U /\
          (!z. z IN cball(vec 0,rho0)
               ==> chart_inv(U,phi) z IN ball(w,delta) /\
                   ?s. s IN L /\ aff_dim s = &2 /\ w IN s /\ chart_inv(U,phi) z IN s) /\
          (!x. x IN U ==> chart_inv (U,phi) (phi x) = x) /\
          (!y. y IN IMAGE phi U
               ==> chart_inv (U,phi) y IN U /\ phi(chart_inv (U,phi) y) = y) /\
          U SUBSET UNIONS L`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_vs] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] CHART_INV) THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS L:real^N->bool)`;
                 `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[OPEN_IN_IMP_SUBSET]);;

let MOI_PDG_VS_SEC_CHART = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 s z.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\
      z IN moi_pdg_ssec k b th1 th2 s /\ norm z < e s
      ==> moi_pdg_gmap k b th1 th2 s z IN ball(vec 0,e s) INTER moi_pdg_dcone b th1 th2 s /\
          norm(moi_pdg_gmap k b th1 th2 s z) = norm z /\
          z IN IMAGE phi U /\
          chart_inv(U,phi) z = R s (moi_pdg_gmap k b th1 th2 s z) /\
          chart_inv(U,phi) z IN s /\
          moi_pdg_st f (h(chart_inv(U,phi) z)) = H s (moi_pdg_gmap k b th1 th2 s z) /\
          ~((f(h(chart_inv(U,phi) z)))$3 = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `z IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` THEN
  REWRITE_TAC[moi_pdg_ssec; moi_pdg_sec; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_pdg_gmap k b th1 th2 (s:real^N->bool) z =
                Cx r * cexp(ii * Cx(b s + t))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_pdg_gmap] THEN MATCH_MP_TAC MOI_PDG_ANGZ_POLAR THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:complex) = r` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `z:complex`
                          then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
    UNDISCH_TAC `&0 <= r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `y = moi_pdg_gmap k b th1 th2 (s:real^N->bool) z` THEN
  SUBGOAL_THEN `norm(y:complex) = r` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `y:complex`
                          then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
    UNDISCH_TAC `&0 <= r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:complex) IN ball(vec 0,e(s:real^N->bool)) INTER
                moi_pdg_dcone b th1 th2 s` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_BALL_0] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`norm(y:complex) = r`; `norm(z:complex) = r`;
                             `norm(z:complex) < e(s:real^N->bool)`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`b:(real^N->bool)->real`; `th1:(real^N->bool)->real`;
                   `th2:(real^N->bool)->real`; `s:real^N->bool`; `y:complex`]
      MOI_PDG_DCONE_POLAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `t:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:(real^N->bool)->complex->real^N) s y IN s /\ R s y IN U /\
                (Q:(real^N->bool)->real^N->real^2) s (R s y) = y /\
                (H:(real^N->bool)->complex->complex) s y = moi_pdg_st f (h(R s y)) /\
                ~(((f:real^3->real^3)(h(R s y)))$3 = &1)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:complex) IN ball(vec 0,e(s:real^N->bool)) INTER
                 moi_pdg_dcone b th1 th2 s` THEN
    REWRITE_TAC[moi_pdg_dcone] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^N->real^2) ((R:(real^N->bool)->complex->real^N) s y) = z`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(phi:real^N->real^2) ((R:(real^N->bool)->complex->real^N) s y) =
                  moi_smo_ang k (b s) ((Q:(real^N->bool)->real^N->real^2) s (R s y))`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `moi_smo_ang`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `moi_pdg_gmap k b th1 th2 (s:real^N->bool) z = y`)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PDG_ANG_POLAR0 THEN
    MAP_EVERY UNDISCH_TAC [`&0 <= r`; `&0 <= th1(s:real^N->bool)`; `th1(s:real^N->bool) <= t`;
                           `t <= th2(s:real^N->bool)`; `th2(s:real^N->bool) <= pi`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv(U:real^N->bool,phi:real^N->real^2) z = (R:(real^N->bool)->complex->real^N) s y`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(phi:real^N->real^2) ((R:(real^N->bool)->complex->real^N) s y) = z`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]);;

let MOI_PDG_VS_COVER = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 z.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      norm z <= rho0
      ==> ?s. s IN L /\ aff_dim s = &2 /\ w IN s /\ z IN moi_pdg_ssec k b th1 th2 s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:complex) IN cball(vec 0,rho0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_CBALL_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:complex) IN IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o check (fun th ->
    can (find_term ((=) `ball(w:real^N,delta)`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `s:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `x = chart_inv(U:real^N->bool,phi:real^N->real^2) z` THEN
  SUBGOAL_THEN `(x:real^N) IN U /\ (phi:real^N->real^2) x = z` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(phi:real^N->real^2) x = moi_smo_ang k (b s) ((Q:(real^N->bool)->real^N->real^2) s x)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `moi_smo_ang`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((Q:(real^N->bool)->real^N->real^2) s x) < e(s:real^N->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `norm((Q:(real^N->bool)->real^N->real^2) s x) = norm(z:complex)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`k:real`; `b(s:real^N->bool):real`;
                     `(Q:(real^N->bool)->real^N->real^2) s x`] MOI_PDG_ANG_NORM) THEN
      SUBGOAL_THEN `moi_smo_ang k (b s) ((Q:(real^N->bool)->real^N->real^2) s x) = z`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]];
      MAP_EVERY UNDISCH_TAC [`norm(z:complex) <= rho0`; `rho0 < e(s:real^N->bool)`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:(real^N->bool)->real^N->real^2) s x IN moi_pdg_dcone b th1 th2 s`
  MP_TAC THENL
   [REWRITE_TAC[moi_pdg_dcone] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      can (find_term ((=) `(R:(real^N->bool)->complex->real^N) s
        ((Q:(real^N->bool)->real^N->real^2) s x) = x`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`b:(real^N->bool)->real`; `th1:(real^N->bool)->real`;
                 `th2:(real^N->bool)->real`; `s:real^N->bool`;
                 `(Q:(real^N->bool)->real^N->real^2) s x`] MOI_PDG_DCONE_POLAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[moi_pdg_ssec; moi_pdg_sec; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `z = moi_smo_ang k (b s) ((Q:(real^N->bool)->real^N->real^2) s x)`
  SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PDG_ANG_POLAR0 THEN
  MAP_EVERY UNDISCH_TAC [`&0 <= r`; `&0 <= th1(s:real^N->bool)`; `th1(s:real^N->bool) <= t`;
                         `t <= th2(s:real^N->bool)`; `th2(s:real^N->bool) <= pi`] THEN
  REAL_ARITH_TAC);;

let MOI_PDG_VS_COVER_ALL = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 z.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> ?s. s IN L /\ aff_dim s = &2 /\ w IN s /\ z IN moi_pdg_ssec k b th1 th2 s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho0` ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `norm(z:complex) <= rho0` THENL
   [MATCH_MP_TAC MOI_PDG_VS_COVER THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
    `h:real^N->real^3`; `w:real^N`; `delta:real`; `U:real^N->bool`; `phi:real^N->real^2`;
    `k:real`; `b:(real^N->bool)->real`; `Q:(real^N->bool)->real^N->real^2`;
    `f:real^3->real^3`; `v1:(real^N->bool)->real^N`; `v2:(real^N->bool)->real^N`;
    `th1:(real^N->bool)->real`; `th2:(real^N->bool)->real`; `e:(real^N->bool)->real`;
    `R:(real^N->bool)->complex->real^N`; `H:(real^N->bool)->complex->complex`; `rho0:real`;
    `Cx(rho0 / norm(z:complex)) * z`] MOI_PDG_VS_COVER) THEN
  SUBGOAL_THEN `&0 < norm(z:complex)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `z = Cx(norm(z:complex) / rho0) * (Cx(rho0 / norm z) * z)` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    SUBGOAL_THEN `norm(z:complex) / rho0 * rho0 / norm z = &1` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < rho0` THEN UNDISCH_TAC `&0 < norm(z:complex)` THEN
      CONV_TAC REAL_FIELD;
      REWRITE_TAC[COMPLEX_MUL_LID]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_pdg_ssec] THEN MATCH_MP_TAC MOI_PDG_SEC_CONIC THEN
  ASM_REWRITE_TAC[GSYM moi_pdg_ssec] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_GMAP_HOMOG = prove
 (`!k b th1 th2 (s:real^N->bool) t z. &0 <= t
     ==> moi_pdg_gmap k b th1 th2 s (Cx t * z) = Cx t * moi_pdg_gmap k b th1 th2 s z`,
  SIMP_TAC[moi_pdg_gmap; MOI_PDG_ANGZ_HOMOG]);;

let MOI_PDG_GMAP_NORM = prove
 (`!k b th1 th2 (s:real^N->bool) z. norm(moi_pdg_gmap k b th1 th2 s z) = norm z`,
  REWRITE_TAC[moi_pdg_gmap; MOI_PDG_ANGZ_NORM]);;

let MOI_PDG_SSEC_CONIC = prove
 (`!k b th1 th2 (s:real^N->bool) z t.
      z IN moi_pdg_ssec k b th1 th2 s /\ &0 <= t
      ==> Cx t * z IN moi_pdg_ssec k b th1 th2 s`,
  REWRITE_TAC[moi_pdg_ssec; MOI_PDG_SEC_CONIC]);;

let MOI_PDG_VS_H0 = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 s.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      s IN L /\ aff_dim s = &2 /\ w IN s
      ==> H s differentiable at (vec 0) /\ H s (vec 0) = vec 0 /\
          (!z. frechet_derivative (H s) (at (vec 0)) z = vec 0 ==> z = vec 0) /\
          &0 < e s /\ rho0 < e s /\ &0 < rho0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:complex) IN ball(vec 0,e(s:real^N->bool)) INTER
     moi_pdg_cone2 (cexp(ii * Cx(b s + th1 s))) (cexp(ii * Cx(b s + th2 s)))`
  (fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (fun th' ->
     can (find_term ((=) `moi_pdg_st`)) (concl th') && is_forall(concl th'))))
  THENL
   [REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; moi_pdg_cone2; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`&0`; `&0`] THEN
    REWRITE_TAC[REAL_LE_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID];
    SIMP_TAC[]]);;

let MOI_PDG_VS_LIN_CONSIST = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 s s' z.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\ s' IN L /\ aff_dim s' = &2 /\ w IN s' /\
      z IN moi_pdg_ssec k b th1 th2 s /\ z IN moi_pdg_ssec k b th1 th2 s'
      ==> frechet_derivative (H s) (at (vec 0)) (moi_pdg_gmap k b th1 th2 s z) =
          frechet_derivative (H s') (at (vec 0)) (moi_pdg_gmap k b th1 th2 s' z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`s':real^N->bool`,`s:real^N->bool`] (SPEC_ALL MOI_PDG_VS_H0)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_PDG_DERIV_DIR2 THEN
  EXISTS_TAC `min (e(s:real^N->bool)) (e s') / (norm(z:complex) + &1)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm(z:complex) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `z:complex` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ADD_LID] THEN
  SIMP_TAC[GSYM MOI_PDG_GMAP_HOMOG; ASSUME `&0 <= t`] THEN
  SUBGOAL_THEN `norm(Cx t * z) < e(s:real^N->bool) /\ norm(Cx t * z) < e(s':real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    UNDISCH_TAC `t < min (e(s:real^N->bool)) (e s') / (norm(z:complex) + &1)` THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; ASSUME `&0 < norm(z:complex) + &1`] THEN
    MP_TAC(ISPEC `z:complex` NORM_POS_LE) THEN UNDISCH_TAC `&0 <= t` THEN
    REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_ARITH;
    ALL_TAC] THEN
  MP_TAC(INST [`Cx t * z`,`z:complex`] (SPEC_ALL MOI_PDG_VS_SEC_CHART)) THEN
  MP_TAC(INST [`s':real^N->bool`,`s:real^N->bool`; `Cx t * z`,`z:complex`]
    (SPEC_ALL MOI_PDG_VS_SEC_CHART)) THEN
  SUBGOAL_THEN `Cx t * z IN moi_pdg_ssec k b th1 th2 (s:real^N->bool) /\
                Cx t * z IN moi_pdg_ssec k b th1 th2 (s':real^N->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_SSEC_CONIC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let moi_pdg_psel = new_definition
 `moi_pdg_psel (L:(real^N->bool)->bool) (w:real^N) (k:real) (b:(real^N->bool)->real)
               (th1:(real^N->bool)->real) (th2:(real^N->bool)->real) (z:complex) =
    @s. s IN L /\ aff_dim s = &2 /\ w IN s /\ z IN moi_pdg_ssec k b th1 th2 s`;;

let moi_pdg_pmap = new_definition
 `moi_pdg_pmap (L:(real^N->bool)->bool) (w:real^N) (k:real) (b:(real^N->bool)->real)
               (th1:(real^N->bool)->real) (th2:(real^N->bool)->real)
               (H:(real^N->bool)->complex->complex) (z:complex) =
    frechet_derivative (H (moi_pdg_psel L w k b th1 th2 z)) (at (vec 0))
      (moi_pdg_gmap k b th1 th2 (moi_pdg_psel L w k b th1 th2 z) z)`;;

let MOI_PDG_VS_PMAP_EQ = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 s z.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\ z IN moi_pdg_ssec k b th1 th2 s
      ==> moi_pdg_pmap L w k b th1 th2 H z =
          frechet_derivative (H s) (at (vec 0)) (moi_pdg_gmap k b th1 th2 s z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_pmap] THEN
  ABBREV_TAC `s0 = moi_pdg_psel (L:(real^N->bool)->bool) w k b th1 th2 z` THEN
  SUBGOAL_THEN `s0 IN L /\ aff_dim s0 = &2 /\ (w:real^N) IN s0 /\
                z IN moi_pdg_ssec k b th1 th2 s0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN REWRITE_TAC[moi_pdg_psel] THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST [`s0:real^N->bool`,`s:real^N->bool`; `s:real^N->bool`,`s':real^N->bool`]
    (SPEC_ALL MOI_PDG_VS_LIN_CONSIST)) THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_VS_PMAP_HOMOG = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 t z.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\ &0 <= t
      ==> moi_pdg_pmap L w k b th1 th2 H (Cx t * z) =
          Cx t * moi_pdg_pmap L w k b th1 th2 H z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_COVER_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_EQ) THEN
  MP_TAC(INST [`Cx t * z`,`z:complex`] (SPEC_ALL MOI_PDG_VS_PMAP_EQ)) THEN
  ASM_SIMP_TAC[MOI_PDG_SSEC_CONIC] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[MOI_PDG_GMAP_HOMOG] THEN
  REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
  MATCH_MP_TAC LINEAR_CMUL THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]);;

let MOI_PDG_VS_PMAP_NZ = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 z.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      ~(z = Cx(&0))
      ==> ~(moi_pdg_pmap L w k b th1 th2 H z = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_COVER_ALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_EQ) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_pdg_gmap k b th1 th2 (s:real^N->bool) z = vec 0` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[COMPLEX_VEC_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[MOI_PDG_GMAP_NORM; NORM_0] THEN
  REWRITE_TAC[NORM_EQ_0; COMPLEX_VEC_0] THEN
  UNDISCH_TAC `~(z = Cx(&0))` THEN CONV_TAC TAUT);;

let MOI_PDG_SLIT_OPEN_C = prove
 (`!c. open {y:complex | Im(cexp(--(ii * Cx c)) * y) = &0
                         ==> &0 < Re(cexp(--(ii * Cx c)) * y)}`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\y:complex. cexp(--(ii * Cx c)) * y`;
                 `{u:complex | Im u = &0 ==> &0 < Re u}`] CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  REWRITE_TAC[MOI_PDG_SLIT_OPEN; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_COMPLEX_LMUL THEN REWRITE_TAC[CONTINUOUS_AT_ID]);;

let MOI_PDG_ANGZ_CONT_AT = prove
 (`!k c z. z = Cx(&0) \/
           (Im(cexp(--(ii * Cx c)) * z) = &0 ==> &0 < Re(cexp(--(ii * Cx c)) * z))
           ==> moi_pdg_angz k c continuous at z`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
   [ASM_REWRITE_TAC[continuous_at] THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:complex` THEN
    REWRITE_TAC[dist; moi_pdg_angz; COMPLEX_SUB_RZERO; GSYM COMPLEX_VEC_0;
                VECTOR_SUB_RZERO] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[NORM_0] THEN
    MP_TAC(ISPECL [`k:real`; `c:real`; `x:complex`] MOI_PDG_ANGF_NORM) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `O = {y:complex | Im(cexp(--(ii * Cx c)) * y) = &0
                               ==> &0 < Re(cexp(--(ii * Cx c)) * y)}` THEN
  SUBGOAL_THEN `open(O:complex->bool) /\ z IN O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[MOI_PDG_SLIT_OPEN_C; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `z:complex` (REWRITE_RULE[OPEN_CONTAINS_BALL]
    (ASSUME `open(O:complex->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`moi_pdg_angf k c`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN REWRITE_TAC[moi_pdg_angz] THEN
    ASM_CASES_TAC `y = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:complex) IN O` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `ball(z:complex,r)`)) (concl th))) THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "O" THEN ASM_REWRITE_TAC[IN_ELIM_THM; COMPLEX_MUL_RZERO; RE_CX; IM_CX;
        REAL_LT_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on O (moi_pdg_angf k c)` MP_TAC THENL
   [MATCH_MP_TAC MOI_PDG_ANGF_SMOOTH THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "O" THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SMOOTH_MAP_ON_CONTINUOUS_ON) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]);;

let MOI_PDG_SEC_SLIT = prove
 (`!k a t1 t2 z. &0 < k /\ t1 <= t2 /\ k * (t2 - t1) < &2 * pi /\
                 z IN moi_pdg_sec k a t1 t2
                 ==> z = Cx(&0) \/
                     (Im(cexp(--(ii * Cx(k * (a + (t1 + t2) / &2)))) * z) = &0
                      ==> &0 < Re(cexp(--(ii * Cx(k * (a + (t1 + t2) / &2)))) * z))`,
  REWRITE_TAC[moi_pdg_sec; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `r = &0` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO]; DISJ2_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = (t1 + t2) / &2` THEN
  SUBGOAL_THEN `cexp(--(ii * Cx(k * (a + m)))) * Cx r * cexp(ii * Cx(k * (a + t))) =
                Cx r * cexp(ii * Cx(k * (t - m)))` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_RING `a * Cx r * b = Cx r * (a * b)`; GSYM CEXP_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CX_MUL; CX_ADD; CX_SUB] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX;
              REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `k * (t - m) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC SIN_EQ_0_PI THEN CONJ_TAC THENL
     [ALL_TAC;
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ]]] THEN
    (SUBGOAL_THEN `abs(k * (t - m)) <= k * ((t2 - t1) / &2)` MP_TAC THENL
     [REWRITE_TAC[REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN EXPAND_TAC "m" THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `k * (t2 - t1) < &2 * pi` THEN REAL_ARITH_TAC]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COS_0; REAL_MUL_RID]);;

let MOI_PDG_GMAP_CONT = prove
 (`!k b th1 th2 (s:real^N->bool).
      &0 < k /\ th1 s <= th2 s /\ k * (th2 s - th1 s) < &2 * pi
      ==> moi_pdg_gmap k b th1 th2 s continuous_on moi_pdg_ssec k b th1 th2 s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[moi_pdg_gmap; moi_pdg_ssec] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_PDG_ANGZ_CONT_AT THEN
  MATCH_MP_TAC MOI_PDG_SEC_SLIT THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_SEC_CLOSED = prove
 (`!k a t1 t2. &0 < k /\ t1 < t2 /\ k * (t2 - t1) < &2 * pi
               ==> closed(moi_pdg_sec k a t1 t2)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_PDG_SEC_HALVES] THEN
  MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN
  (MATCH_MP_TAC MOI_PDG_CONE2_CLOSED THEN
   REWRITE_TAC[MOI_PDG_IM_CNJ_UNIT] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN MATCH_MP_TAC SIN_POS_PI THEN
   REWRITE_TAC[REAL_ARITH `k * (a + (t1 + t2) / &2) - k * (a + t1) = k * ((t2 - t1) / &2)`;
               REAL_ARITH `k * (a + t2) - k * (a + (t1 + t2) / &2) = k * ((t2 - t1) / &2)`] THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
     UNDISCH_TAC `k * (t2 - t1) < &2 * pi` THEN REAL_ARITH_TAC]));;

let MOI_PDG_VS_PMAP_CONT = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> moi_pdg_pmap L w k b th1 th2 H continuous_on (:complex)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `continuous_map(euclidean,euclidean)
                  (moi_pdg_pmap L w k b th1 th2 (H:(real^N->bool)->complex->complex))`
  MP_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:real^N->bool`,`:K`] PASTING_LEMMA_CLOSED) THEN
    MAP_EVERY EXISTS_TAC
     [`\s:real^N->bool. moi_pdg_pmap L w k b th1 th2 (H:(real^N->bool)->complex->complex)`;
      `\s:real^N->bool. moi_pdg_ssec k b th1 th2 s`;
      `{s:real^N->bool | s IN L /\ aff_dim s = &2 /\ w IN s}`] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN; TOPSPACE_EUCLIDEAN; IN_UNIV; IN_ELIM_THM;
                    CLOSED_IN_EUCLIDEAN] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [REWRITE_TAC[moi_pdg_ssec] THEN MATCH_MP_TAC MOI_PDG_SEC_CLOSED THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `frechet_derivative ((H:(real^N->bool)->complex->complex) s) (at (vec 0)) o
                  moi_pdg_gmap k b th1 th2 s` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_EQ) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_PDG_GMAP_CONT THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
          MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]]];
      X_GEN_TAC `z:complex` THEN
      MP_TAC(SPEC_ALL MOI_PDG_VS_COVER_ALL) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM CONTINUOUS_MAP_EUCLIDEAN] THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV]]);;


(* The chart map F = st f h chart_inv near the vertex, its linearization P,       *)
(* and the degree of P (leaf D4b).                                                *)

let moi_pdg_fmap = new_definition
 `moi_pdg_fmap (U:real^N->bool) (phi:real^N->real^2) (f:real^3->real^3)
               (h:real^N->real^3) (z:complex) =
    moi_pdg_st f (h(chart_inv(U,phi) z))`;;

let MOI_PDG_VS_F_LOCAL = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 z.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      norm z <= rho0
      ==> z IN IMAGE phi U /\ chart_inv(U,phi) z IN U /\
          chart_inv(U,phi) z IN UNIONS L /\
          h(chart_inv(U,phi) z) IN sphere(vec 0,&1) /\
          ~((f(h(chart_inv(U,phi) z)))$3 = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `z IN IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `cball(vec 0:real^2,rho0)`)) (concl th) &&
      not(is_forall(concl th)))) THEN
    ASM_REWRITE_TAC[IN_CBALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv(U:real^N->bool,phi:real^N->real^2) z IN U` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv(U:real^N->bool,phi:real^N->real^2) z IN UNIONS L` ASSUME_TAC
  THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_COVER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_SEC_CHART) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]);;

let MOI_PDG_VS_F_0 = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> moi_pdg_fmap U phi f h (Cx(&0)) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_pdg_fmap; GSYM COMPLEX_VEC_0] THEN
  SUBGOAL_THEN `chart_inv(U:real^N->bool,phi:real^N->real^2) (vec 0) = w` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_PDG_ST_SOUTH]);;

let MOI_PDG_VS_F_CONT = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> moi_pdg_fmap U phi f h continuous_on cball(vec 0,rho0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `U:real^N->bool`; `phi:real^N->real^2`] MOI_PDG_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_pdg_fmap U phi f (h:real^N->real^3) =
                moi_pdg_st f o h o chart_inv(U,phi)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_pdg_fmap; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (phi:real^N->real^2) U` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS L:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_CBALL_0] THEN DISCH_TAC THEN
      MP_TAC(SPEC_ALL MOI_PDG_VS_F_LOCAL) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `{p:real^3 | ~(((f:real^3->real^3) p)$3 = &1)}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN MATCH_MP_TAC MOI_PDG_ST_SMOOTH THEN
    ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_CBALL_0] THEN DISCH_TAC THEN
    MP_TAC(SPEC_ALL MOI_PDG_VS_F_LOCAL) THEN ASM_SIMP_TAC[]]);;

let MOI_PDG_VS_F_INJ = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 z1 z2.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      norm z1 <= rho0 /\ norm z2 <= rho0 /\
      moi_pdg_fmap U phi f h z1 = moi_pdg_fmap U phi f h z2
      ==> z1 = z2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`z1:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_F_LOCAL)) THEN
  MP_TAC(INST [`z2:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_F_LOCAL)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^3)(chart_inv(U:real^N->bool,phi:real^N->real^2) z1) = h(chart_inv(U,phi) z2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^3->real^3`; `(h:real^N->real^3)(chart_inv(U:real^N->bool,phi:real^N->real^2) z1)`]
      MOI_PDG_STI_ST) THEN
    MP_TAC(ISPECL [`f:real^3->real^3`; `(h:real^N->real^3)(chart_inv(U:real^N->bool,phi:real^N->real^2) z2)`]
      MOI_PDG_STI_ST) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_pdg_fmap U phi f (h:real^N->real^3) z1 = moi_pdg_fmap U phi f h z2` THEN
    REWRITE_TAC[moi_pdg_fmap] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `chart_inv(U:real^N->bool,phi:real^N->real^2) z1 = chart_inv(U,phi) z2`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_PDG_VS_F_FIRST_ORDER = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> !ep. &0 < ep
               ==> ?r. &0 < r /\
                       !x. norm x < r
                           ==> norm(moi_pdg_fmap U phi f h x -
                                    moi_pdg_pmap L w k b th1 th2 H x) <= ep * norm x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. ?d. s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s
            ==> &0 < d /\ d <= e s /\
                !y. norm y < d
                    ==> norm((H:(real^N->bool)->complex->complex) s y -
                             frechet_derivative (H s) (at (vec 0)) y) <= ep * norm y`
  MP_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`(H:(real^N->bool)->complex->complex) s`;
                   `frechet_derivative ((H:(real^N->bool)->complex->complex) s) (at (vec 0))`;
                   `vec 0:complex`] HAS_DERIVATIVE_AT_ALT) THEN
    ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
    DISCH_THEN(MP_TAC o SPEC `ep:real` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d (e(s:real^N->bool))` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    X_GEN_TAC `y:complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:complex`) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_RZERO];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->real` (LABEL_TAC "d")) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->real`;
                 `{s:real^N->bool | s IN L /\ aff_dim s = &2 /\ w IN s}`]
    MOI_PDG_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "d" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min m rho0` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
  MP_TAC(INST [`x:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_COVER)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "d" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(s:real^N->bool) IN L`) (CONJ (ASSUME `aff_dim(s:real^N->bool) = &2`)
          (ASSUME `(w:real^N) IN s`))))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `m <= (d:(real^N->bool)->real) s` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(INST [`x:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_SEC_CHART)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(INST [`x:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_PMAP_EQ)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[moi_pdg_fmap] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `ep:real`)) (concl th) then
      MP_TAC(SPEC `moi_pdg_gmap k b th1 th2 (s:real^N->bool) x` th) else NO_TAC) THEN
  REWRITE_TAC[MOI_PDG_GMAP_NORM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REAL_ARITH_TAC);;

let MOI_PDG_VS_WINDING = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      MOI_SMO_VERTEX_DEGREE_STATEMENT /\
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> winding_number((\t. moi_pdg_pmap L w k b th1 th2 H
                               (cexp(ii * Cx(&2 * pi * drop t)))),Cx(&0)) = Cx(&1) \/
          winding_number((\t. moi_pdg_pmap L w k b th1 th2 H
                               (cexp(ii * Cx(&2 * pi * drop t)))),Cx(&0)) = --Cx(&1)`,
  REWRITE_TAC[MOI_SMO_VERTEX_DEGREE_STATEMENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`moi_pdg_fmap U phi f (h:real^N->real^3)`; `ball(vec 0:complex,rho0)`] THEN
  REWRITE_TAC[OPEN_BALL; IN_BALL_0; COMPLEX_NORM_CX; REAL_ABS_0; ETA_AX] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:complex,rho0)` THEN
    REWRITE_TAC[BALL_SUBSET_CBALL] THEN MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_F_CONT) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_F_INJ) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_F_0) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_CONT) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_HOMOG) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MP_TAC(INST [`x:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_PMAP_NZ)) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_F_FIRST_ORDER) THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_CEXP_II_CLOSE = prove
 (`!a ep. norm(cexp(ii * Cx(a + ep)) - cexp(ii * Cx a)) <= abs ep`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `cexp(ii * Cx(a + ep)) - cexp(ii * Cx a) =
                cexp(ii * Cx a) * (cexp(ii * Cx ep) - Cx(&1))` SUBST1_TAC THENL
   [REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; REAL_MUL_LID; DIST_CEXP_II_1] THEN
  MP_TAC(ISPEC `ep / &2` REAL_ABS_SIN_BOUND_LE) THEN REAL_ARITH_TAC);;

let MOI_PDG_CEXP_II_INJ = prove
 (`!x y. abs(x - y) < &2 * pi /\ cexp(ii * Cx x) = cexp(ii * Cx y) ==> x = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ii * Cx x = ii * Cx y` MP_TAC THENL
   [MATCH_MP_TAC COMPLEX_EQ_CEXP THEN ASM_REWRITE_TAC[IM_MUL_II; RE_CX];
    REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; II_NZ; CX_INJ]]);;

let MOI_PDG_SSEC_UNIT = prove
 (`!k b th1 th2 (s:real^N->bool) a.
      cexp(ii * Cx a) IN moi_pdg_ssec k b th1 th2 s <=>
      ?t. th1 s <= t /\ t <= th2 s /\ cexp(ii * Cx a) = cexp(ii * Cx(k * (b s + t)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_ssec; moi_pdg_sec; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r = &1` (fun th -> ASM_REWRITE_TAC[th; COMPLEX_MUL_LID]) THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:complex->real` o check (fun th ->
      is_eq(concl th) && can (find_term ((=) `Cx r`)) (concl th))) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`&1`; `t:real`] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LID; REAL_POS]]);;

let MOI_PDG_VS_UPPER = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 a.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> ?s t. s IN L /\ aff_dim s = &2 /\ w IN s /\ th1 s <= t /\ t < th2 s /\
                cexp(ii * Cx a) = cexp(ii * Cx(k * (b s + t)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(LABEL_TAC "neg") THEN
  SUBGOAL_THEN
   `!s. ?d. s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s
            ==> &0 < d /\
                !ep. &0 < ep /\ ep < d
                     ==> ~(cexp(ii * Cx(a + ep)) IN moi_pdg_ssec k b th1 th2 s)`
  MP_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `cexp(ii * Cx a) IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` THENL
     [UNDISCH_TAC `cexp(ii * Cx a) IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` THEN
      REWRITE_TAC[MOI_PDG_SSEC_UNIT] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `t:real = th2(s:real^N->bool)` SUBST_ALL_TAC THENL
       [REMOVE_THEN "neg" (MP_TAC o SPECL [`s:real^N->bool`; `t:real`]) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXISTS_TAC `&2 * pi - k * (th2(s:real^N->bool) - th1 s)` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `ep:real` THEN STRIP_TAC THEN REWRITE_TAC[MOI_PDG_SSEC_UNIT] THEN
      DISCH_THEN(X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `k * (b(s:real^N->bool) + th2 s) + ep = k * (b s + t')` MP_TAC THENL
       [MATCH_MP_TAC MOI_PDG_CEXP_II_INJ THEN CONJ_TAC THENL
         [SUBGOAL_THEN `&0 <= k * (th2(s:real^N->bool) - t') /\
                        k * (th2 s - t') <= k * (th2 s - th1 s)` MP_TAC THENL
           [CONJ_TAC THENL
             [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
              MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
            UNDISCH_TAC `ep < &2 * pi - k * (th2(s:real^N->bool) - th1 s)` THEN
            UNDISCH_TAC `&0 < ep` THEN REAL_ARITH_TAC];
          REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
          FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
             lhs(concl th) = `cexp(ii * Cx(a + ep))` then
             REWRITE_TAC[GSYM th] else NO_TAC) THEN
          REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
          FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
             lhs(concl th) = `cexp(ii * Cx a)` then
             REWRITE_TAC[th] else NO_TAC) THEN
          REWRITE_TAC[GSYM CEXP_ADD; GSYM COMPLEX_ADD_LDISTRIB; GSYM CX_ADD]];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= k * (th2(s:real^N->bool) - t')` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&0 < ep` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `open((:complex) DIFF moi_pdg_ssec k b th1 th2 (s:real^N->bool))`
    MP_TAC THENL
     [REWRITE_TAC[GSYM closed; moi_pdg_ssec] THEN MATCH_MP_TAC MOI_PDG_SEC_CLOSED THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `cexp(ii * Cx a)`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `ep:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `cexp(ii * Cx(a + ep)) IN ball(cexp(ii * Cx a),r)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      MP_TAC(ISPECL [`a:real`; `ep:real`] MOI_PDG_CEXP_II_CLOSE) THEN
      ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->real` (LABEL_TAC "d")) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->real`;
                 `{s:real^N->bool | s IN L /\ aff_dim s = &2 /\ w IN s}`]
    MOI_PDG_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "d" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(INST [`cexp(ii * Cx(a + m / &2))`,`z:complex`] (SPEC_ALL MOI_PDG_VS_COVER_ALL)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "d" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(s:real^N->bool) IN L`) (CONJ (ASSUME `aff_dim(s:real^N->bool) = &2`)
          (ASSUME `(w:real^N) IN s`))))) THEN
  DISCH_THEN(MP_TAC o SPEC `m / &2` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `m <= (d:(real^N->bool)->real) s` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < m` THEN REAL_ARITH_TAC);;

let MOI_PDG_VS_LOWER = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 a.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> ?s t. s IN L /\ aff_dim s = &2 /\ w IN s /\ th1 s < t /\ t <= th2 s /\
                cexp(ii * Cx a) = cexp(ii * Cx(k * (b s + t)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(LABEL_TAC "neg") THEN
  SUBGOAL_THEN
   `!s. ?d. s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s
            ==> &0 < d /\
                !ep. &0 < ep /\ ep < d
                     ==> ~(cexp(ii * Cx(a - ep)) IN moi_pdg_ssec k b th1 th2 s)`
  MP_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `cexp(ii * Cx a) IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` THENL
     [UNDISCH_TAC `cexp(ii * Cx a) IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` THEN
      REWRITE_TAC[MOI_PDG_SSEC_UNIT] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `t:real = th1(s:real^N->bool)` SUBST_ALL_TAC THENL
       [REMOVE_THEN "neg" (MP_TAC o SPECL [`s:real^N->bool`; `t:real`]) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXISTS_TAC `&2 * pi - k * (th2(s:real^N->bool) - th1 s)` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `ep:real` THEN STRIP_TAC THEN REWRITE_TAC[MOI_PDG_SSEC_UNIT] THEN
      DISCH_THEN(X_CHOOSE_THEN `t':real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `k * (b(s:real^N->bool) + th1 s) - ep = k * (b s + t')` MP_TAC THENL
       [MATCH_MP_TAC MOI_PDG_CEXP_II_INJ THEN CONJ_TAC THENL
         [SUBGOAL_THEN `&0 <= k * (t' - th1(s:real^N->bool)) /\
                        k * (t' - th1 s) <= k * (th2 s - th1 s)` MP_TAC THENL
           [CONJ_TAC THENL
             [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
              MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
            UNDISCH_TAC `ep < &2 * pi - k * (th2(s:real^N->bool) - th1 s)` THEN
            UNDISCH_TAC `&0 < ep` THEN REAL_ARITH_TAC];
          REWRITE_TAC[real_sub; CX_ADD; CX_NEG; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
          FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
             lhs(concl th) = `cexp(ii * Cx(a - ep))` then
             REWRITE_TAC[GSYM th] else NO_TAC) THEN
          REWRITE_TAC[real_sub; CX_ADD; CX_NEG; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
          FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
             lhs(concl th) = `cexp(ii * Cx a)` then
             REWRITE_TAC[th] else NO_TAC)];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= k * (t' - th1(s:real^N->bool))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&0 < ep` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `open((:complex) DIFF moi_pdg_ssec k b th1 th2 (s:real^N->bool))`
    MP_TAC THENL
     [REWRITE_TAC[GSYM closed; moi_pdg_ssec] THEN MATCH_MP_TAC MOI_PDG_SEC_CLOSED THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `cexp(ii * Cx a)`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `ep:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `cexp(ii * Cx(a - ep)) IN ball(cexp(ii * Cx a),r)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      MP_TAC(ISPECL [`a:real`; `--ep:real`] MOI_PDG_CEXP_II_CLOSE) THEN
      REWRITE_TAC[GSYM real_sub; REAL_ABS_NEG] THEN ASM_REAL_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->real` (LABEL_TAC "d")) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->real`;
                 `{s:real^N->bool | s IN L /\ aff_dim s = &2 /\ w IN s}`]
    MOI_PDG_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "d" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(INST [`cexp(ii * Cx(a - m / &2))`,`z:complex`] (SPEC_ALL MOI_PDG_VS_COVER_ALL)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "d" (fun th -> MP_TAC(MATCH_MP th
    (CONJ (ASSUME `(s:real^N->bool) IN L`) (CONJ (ASSUME `aff_dim(s:real^N->bool) = &2`)
          (ASSUME `(w:real^N) IN s`))))) THEN
  DISCH_THEN(MP_TAC o SPEC `m / &2` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `m <= (d:(real^N->bool)->real) s` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < m` THEN REAL_ARITH_TAC);;

let MOI_PDG_RIGHT_INC = prove
 (`!f:real^1->real.
      (lift o f) continuous_on interval[vec 0,vec 1] /\
      (!t. t IN interval[vec 0,vec 1] /\ drop t < &1
           ==> ?d. &0 < d /\
                   !s. s IN interval[vec 0,vec 1] /\ drop t < drop s /\ drop s < drop t + d
                       ==> f t < f s)
      ==> !s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                drop s < drop t
                ==> f s < f t`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inc")) THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `interval[s:real^1,t] SUBSET interval[vec 0,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL_1] THEN
    MAP_EVERY UNDISCH_TAC [`(s:real^1) IN interval[vec 0,vec 1]`;
                           `(t:real^1) IN interval[vec 0,vec 1]`] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^1->real`; `interval[s:real^1,t]`] CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[COMPACT_INTERVAL; INTERVAL_EQ_EMPTY_1] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!p. p IN interval[s:real^1,t] /\ (f:real^1->real) p = f x0 /\ drop p < drop t ==> F`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `p:real^1` THEN STRIP_TAC THEN
    USE_THEN "inc" (MP_TAC o SPEC `p:real^1`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `v = lift(drop p + min (d / &2) ((drop t - drop p) / &2))` THEN
    SUBGOAL_THEN `drop p < drop v /\ drop v < drop p + d /\ drop v < drop t`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^1) IN interval[s,t]` ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^1) IN interval[s,t]` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^1->real) p < f v` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^1->real) v <= f x0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A = {u:real^1 | u IN interval[s,t] /\ lift(f u) IN {lift(f x0)}}` THEN
  MP_TAC(ISPECL [`drop`; `A:real^1->bool`] CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `interval[s:real^1,t]` THEN
        REWRITE_TAC[BOUNDED_INTERVAL] THEN EXPAND_TAC "A" THEN SET_TAC[];
        EXPAND_TAC "A" THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
        REWRITE_TAC[CLOSED_INTERVAL; CLOSED_SING] THEN
        SUBGOAL_THEN `(\u:real^1. lift(f u)) = lift o f` SUBST1_TAC THENL
         [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[]];
      EXPAND_TAC "A" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; IN_SING] THEN
      EXISTS_TAC `x0:real^1` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `lift o drop = (\x:real^1. x)` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; REWRITE_TAC[CONTINUOUS_ON_ID]]];
    ALL_TAC] THEN
  EXPAND_TAC "A" THEN REWRITE_TAC[IN_ELIM_THM; IN_SING; LIFT_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `drop u < drop t` THENL
   [USE_THEN "key" MATCH_MP_TAC THEN EXISTS_TAC `u:real^1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `u:real^1 = t` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ] THEN UNDISCH_TAC `(u:real^1) IN interval[s,t]` THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^1) IN interval[s,t]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^1->real) s = f x0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^1->real) s <= f x0` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `(f:real^1->real) y <= f x0`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`(f:real^1->real) t <= f s`; `(f:real^1->real) t = f x0`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "key" MATCH_MP_TAC THEN EXISTS_TAC `s:real^1` THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_LIFT_STEP = prove
 (`!a b:complex. &0 < Im(cnj(cexp a) * cexp b) /\ norm(b - a) < pi / &2 ==> Im a < Im b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CNJ_CEXP; GSYM CEXP_ADD; IM_CEXP] THEN
  REWRITE_TAC[IM_ADD; IM_CNJ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sin(Im b - Im a)` MP_TAC THENL
   [UNDISCH_TAC `&0 < exp(Re(cnj a + b)) * sin(--Im a + Im b)` THEN
    REWRITE_TAC[REAL_ARITH `--x + y = y - x`] THEN
    MP_TAC(SPEC `Re(cnj a + b)` REAL_EXP_POS_LT) THEN
    MESON_TAC[REAL_LT_MUL_EQ; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(Im b - Im a) < pi / &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `norm(b - a:complex)` THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `b - a:complex` COMPLEX_NORM_GE_RE_IM) THEN
    REWRITE_TAC[IM_SUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `(p ==> q ==> r) <=> (p /\ ~r ==> ~q)`] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x - y = --(y - x)`] THEN REWRITE_TAC[SIN_NEG] THEN
  REWRITE_TAC[REAL_ARITH `--x <= &0 <=> &0 <= x`] THEN MATCH_MP_TAC SIN_POS_PI_LE THEN
  MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_CEXP_POLAR = prove
 (`!q. cexp q = Cx(exp(Re q)) * cexp(ii * Cx(Im q))`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [COMPLEX_EXPAND] THEN
  REWRITE_TAC[CEXP_ADD; CX_EXP]);;

let MOI_PDG_LIFT_IM_CONT = prove
 (`!s. (\z:complex. lift(Im z)) continuous_on s`,
  GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[linear; IM_ADD; IM_CMUL; LIFT_ADD; LIFT_CMUL]);;

let MOI_PDG_WIND_INJ = prove
 (`!P:complex->complex.
      P continuous_on (:complex) /\
      (!t z. &0 <= t ==> P(Cx t * z) = Cx t * P z) /\
      (!z. ~(z = Cx(&0)) ==> ~(P z = Cx(&0))) /\
      (winding_number((\t. P(cexp(ii * Cx(&2 * pi * drop t)))),Cx(&0)) = Cx(&1) \/
       winding_number((\t. P(cexp(ii * Cx(&2 * pi * drop t)))),Cx(&0)) = --Cx(&1)) /\
      (!a. ?d. &0 < d /\
               !ep. &0 < ep /\ ep < d
                    ==> &0 < Im(cnj(P(cexp(ii * Cx a))) * P(cexp(ii * Cx(a + ep)))))
      ==> !z1 z2. P z1 = P z2 ==> z1 = z2`,
  GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC `g = \t. (P:complex->complex)(cexp(ii * Cx(&2 * pi * drop t)))` THEN
  SUBGOAL_THEN `path(g:real^1->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[path] THEN
    SUBGOAL_THEN `(\t. (P:complex->complex)(cexp(ii * Cx(&2 * pi * drop t)))) =
                  P o circlepath(Cx(&0),&1)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; CIRCLEPATH; COMPLEX_ADD_LID; COMPLEX_MUL_LID] THEN
      GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[CX_MUL] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[GSYM path; PATH_CIRCLEPATH] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. ~((g:real^1->complex) t = Cx(&0))` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CEXP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->complex`; `Cx(&0)`] WINDING_NUMBER_AS_CONTINUOUS_LOGARITHM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[path_image; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^1->complex` STRIP_ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_ADD_LID]) THEN
  SUBGOAL_THEN `(lift o (\t. Im((q:real^1->complex) t))) continuous_on interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `lift o (\t. Im((q:real^1->complex) t)) = (\z. lift(Im z)) o q`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN REWRITE_TAC[MOI_PDG_LIFT_IM_CONT] THEN
    ASM_MESON_TAC[path];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. t IN interval[vec 0,vec 1] /\ drop t < &1
        ==> ?d. &0 < d /\
                !s. s IN interval[vec 0,vec 1] /\ drop t < drop s /\ drop s < drop t + d
                    ==> Im((q:real^1->complex) t) < Im(q s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&2 * pi * drop t` o check (fun th ->
      can (find_term ((=) `cnj`)) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?d1. &0 < d1 /\
                   !s. s IN interval[vec 0,vec 1] /\ dist(s,t) < d1
                       ==> dist((q:real^1->complex) s,q t) < pi / &2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `path(q:real^1->complex)` THEN REWRITE_TAC[path; continuous_on] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^1`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `pi / &2`) THEN
      ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `min d1 (d0 / (&2 * pi))` THEN
    SUBGOAL_THEN `&0 < &2 * pi` ASSUME_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV] THEN
    X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_PDG_LIFT_STEP THEN CONJ_TAC THENL
     [SUBGOAL_THEN `cexp((q:real^1->complex) t) = g t /\ cexp(q s) = g s` (fun th ->
        REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `&2 * pi * drop s = &2 * pi * drop t + &2 * pi * (drop s - drop t)`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `drop s - drop t < d0 / (&2 * pi)` MP_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC];
      REWRITE_TAC[GSYM dist] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[DIST_REAL; GSYM drop] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\t. Im((q:real^1->complex) t)` MOI_PDG_RIGHT_INC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "mono") THEN
  SUBGOAL_THEN `Im((q:real^1->complex)(vec 1)) - Im(q(vec 0)) = &2 * pi` ASSUME_TAC THENL
   [SUBGOAL_THEN `Im((q:real^1->complex)(vec 0)) < Im(q(vec 1))` MP_TAC THENL
     [USE_THEN "mono" MATCH_MP_TAC THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; DROP_VEC; REAL_LT_01];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `Im` o check (fun th ->
      can (find_term ((=) `pathfinish:(real^1->complex)->complex`)) (concl th))) THEN
    REWRITE_TAC[pathfinish; pathstart; IM_SUB] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[IM_MUL_CX; IM_MUL_II; RE_CX; RE_NEG] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1] /\ drop t < &1
                    ==> Im((q:real^1->complex)(vec 0)) <= Im(q t) /\
                        Im(q t) < Im(q(vec 0)) + &2 * pi` (LABEL_TAC "range") THENL
   [X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_CASES_TAC `t:real^1 = vec 0` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "mono" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; DROP_VEC] THEN
      UNDISCH_TAC `~(t:real^1 = vec 0)` THEN UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `Im((q:real^1->complex) t) < Im(q(vec 1))` MP_TAC THENL
       [USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; DROP_VEC];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:complex->complex)(Cx(&0)) = Cx(&0)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPECL [`&0`; `Cx(&0)`] o check (fun th ->
      can (find_term ((=) `(P:complex->complex)(Cx t * z)`)) (concl th))) THEN
    REWRITE_TAC[REAL_LE_REFL; COMPLEX_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. ~(z = Cx(&0))
        ==> lift(Arg z / (&2 * pi)) IN interval[vec 0,vec 1] /\
            drop(lift(Arg z / (&2 * pi))) < &1 /\
            (P:complex->complex) z =
            Cx(norm z) * cexp((q:real^1->complex)(lift(Arg z / (&2 * pi))))`
  (LABEL_TAC "polar") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPEC `z:complex` ARG) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "zp"))) THEN
    SUBGOAL_THEN `&0 < &2 * pi` ASSUME_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `lift(Arg z / (&2 * pi)) IN interval[vec 0,vec 1] /\
                  drop(lift(Arg z / (&2 * pi))) < &1` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_LT_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "zp" (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `(P:complex->complex)(Cx t * z)`)) (concl th)
      then REWRITE_TAC[MATCH_MP (SPECL [`norm(z:complex)`; `cexp(ii * Cx(Arg z))`] th)
                        (ISPEC `z:complex` NORM_POS_LE)] else NO_TAC) THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `cexp((q:real^1->complex)(lift(Arg z / (&2 * pi)))) =
                  g(lift(Arg z / (&2 * pi)))` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[LIFT_DROP] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < &2 * pi` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z1:complex`; `z2:complex`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `z1 = Cx(&0)` THEN ASM_CASES_TAC `z2 = Cx(&0)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "polar" (fun th -> MP_TAC(MATCH_MP th (ASSUME `~(z1 = Cx(&0))`))) THEN
  USE_THEN "polar" (fun th -> MP_TAC(MATCH_MP th (ASSUME `~(z2 = Cx(&0))`))) THEN
  ABBREV_TAC `t1 = lift(Arg z1 / (&2 * pi))` THEN
  ABBREV_TAC `t2 = lift(Arg z2 / (&2 * pi))` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx(norm(z1:complex) * exp(Re((q:real^1->complex) t1))) * cexp(ii * Cx(Im(q t1))) =
                Cx(norm(z2:complex) * exp(Re(q t2))) * cexp(ii * Cx(Im(q t2)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CX_MUL; GSYM COMPLEX_MUL_ASSOC; GSYM MOI_PDG_CEXP_POLAR] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z1:complex) * exp(Re((q:real^1->complex) t1)) =
                norm(z2:complex) * exp(Re(q t2))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:complex->real`) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; NORM_CEXP_II; COMPLEX_NORM_CX; REAL_MUL_RID] THEN
    SIMP_TAC[REAL_ABS_MUL; REAL_ABS_NORM; REAL_ABS_EXP];
    ALL_TAC] THEN
  SUBGOAL_THEN `Im((q:real^1->complex) t1) = Im(q t2)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_CEXP_II_INJ THEN CONJ_TAC THENL
     [USE_THEN "range" (MP_TAC o SPEC `t1:real^1`) THEN
      USE_THEN "range" (MP_TAC o SPEC `t2:real^1`) THEN
      REWRITE_TAC[ASSUME `(t1:real^1) IN interval[vec 0,vec 1]`; ASSUME `drop(t1:real^1) < &1`;
                  ASSUME `(t2:real^1) IN interval[vec 0,vec 1]`; ASSUME `drop(t2:real^1) < &1`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(COMPLEX_FIELD `!a x y. ~(a = Cx(&0)) /\ a * x = a * y ==> x = y`) THEN
    EXISTS_TAC `Cx(norm(z1:complex) * exp(Re((q:real^1->complex) t1)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[CX_INJ; REAL_ENTIRE; REAL_EXP_NZ] THEN ASM_REWRITE_TAC[NORM_EQ_0; COMPLEX_VEC_0];
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && is_eq(concl th) &&
         can (find_term ((=) `exp`)) (concl th) && not(can (find_term ((=) `cexp`)) (concl th))
         then GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th] else NO_TAC) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `t1:real^1 = t2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `(t1:real^1) IN interval[vec 0,vec 1]` ||
      concl th = `(t2:real^1) IN interval[vec 0,vec 1]`))) THEN
    REPEAT DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `~(a < b) /\ ~(b < a) ==> a = b`) THEN CONJ_TAC THEN
    DISCH_TAC THENL
     [SUBGOAL_THEN `Im((q:real^1->complex) t1) < Im(q t2)` MP_TAC THENL
       [USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `Im((q:real^1->complex) t2) < Im(q t1)` MP_TAC THENL
       [USE_THEN "mono" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Arg z1 = Arg z2` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`lift(Arg z1 / (&2 * pi)) = t1`; `lift(Arg z2 / (&2 * pi)) = t2`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LIFT_EQ] THEN
    MP_TAC PI_POS THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z1:complex) = norm(z2:complex)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `exp`)) (concl th) && not(can (find_term ((=) `cexp`)) (concl th)))) THEN
    ASM_REWRITE_TAC[REAL_EQ_MUL_RCANCEL; REAL_EXP_NZ];
    ALL_TAC] THEN
  MP_TAC(SPEC `z1:complex` ARG) THEN MP_TAC(SPEC `z2:complex` ARG) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let MOI_PDG_LIN_IM_CNJ = prove
 (`!(L:complex->complex) x y. linear L
      ==> Im(cnj(L x) * L y) = det(matrix L) * Im(cnj x * y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  REWRITE_TAC[complex_mul; IM] THEN REWRITE_TAC[RE_CNJ; IM_CNJ; DET_2] THEN
  REWRITE_TAC[RE_DEF; IM_DEF] THEN
  SIMP_TAC[MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH; DOT_2] THEN
  CONV_TAC REAL_RING);;

let MOI_PDG_GMAP_UNIT = prove
 (`!k b th1 th2 (s:real^N->bool) t.
      &0 < k /\ th1 s <= t /\ t <= th2 s /\ k * (th2 s - th1 s) < &2 * pi
      ==> moi_pdg_gmap k b th1 th2 s (cexp(ii * Cx(k * (b s + t)))) =
          cexp(ii * Cx(b s + t))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_gmap] THEN
  MP_TAC(ISPECL [`k:real`; `b(s:real^N->bool):real`; `th1(s:real^N->bool):real`;
                 `th2(s:real^N->bool):real`; `&1`; `t:real`] MOI_PDG_ANGZ_POLAR) THEN
  ASM_REWRITE_TAC[REAL_POS; COMPLEX_MUL_LID]);;

let MOI_PDG_VS_ANG_INC = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 a.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      (!s. s IN L /\ aff_dim s = &2 /\ w IN s ==> &0 < det(jacobian (H s) (at (vec 0))))
      ==> ?d. &0 < d /\
              !ep. &0 < ep /\ ep < d
                   ==> &0 < Im(cnj(moi_pdg_pmap L w k b th1 th2 H (cexp(ii * Cx a))) *
                               moi_pdg_pmap L w k b th1 th2 H (cexp(ii * Cx(a + ep))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_UPPER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `min (k * (th2(s:real^N->bool) - t)) (k * pi)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `ep:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < ep / k /\ ep / k < th2(s:real^N->bool) - t /\ ep / k < pi`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ] THEN
    UNDISCH_TAC `ep < min (k * (th2(s:real^N->bool) - t)) (k * pi)` THEN
    REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cexp(ii * Cx(a + ep)) = cexp(ii * Cx(k * (b(s:real^N->bool) + t + ep / k)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `cexp(ii * Cx a)`
                            then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[GSYM CEXP_ADD; GSYM COMPLEX_ADD_LDISTRIB; GSYM CX_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `cexp(ii * Cx a)`
                          then REWRITE_TAC[th] else NO_TAC) THEN
  MP_TAC(INST [`cexp(ii * Cx(k * (b(s:real^N->bool) + t)))`,`z:complex`]
    (SPEC_ALL MOI_PDG_VS_PMAP_EQ)) THEN
  MP_TAC(INST [`cexp(ii * Cx(k * (b(s:real^N->bool) + t + ep / k)))`,`z:complex`]
    (SPEC_ALL MOI_PDG_VS_PMAP_EQ)) THEN
  ASM_REWRITE_TAC[MOI_PDG_SSEC_UNIT] THEN
  ANTS_TAC THENL
   [EXISTS_TAC `t + ep / k` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL
   [EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `moi_pdg_gmap k b th1 th2 (s:real^N->bool)
                  (cexp(ii * Cx(k * (b s + t + ep / k)))) = cexp(ii * Cx(b s + t + ep / k)) /\
                moi_pdg_gmap k b th1 th2 s (cexp(ii * Cx(k * (b s + t)))) =
                cexp(ii * Cx(b s + t))` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_GMAP_UNIT THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[MOI_PDG_LIN_IM_CNJ; LINEAR_FRECHET_DERIVATIVE; GSYM jacobian;
           ASSUME `(H:(real^N->bool)->complex->complex) s differentiable at (vec 0)`] THEN
  REWRITE_TAC[MOI_PDG_IM_CNJ_UNIT; REAL_ARITH `(a + t + e) - (a + t) = e:real`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC SIN_POS_PI THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_VS_PMAP_INJ = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      MOI_SMO_VERTEX_DEGREE_STATEMENT /\
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      (!s. s IN L /\ aff_dim s = &2 /\ w IN s ==> &0 < det(jacobian (H s) (at (vec 0))))
      ==> !z1 z2. moi_pdg_pmap L w k b th1 th2 H z1 = moi_pdg_pmap L w k b th1 th2 H z2
                  ==> z1 = z2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_WIND_INJ THEN
  REWRITE_TAC[ETA_AX] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_CONT) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_HOMOG) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MP_TAC(INST [`z:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_PMAP_NZ)) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_WINDING) THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_ANG_INC) THEN ASM_REWRITE_TAC[]]);;


(* Sign consistency of the per-triangle linearizations (leaf D4a) and the          *)
(* positively oriented vertex setting (MOI_PDG_VS_POS_EXISTS).                    *)

let MOI_PDG_CEXP_II_RE_IM = prove
 (`!g. Re(cexp(ii * Cx g)) = cos g /\ Im(cexp(ii * Cx g)) = sin g`,
  REWRITE_TAC[RE_CEXP; IM_CEXP; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX; REAL_NEG_0;
              REAL_EXP_0; REAL_MUL_LID]);;

let MOI_PDG_UPBOX = prove
 (`!k a t1 t2 t t0. &0 < k /\ t1 <= t /\ t < t2 /\ &0 < t0
     ==> ?eta. &0 < eta /\
               !x. &0 <= Im x /\ Im x <= eta /\ abs(Re x - t0) <= eta
                   ==> cexp(ii * Cx(k * (a + t))) * x IN moi_pdg_sec k a t1 t2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = min (k * (t2 - t)) (pi / &2)` THEN
  SUBGOAL_THEN `&0 < g /\ g <= k * (t2 - t) /\ g <= pi / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN SUBGOAL_THEN `&0 < k * (t2 - t)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; MP_TAC PI_POS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sin g /\ &0 <= cos g /\ cos g <= &1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC COS_POS_PI_LE THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `g:real` COS_BOUNDS) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (t0 / &2) (t0 * sin g / &2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `x:complex` THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Im x / sin g /\ &0 <= Re x - Im x / sin g * cos g`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN
    SUBGOAL_THEN `Im x / sin g * cos g <= Im x / sin g` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `Im x / sin g <= t0 / &2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `bb = Im x / sin g` THEN
  ABBREV_TAC `aa = Re x - bb * cos g` THEN
  SUBGOAL_THEN `x = Cx aa + Cx bb * cexp(ii * Cx g)` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_MUL_CX; IM_MUL_CX; RE_CX; IM_CX;
                MOI_PDG_CEXP_II_RE_IM] THEN
    MAP_EVERY EXPAND_TAC ["aa"; "bb"] THEN
    UNDISCH_TAC `&0 < sin g` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `cexp(ii * Cx(k * (a + t))) * (Cx aa + Cx bb * cexp(ii * Cx g)) IN
                moi_pdg_cone2 (cexp(ii * Cx(k * (a + t)))) (cexp(ii * Cx(k * (a + t) + g)))`
  MP_TAC THENL
   [REWRITE_TAC[moi_pdg_cone2; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`aa:real`; `bb:real`] THEN ASM_REWRITE_TAC[COMPLEX_CMUL] THEN
    REWRITE_TAC[CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k * (a + t)`; `g:real`;
    `cexp(ii * Cx(k * (a + t))) * (Cx aa + Cx bb * cexp(ii * Cx g))`] MOI_PDG_CONE2_POLAR) THEN
  ANTS_TAC THENL [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[moi_pdg_sec; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `t + tau / k`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `t1 <= t /\ &0 <= x ==> t1 <= t + x`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    MATCH_MP_TAC(REAL_ARITH `x <= t2 - t ==> t + x <= t2`) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD]);;

let MOI_PDG_LOWBOX = prove
 (`!k a t1 t2 t t0. &0 < k /\ t1 < t /\ t <= t2 /\ &0 < t0
     ==> ?eta. &0 < eta /\
               !x. --eta <= Im x /\ Im x <= &0 /\ abs(Re x - t0) <= eta
                   ==> cexp(ii * Cx(k * (a + t))) * x IN moi_pdg_sec k a t1 t2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = min (k * (t - t1)) (pi / &2)` THEN
  SUBGOAL_THEN `&0 < g /\ g <= k * (t - t1) /\ g <= pi / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN SUBGOAL_THEN `&0 < k * (t - t1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; MP_TAC PI_POS THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sin g /\ &0 <= cos g /\ cos g <= &1` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIN_POS_PI THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC COS_POS_PI_LE THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC `g:real` COS_BOUNDS) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `min (t0 / &2) (t0 * sin g / &2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `x:complex` THEN REWRITE_TAC[REAL_LE_MIN] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= --Im x / sin g /\ &0 <= Re x - --Im x / sin g * cos g`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN
    SUBGOAL_THEN `--Im x / sin g * cos g <= --Im x / sin g` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `--Im x / sin g <= t0 / &2` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `aa = --Im x / sin g` THEN
  ABBREV_TAC `bb = Re x - aa * cos g` THEN
  SUBGOAL_THEN `x = Cx aa * cexp(ii * Cx(--g)) + Cx bb` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_MUL_CX; IM_MUL_CX; RE_CX; IM_CX;
                MOI_PDG_CEXP_II_RE_IM; SIN_NEG; COS_NEG] THEN
    MAP_EVERY EXPAND_TAC ["bb"; "aa"] THEN
    UNDISCH_TAC `&0 < sin g` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `cexp(ii * Cx(k * (a + t))) * (Cx aa * cexp(ii * Cx(--g)) + Cx bb) IN
                moi_pdg_cone2 (cexp(ii * Cx(k * (a + t) - g)))
                              (cexp(ii * Cx((k * (a + t) - g) + g)))`
  MP_TAC THENL
   [REWRITE_TAC[moi_pdg_cone2; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`aa:real`; `bb:real`] THEN ASM_REWRITE_TAC[COMPLEX_CMUL] THEN
    REWRITE_TAC[REAL_ARITH `(x - g) + g = x:real`] THEN
    REWRITE_TAC[real_sub; CX_ADD; CX_NEG; COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k * (a + t) - g`; `g:real`;
    `cexp(ii * Cx(k * (a + t))) * (Cx aa * cexp(ii * Cx(--g)) + Cx bb)`] MOI_PDG_CONE2_POLAR) THEN
  ANTS_TAC THENL [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[moi_pdg_sec; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `t - (g - tau) / k`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= t - t1 ==> t1 <= t - x`) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `t <= t2 /\ &0 <= x ==> t - x <= t2`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD]);;

let MOI_PDG_VS_SEC_SMOOTH = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 s y.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\
      y IN moi_pdg_ssec k b th1 th2 s /\ ~(y = Cx(&0)) /\ norm y < rho0
      ==> ?r. &0 < r /\
              smooth_map_on (ball(y,r))
                (H s o moi_pdg_angf (inv k) (k * (b s + (th1 s + th2 s) / &2))) /\
              (!z. z IN ball(y,r) INTER moi_pdg_ssec k b th1 th2 s
                   ==> (H s o moi_pdg_angf (inv k) (k * (b s + (th1 s + th2 s) / &2))) z =
                       moi_pdg_fmap U phi f h z) /\
              (!z. z IN ball(y,r) ==> norm z < rho0) /\
              ~(det(jacobian (H s o moi_pdg_angf (inv k) (k * (b s + (th1 s + th2 s) / &2)))
                    (at y)) = &0) /\
              &0 < det(jacobian (H s o moi_pdg_angf (inv k) (k * (b s + (th1 s + th2 s) / &2)))
                         (at y)) *
                   det(jacobian (H s) (at (vec 0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. z IN moi_pdg_ssec k b th1 th2 (s:real^N->bool) /\ ~(z = Cx(&0))
        ==> (Im(cexp(--(ii * Cx(k * (b s + (th1 s + th2 s) / &2)))) * z) = &0
             ==> &0 < Re(cexp(--(ii * Cx(k * (b s + (th1 s + th2 s) / &2)))) * z))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:real`; `b(s:real^N->bool):real`; `th1(s:real^N->bool):real`;
                   `th2(s:real^N->bool):real`; `z:complex`] MOI_PDG_SEC_SLIT) THEN
    REWRITE_TAC[GSYM moi_pdg_ssec] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Os = {z:complex | Im(cexp(--(ii * Cx(k * (b(s:real^N->bool) +
                                    (th1 s + th2 s) / &2)))) * z) = &0
                                ==> &0 < Re(cexp(--(ii * Cx(k * (b s +
                                    (th1 s + th2 s) / &2)))) * z)}` THEN
  SUBGOAL_THEN `open(Os:complex->bool) /\ (y:complex) IN Os /\
                smooth_map_on Os (moi_pdg_angf (inv k)
                   (k * (b(s:real^N->bool) + (th1 s + th2 s) / &2))) /\
                ~(Cx(&0) IN Os)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Os" THEN REWRITE_TAC[MOI_PDG_SLIT_OPEN_C; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_MUL_RZERO; RE_CX; IM_CX; REAL_LT_REFL] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_PDG_ANGF_SMOOTH THEN REWRITE_TAC[MOI_PDG_SLIT_OPEN_C; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `y:complex` (REWRITE_RULE[OPEN_CONTAINS_BALL]
    (ASSUME `open(Os:complex->bool)`))) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min r1 (rho0 - norm(y:complex))` THEN
  SUBGOAL_THEN `!z. z IN ball(y:complex,min r1 (rho0 - norm y))
                    ==> z IN Os /\ ~(z = Cx(&0)) /\ norm z < rho0` (LABEL_TAC "inb") THENL
   [X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:complex) IN Os` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `ball(y:complex,r1)`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_BALL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [MAP_EVERY (MP_TAC o ASSUME) [`(z:complex) IN Os`; `~(Cx(&0) IN Os)`] THEN MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`z:complex`; `y:complex`] NORM_TRIANGLE_SUB) THEN
    UNDISCH_TAC `dist(y:complex,z) < rho0 - norm y` THEN REWRITE_TAC[dist] THEN
    MP_TAC(ISPECL [`y:complex`; `z:complex`] NORM_SUB) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < min r1 (rho0 - norm(y:complex))` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Gs = moi_pdg_angf (inv k) (k * (b(s:real^N->bool) + (th1 s + th2 s) / &2))` THEN
  SUBGOAL_THEN `!z. z IN Os ==> norm((Gs:complex->complex) z) = norm z` ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN EXPAND_TAC "Gs" THEN
    MATCH_MP_TAC MOI_PDG_ANGF_NORM THEN MAP_EVERY (MP_TAC o ASSUME) [`(z:complex) IN Os`; `~(Cx(&0) IN Os)`] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN Os ==> moi_pdg_gmap k b th1 th2 (s:real^N->bool) z = Gs z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Gs" THEN REWRITE_TAC[moi_pdg_gmap; moi_pdg_angz] THEN
    COND_CASES_TAC THENL [UNDISCH_TAC `(z:complex) IN Os` THEN ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(y:complex,min r1 (rho0 - norm y)))
                  ((H:(real^N->bool)->complex->complex) s o Gs)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `z:complex` THEN
      DISCH_TAC THEN USE_THEN "inb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `(z:complex) IN ball(y,min r1 (rho0 - norm y))`))) THEN
      SIMP_TAC[ASSUME `!z. z IN Os ==> norm((Gs:complex->complex) z) = norm z`;
               ASSUME `(z:complex) IN Os`] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `Os:complex->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN USE_THEN "inb" (fun th -> MESON_TAC[th])];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    USE_THEN "inb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(z:complex) IN ball(y,min r1 (rho0 - norm y))`))) THEN
    MP_TAC(SPEC_ALL MOI_PDG_VS_SEC_CHART) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    REWRITE_TAC[o_THM; moi_pdg_fmap] THEN
    MP_TAC(ASSUME `moi_pdg_st (f:real^3->real^3) ((h:real^N->real^3)(chart_inv(U,phi) z)) =
                   (H:(real^N->bool)->complex->complex) s (moi_pdg_gmap k b th1 th2 s z)`) THEN
    MP_TAC(ASSUME `!z. z IN Os ==> moi_pdg_gmap k b th1 th2 (s:real^N->bool) z = (Gs:complex->complex) z`) THEN
    MP_TAC(ASSUME `(z:complex) IN Os`) THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "inb" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN `norm((Gs:complex->complex) y) < e(s:real^N->bool)` ASSUME_TAC THENL
   [SIMP_TAC[ASSUME `!z. z IN Os ==> norm((Gs:complex->complex) z) = norm z`;
             ASSUME `(y:complex) IN Os`] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(Gs:complex->complex) differentiable at y /\
                (H:(real^N->bool)->complex->complex) s differentiable at (Gs y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "Gs" THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `Os:complex->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN
      ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0]];
    ALL_TAC] THEN
  SIMP_TAC[MOI_PDG_DET_CHAIN; ASSUME `(Gs:complex->complex) differentiable at y`;
           ASSUME `(H:(real^N->bool)->complex->complex) s differentiable at
                    ((Gs:complex->complex) y)`] THEN
  SUBGOAL_THEN `det(jacobian (Gs:complex->complex) (at y)) = inv k` SUBST1_TAC THENL
   [EXPAND_TAC "Gs" THEN MATCH_MP_TAC MOI_PDG_ANGF_DET THEN
    UNDISCH_TAC `(y:complex) IN Os` THEN EXPAND_TAC "Os" THEN REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Gs:complex->complex) y IN ball(vec 0,e(s:real^N->bool)) INTER
                moi_pdg_dcone b th1 th2 s` ASSUME_TAC THENL
   [SUBGOAL_THEN `(Gs:complex->complex) y = moi_pdg_gmap k b th1 th2 (s:real^N->bool) y`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC(ASSUME `!z. z IN Os ==> moi_pdg_gmap k b th1 th2 (s:real^N->bool) z = (Gs:complex->complex) z`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(INST [`y:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_SEC_CHART)) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Sd = ball(vec 0:complex,e(s:real^N->bool)) INTER moi_pdg_dcone b th1 th2 s` THEN
  SUBGOAL_THEN `!x. x IN Sd ==> ~(det(jacobian ((H:(real^N->bool)->complex->complex) s)
                                    (at x)) = &0)` ASSUME_TAC THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_PDG_DET_NZ_INJ THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN UNDISCH_TAC `(x:complex) IN Sd` THEN EXPAND_TAC "Sd" THEN
      SIMP_TAC[IN_INTER];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
        can (find_term ((=) `moi_pdg_st`)) (concl th) && is_forall(concl th))) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `(x:complex) IN Sd` THEN EXPAND_TAC "Sd" THEN
        REWRITE_TAC[moi_pdg_dcone];
        SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(jacobian ((H:(real^N->bool)->complex->complex) s)
                         (at ((Gs:complex->complex) y))) *
                    det(jacobian (H s) (at (vec 0)))` MP_TAC THENL
   [MP_TAC(ISPECL [`Sd:complex->bool`;
                    `\x. det(jacobian ((H:(real^N->bool)->complex->complex) s) (at x))`;
                    `(Gs:complex->complex) y`; `vec 0:complex`] MOI_PDG_SIGN_CONST) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN EXPAND_TAC "Sd" THEN
      REWRITE_TAC[moi_pdg_dcone] THEN MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_BALL; MOI_PDG_CONE2_CONVEX];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_PDG_JAC_DET_CONT THEN ASM_REWRITE_TAC[OPEN_BALL];
        EXPAND_TAC "Sd" THEN SET_TAC[]];
      EXPAND_TAC "Sd" THEN
      REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; moi_pdg_dcone; moi_pdg_cone2; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`&0`; `&0`] THEN
      REWRITE_TAC[REAL_LE_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv k` MP_TAC THENL [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `~(det(jacobian ((H:(real^N->bool)->complex->complex) s)
                       (at ((Gs:complex->complex) y))) = &0)` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
  ABBREV_TAC `dH = det(jacobian ((H:(real^N->bool)->complex->complex) s)
                         (at ((Gs:complex->complex) y)))` THEN
  ABBREV_TAC `d0 = det(jacobian ((H:(real^N->bool)->complex->complex) s) (at (vec 0)))` THEN
  REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `(a * b) * c = b * (a * c)`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_SIGN_ARITH = prove
 (`!a b x y. &0 < a * b /\ &0 < a * x /\ &0 < b * y ==> &0 < x * y`,
  REWRITE_TAC[REAL_MUL_POS_LT] THEN REAL_ARITH_TAC);;

let MOI_PDG_DET_ROT_COMPOSE = prove
 (`!(A:complex->complex) c x.
      norm c = &1 /\ A differentiable at (c * x)
      ==> det(jacobian (A o (\z. c * z)) (at x)) = det(jacobian A (at (c * x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear (\z:complex. c * z)` ASSUME_TAC THENL
   [REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:complex. c * z`; `A:complex->complex`; `x:complex`] MOI_PDG_DET_CHAIN) THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_LINEAR; MOI_PDG_DET_CMUL] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let MOI_PDG_VS_SIGN_PAIR = prove
 (`!L sigma (h:real^N->real^3) h' w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
    s s' t t' a.
      MOI_SMO_CREASE_ORIENT_STATEMENT /\
      homeomorphism (UNIONS L,sphere(vec 0,&1)) (h,h') /\
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\ th1 s <= t /\ t < th2 s /\
      cexp(ii * Cx a) = cexp(ii * Cx(k * (b s + t))) /\
      s' IN L /\ aff_dim s' = &2 /\ w IN s' /\ th1 s' < t' /\ t' <= th2 s' /\
      cexp(ii * Cx a) = cexp(ii * Cx(k * (b s' + t')))
      ==> &0 < det(jacobian (H s) (at (vec 0))) * det(jacobian (H s') (at (vec 0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`s':real^N->bool`,`s:real^N->bool`] (SPEC_ALL MOI_PDG_VS_TRI)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = cexp(ii * Cx a)` THEN
  RULE_ASSUM_TAC(fun th -> if is_eq(concl th) && lhs(concl th) = `c:complex`
                           then SYM th else th) THEN
  ABBREV_TAC `t0 = rho0 / &2` THEN
  SUBGOAL_THEN `&0 < t0 /\ t0 < rho0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t0" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(c:complex) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[NORM_CEXP_II]; ALL_TAC] THEN
  SUBGOAL_THEN `c * Cx t0 IN moi_pdg_ssec k b th1 th2 (s:real^N->bool) /\
                c * Cx t0 IN moi_pdg_ssec k b th1 th2 (s':real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_pdg_ssec; moi_pdg_sec; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`t0:real`; `t:real`] THEN
      SUBST1_TAC(SYM(ASSUME `cexp(ii * Cx(k * (b(s:real^N->bool) + t))) = c`));
      MAP_EVERY EXISTS_TAC [`t0:real`; `t':real`] THEN
      SUBST1_TAC(SYM(ASSUME `cexp(ii * Cx(k * (b(s':real^N->bool) + t'))) = c`))] THEN
    REWRITE_TAC[COMPLEX_MUL_SYM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c * Cx t0 = Cx(&0)) /\ norm(c * Cx t0) < rho0` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_MUL_LID; NORM_CEXP_II] THEN
    CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_MUL_LID; REAL_ABS_0;
                      NORM_CEXP_II] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(INST [`c * Cx t0`,`y:complex`] (SPEC_ALL MOI_PDG_VS_SEC_SMOOTH)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(INST [`c * Cx t0`,`y:complex`; `s':real^N->bool`,`s:real^N->bool`]
    (SPEC_ALL MOI_PDG_VS_SEC_SMOOTH)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Ap = (H:(real^N->bool)->complex->complex) s o
                   moi_pdg_angf (inv k) (k * (b s + (th1 s + th2 s) / &2))` THEN
  ABBREV_TAC `Am = (H:(real^N->bool)->complex->complex) s' o
                   moi_pdg_angf (inv k) (k * (b s' + (th1 s' + th2 s') / &2))` THEN
  MP_TAC(ISPECL [`k:real`; `b(s:real^N->bool):real`; `th1(s:real^N->bool):real`;
                 `th2(s:real^N->bool):real`; `t:real`; `t0:real`] MOI_PDG_UPBOX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `cexp(ii * Cx(k * (b(s:real^N->bool) + t))) = c`;
              GSYM moi_pdg_ssec] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real`; `b(s':real^N->bool):real`; `th1(s':real^N->bool):real`;
                 `th2(s':real^N->bool):real`; `t':real`; `t0:real`] MOI_PDG_LOWBOX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `cexp(ii * Cx(k * (b(s':real^N->bool) + t'))) = c`;
              GSYM moi_pdg_ssec] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta3:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rr = min r1 r2` THEN
  ABBREV_TAC `eta = min (min eta2 eta3) (min (rr / &4) (t0 / &2))` THEN
  SUBGOAL_THEN `&0 < rr /\ rr <= r1 /\ rr <= r2 /\ &0 < eta /\ eta <= eta2 /\ eta <= eta3 /\
                &4 * eta <= rr /\ eta <= t0 / &2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["eta"; "rr"] THEN
    MAP_EVERY (MP_TAC o ASSUME) [`&0 < r1`; `&0 < r2`; `&0 < eta2`; `&0 < eta3`; `&0 < t0`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t0,rr) ==> c * x IN ball(c * Cx t0,r1) /\
                                            c * x IN ball(c * Cx t0,r2)`
  (LABEL_TAC "cb") THENL
   [X_GEN_TAC `x:complex` THEN REWRITE_TAC[IN_BALL; dist] THEN
    REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB; COMPLEX_NORM_MUL] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID] THEN
    MP_TAC(ASSUME `rr <= r1`) THEN MP_TAC(ASSUME `rr <= r2`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | (t0 - eta) <= Re x /\ Re x <= t0 + eta /\ abs(Im x) <= eta} SUBSET
                ball(Cx t0,rr)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL; dist] THEN X_GEN_TAC `x:complex` THEN
    STRIP_TAC THEN MP_TAC(ISPEC `Cx t0 - x` COMPLEX_NORM_LE_RE_IM) THEN
    REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX] THEN
    MAP_EVERY (MP_TAC o ASSUME) [`t0 - eta <= Re(x:complex)`; `Re(x:complex) <= t0 + eta`;
                                 `abs(Im(x:complex)) <= eta`; `&4 * eta <= rr`; `&0 < eta`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (\x:complex. c * x)` ASSUME_TAC THENL
   [REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(Cx t0,rr)) ((Ap:complex->complex) o (\x. c * x)) /\
                smooth_map_on (ball(Cx t0,rr)) ((Am:complex->complex) o (\x. c * x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THENL
     [EXISTS_TAC `ball(c * Cx t0,r1)`; EXISTS_TAC `ball(c * Cx t0,r2)`] THEN
    REWRITE_TAC[OPEN_BALL] THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
       USE_THEN "cb" (fun th -> REWRITE_TAC[MATCH_MP th
         (ASSUME `(x:complex) IN ball(Cx t0,rr)`)]);
       CONJ_TAC THENL
        [MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[OPEN_BALL];
         FIRST_ASSUM ACCEPT_TAC]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. t0 - eta <= Re x /\ Re x <= t0 + eta /\ abs(Im x) <= eta
                    ==> c * x IN ball(c * Cx t0,r1) /\ c * x IN ball(c * Cx t0,r2) /\
                        abs(Re x - t0) <= eta2 /\ abs(Re x - t0) <= eta3 /\
                        norm(c * x) < rho0` (LABEL_TAC "box") THENL
   [X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:complex) IN ball(Cx t0,rr)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `ball(Cx t0,rr)`)) (concl th) && not(is_forall(concl th)))) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    USE_THEN "cb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(x:complex) IN ball(Cx t0,rr)`))) THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MAP_EVERY (MP_TAC o ASSUME) [`t0 - eta <= Re(x:complex)`; `Re(x:complex) <= t0 + eta`;
                                   `eta <= eta2`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY (MP_TAC o ASSUME) [`t0 - eta <= Re(x:complex)`; `Re(x:complex) <= t0 + eta`;
                                   `eta <= eta3`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ball(c * Cx t0,r1)`)) (concl th) &&
      can (find_term ((=) `rho0:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `U:real^N->bool`;
                 `phi:real^N->real^2`; `Cx(&0)`; `c:complex`; `t0 - eta`; `t0 + eta`;
                 `f:real^3->real^3`; `eta:real`; `ball(Cx t0,rr)`;
                 `(Ap:complex->complex) o (\x. c * x)`;
                 `(Am:complex->complex) o (\x. c * x)`] MOI_PDG_CR_D4A) THEN
  REWRITE_TAC[COMPLEX_ADD_LID; REAL_ARITH `(t0 - eta + t0 + eta) / &2 = t0`] THEN
  SUBGOAL_THEN `(Ap:complex->complex) differentiable at (c * Cx t0) /\
                (Am:complex->complex) differentiable at (c * Cx t0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THENL
     [EXISTS_TAC `ball(c * Cx t0,r1)`; EXISTS_TAC `ball(c * Cx t0,r2)`] THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `det(jacobian ((Ap:complex->complex) o (\x. c * x)) (at (Cx t0))) =
                det(jacobian Ap (at (c * Cx t0))) /\
                det(jacobian ((Am:complex->complex) o (\x. c * x)) (at (Cx t0))) =
                det(jacobian Am (at (c * Cx t0)))` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_DET_ROT_COMPOSE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ASSUME `&0 < eta`) THEN REAL_ARITH_TAC;
      X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
      USE_THEN "box" (MP_TAC o SPEC `x:complex`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      MP_TAC(INST [`c * x:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_F_LOCAL)) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MP_TAC(ASSUME `norm(c * x:complex) < rho0`) THEN REAL_ARITH_TAC;
        SIMP_TAC[]];
      X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
      USE_THEN "box" (MP_TAC o SPEC `x:complex`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `&0 <= Im(x:complex)`) THEN MP_TAC(ASSUME `Im(x:complex) <= eta`) THEN
        REAL_ARITH_TAC;
        STRIP_TAC] THEN
      REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `c * x IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `eta2:real`)) (concl th))) THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `Im(x:complex) <= eta`) THEN MP_TAC(ASSUME `eta <= eta2`) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM moi_pdg_fmap] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Ap:complex->complex`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_pdg_fmap")) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER];
      X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
      USE_THEN "box" (MP_TAC o SPEC `x:complex`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `--eta <= Im(x:complex)`) THEN MP_TAC(ASSUME `Im(x:complex) <= &0`) THEN
        REAL_ARITH_TAC;
        STRIP_TAC] THEN
      REWRITE_TAC[o_THM] THEN
      SUBGOAL_THEN `c * x IN moi_pdg_ssec k b th1 th2 (s':real^N->bool)` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `eta3:real`)) (concl th))) THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME `--eta <= Im(x:complex)`) THEN MP_TAC(ASSUME `eta <= eta3`) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM moi_pdg_fmap] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Am:complex->complex`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_pdg_fmap")) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC MOI_PDG_SIGN_ARITH THEN
  MAP_EVERY EXISTS_TAC [`det(jacobian (Ap:complex->complex) (at (c * Cx t0)))`;
                        `det(jacobian (Am:complex->complex) (at (c * Cx t0)))`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_SIGN_ARITH2 = prove
 (`!x y z. &0 < x * y /\ &0 < z * y ==> &0 < x * z`,
  REWRITE_TAC[REAL_MUL_POS_LT] THEN REAL_ARITH_TAC);;

let MOI_PDG_VS_SIGN_DIR = prove
 (`!L sigma (h:real^N->real^3) h' w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 s1 s2 a.
      MOI_SMO_CREASE_ORIENT_STATEMENT /\
      homeomorphism (UNIONS L,sphere(vec 0,&1)) (h,h') /\
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      s1 IN L /\ aff_dim s1 = &2 /\ w IN s1 /\ s2 IN L /\ aff_dim s2 = &2 /\ w IN s2 /\
      cexp(ii * Cx a) IN moi_pdg_ssec k b th1 th2 s1 /\
      cexp(ii * Cx a) IN moi_pdg_ssec k b th1 th2 s2
      ==> &0 < det(jacobian (H s1) (at (vec 0))) * det(jacobian (H s2) (at (vec 0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_UPPER) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `su:real^N->bool` (X_CHOOSE_THEN `tu:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_LOWER) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `sl:real^N->bool` (X_CHOOSE_THEN `tl:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&0 < det(jacobian ((H:(real^N->bool)->complex->complex) su) (at (vec 0))) *
                    det(jacobian (H sl) (at (vec 0)))` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST [`su:real^N->bool`,`s:real^N->bool`; `sl:real^N->bool`,`s':real^N->bool`;
                       `tu:real`,`t:real`; `tl:real`,`t':real`]
      (SPEC_ALL MOI_PDG_VS_SIGN_PAIR)) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s /\
        cexp(ii * Cx a) IN moi_pdg_ssec k b th1 th2 s
        ==> &0 < det(jacobian ((H:(real^N->bool)->complex->complex) s) (at (vec 0))) *
                 det(jacobian (H su) (at (vec 0)))`
  (LABEL_TAC "su") THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `cexp(ii * Cx a) IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` THEN
    REWRITE_TAC[MOI_PDG_SSEC_UNIT] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `t < th2(s:real^N->bool)` THENL
     [SUBGOAL_THEN `&0 < det(jacobian ((H:(real^N->bool)->complex->complex) s) (at (vec 0))) *
                        det(jacobian (H sl) (at (vec 0)))` MP_TAC THENL
       [MATCH_MP_TAC(INST [`sl:real^N->bool`,`s':real^N->bool`; `tl:real`,`t':real`]
          (SPEC_ALL MOI_PDG_VS_SIGN_PAIR)) THEN
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `&0 < det(jacobian ((H:(real^N->bool)->complex->complex) su) (at (vec 0))) *
                         det(jacobian (H sl) (at (vec 0)))` THEN
      REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_PDG_SIGN_ARITH2 THEN
      EXISTS_TAC `det(jacobian ((H:(real^N->bool)->complex->complex) sl) (at (vec 0)))` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `th1(s:real^N->bool) < t` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MATCH_MP_TAC(INST [`su:real^N->bool`,`s:real^N->bool`; `s:real^N->bool`,`s':real^N->bool`;
                         `tu:real`,`t:real`; `t:real`,`t':real`]
        (SPEC_ALL MOI_PDG_VS_SIGN_PAIR)) THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_SIGN_ARITH2 THEN
  EXISTS_TAC `det(jacobian ((H:(real^N->bool)->complex->complex) su) (at (vec 0)))` THEN
  CONJ_TAC THEN USE_THEN "su" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_VS_SIGNS = prove
 (`!L sigma (h:real^N->real^3) h' w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      MOI_SMO_CREASE_ORIENT_STATEMENT /\
      homeomorphism (UNIONS L,sphere(vec 0,&1)) (h,h') /\
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> (!s. s IN L /\ aff_dim s = &2 /\ w IN s
               ==> &0 < det(jacobian (H s) (at (vec 0)))) \/
          (!s. s IN L /\ aff_dim s = &2 /\ w IN s
               ==> det(jacobian (H s) (at (vec 0))) < &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `TT = {s:real^N->bool | s IN L /\ aff_dim s = &2 /\ w IN s}` THEN
  ABBREV_TAC `D = \s:real^N->bool. det(jacobian ((H:(real^N->bool)->complex->complex) s)
                                          (at (vec 0)))` THEN
  SUBGOAL_THEN `!s. s IN TT ==> ~((D:(real^N->bool)->real) s = &0) /\
                                closed(moi_pdg_ssec k b th1 th2 s) /\
                                cexp(ii * Cx(k * (b s + th1 s))) IN
                                  moi_pdg_ssec k b th1 th2 s`
  (LABEL_TAC "tt") THENL
   [X_GEN_TAC `s:real^N->bool` THEN EXPAND_TAC "TT" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "D" THEN MATCH_MP_TAC MOI_PDG_DET_NZ_INJ THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_pdg_ssec] THEN MATCH_MP_TAC MOI_PDG_SEC_CLOSED THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_PDG_SSEC_UNIT] THEN EXISTS_TAC `th1(s:real^N->bool):real` THEN
      REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `E1 = UNIONS (IMAGE (\s. moi_pdg_ssec k b th1 th2 (s:real^N->bool))
                                 {s | s IN TT /\ &0 < (D:(real^N->bool)->real) s})` THEN
  ABBREV_TAC `E2 = UNIONS (IMAGE (\s. moi_pdg_ssec k b th1 th2 (s:real^N->bool))
                                 {s | s IN TT /\ (D:(real^N->bool)->real) s < &0})` THEN
  SUBGOAL_THEN `closed(E1:complex->bool) /\ closed(E2:complex->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E1"; "E2"] THEN CONJ_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[];
       REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN E1 <=> ?s. s IN TT /\ &0 < (D:(real^N->bool)->real) s /\
                                   z IN moi_pdg_ssec k b th1 th2 s` ASSUME_TAC THENL
   [EXPAND_TAC "E1" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN E2 <=> ?s. s IN TT /\ (D:(real^N->bool)->real) s < &0 /\
                                   z IN moi_pdg_ssec k b th1 th2 s` ASSUME_TAC THENL
   [EXPAND_TAC "E2" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:complex`; `&1`] CONNECTED_SPHERE) THEN
  REWRITE_TAC[DIMINDEX_2; LE_REFL; CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`E1:complex->bool`; `E2:complex->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sphere(vec 0:complex,&1) SUBSET E1 UNION E2` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(INST [`z:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_COVER_ALL)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) IN TT` ASSUME_TAC THENL
     [EXPAND_TAC "TT" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    USE_THEN "tt" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(s:real^N->bool) IN TT`))) THEN
    ASM_CASES_TAC `&0 < (D:(real^N->bool)->real) s` THENL
     [DISJ1_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `E1 INTER E2 INTER sphere(vec 0:complex,&1) = {}` (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:complex` THEN
    ASM_REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s2:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `z = cexp(ii * Cx(Arg z))` ASSUME_TAC THENL
     [MP_TAC(SPEC `z:complex` ARG) THEN ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < det(jacobian ((H:(real^N->bool)->complex->complex) s1) (at (vec 0))) *
                       det(jacobian (H s2) (at (vec 0)))` MP_TAC THENL
     [MATCH_MP_TAC(INST [`Arg z`,`a:real`] (SPEC_ALL MOI_PDG_VS_SIGN_DIR)) THEN
      REWRITE_TAC[GSYM(ASSUME `z = cexp(ii * Cx(Arg z))`)] THEN
      UNDISCH_TAC `(s1:real^N->bool) IN TT` THEN UNDISCH_TAC `(s2:real^N->bool) IN TT` THEN
      EXPAND_TAC "TT" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `&0 < (D:(real^N->bool)->real) s1` THEN
    UNDISCH_TAC `(D:(real^N->bool)->real) s2 < &0` THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[REAL_MUL_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. (D:(real^N->bool)->real) s =
                    det(jacobian ((H:(real^N->bool)->complex->complex) s) (at (vec 0)))`
  ASSUME_TAC THENL [EXPAND_TAC "D" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s ==> s IN TT` ASSUME_TAC THENL
   [EXPAND_TAC "TT" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THENL
   [DISJ2_TAC; DISJ1_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  (SUBGOAL_THEN `(s:real^N->bool) IN TT` ASSUME_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  USE_THEN "tt" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(s:real^N->bool) IN TT`))) THENL
   [UNDISCH_TAC `E1 INTER sphere(vec 0:complex,&1) = {}`;
    UNDISCH_TAC `E2 INTER sphere(vec 0:complex,&1) = {}`] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `cexp(ii * Cx(k * (b(s:real^N->bool) + th1 s)))`) THEN
  ASM_REWRITE_TAC[IN_SPHERE_0; NORM_CEXP_II] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((D:(real^N->bool)->real) s = &0)` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let moi_pdg_refl = new_definition
 `moi_pdg_refl (p:real^3) = vector[p$1; --(p$2); p$3]:real^3`;;

let MOI_PDG_REFL_COMPONENTS = prove
 (`!p. (moi_pdg_refl p)$1 = p$1 /\ (moi_pdg_refl p)$2 = --(p$2) /\
       (moi_pdg_refl p)$3 = p$3`,
  REWRITE_TAC[moi_pdg_refl; VECTOR_3]);;

let MOI_PDG_REFL_ORTH = prove
 (`orthogonal_transformation moi_pdg_refl`,
  REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; MOI_PDG_REFL_COMPONENTS] THEN REAL_ARITH_TAC;
    REWRITE_TAC[NORM_EQ; DOT_3; MOI_PDG_REFL_COMPONENTS] THEN REAL_ARITH_TAC]);;

let MOI_PDG_ST_REFL = prove
 (`!(f:real^3->real^3) y. moi_pdg_st (moi_pdg_refl o f) y = cnj(moi_pdg_st f y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPLEX_EQ; RE_CNJ; IM_CNJ] THEN
  REWRITE_TAC[moi_pdg_st; o_THM; MOI_PDG_REFL_COMPONENTS; RE_DEF; IM_DEF;
              VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_PDG_VTRI_FLIP = prove
 (`!L U phi k (f:real^3->real^3) (h:real^N->real^3) w s bs Qs v1 v2 th1 th2 e R H.
      moi_pdg_vtri L U phi k f h w s bs Qs v1 v2 th1 th2 e R H
      ==> moi_pdg_vtri L U phi k (moi_pdg_refl o f) h w s bs Qs v1 v2 th1 th2 e R
                       (cnj o H)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_vtri] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[OPEN_BALL; LINEAR_CNJ];
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_VEC_0; CNJ_CX];
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:complex` o check (fun th ->
      can (find_term ((=) `moi_pdg_st`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[o_THM; MOI_PDG_ST_REFL; MOI_PDG_REFL_COMPONENTS] THEN
    X_GEN_TAC `z:complex` THEN
    SUBGOAL_THEN `(H:complex->complex) differentiable at y` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(vec 0:complex,e)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_MESON_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `frechet_derivative (cnj o (H:complex->complex)) (at y) =
                  cnj o frechet_derivative H (at y)` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`H:complex->complex`; `cnj`; `y:complex`] MOI_PDG_FD_CHAIN) THEN
      REWRITE_TAC[ASSUME `(H:complex->complex) differentiable at y`;
                  MATCH_MP DIFFERENTIABLE_LINEAR LINEAR_CNJ] THEN
      DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[LINEAR_CNJ];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM; COMPLEX_VEC_0; CNJ_EQ_0] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN ASM_MESON_TAC[]]);;

let MOI_PDG_VS_FLIP = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> moi_pdg_vs L sigma h w delta U phi k b Q (moi_pdg_refl o f) v1 v2 th1 th2 e R
                     (\s. cnj o H s) rho0 /\
          (!s. s IN L /\ aff_dim s = &2 /\ w IN s
               ==> det(jacobian (cnj o H s) (at (vec 0))) =
                   --det(jacobian (H s) (at (vec 0))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `moi_pdg_vs L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2
                   e R H rho0` THEN
    REWRITE_TAC[moi_pdg_vs] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ORTHOGONAL_TRANSFORMATION_COMPOSE THEN
      ASM_REWRITE_TAC[MOI_PDG_REFL_ORTH];
      REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; MOI_PDG_REFL_COMPONENTS;
               VECTOR_NEG_COMPONENT; BASIS_COMPONENT; ARITH] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_pdg_vtri"))
          (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_PDG_VTRI_FLIP THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_PDG_JAC_CNJ_LEFT THEN
    MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let MOI_PDG_VS_POS_EXISTS = prove
 (`!L sigma (h:real^N->real^3) h' w delta U phi k b Q.
      MOI_SMO_CREASE_ORIENT_STATEMENT /\
      simplicial_complex L /\
      smooth_manifold_atlas (subtopology euclidean (UNIONS L)) sigma /\
      homeomorphism (UNIONS L,sphere(vec 0,&1)) (h,h') /\
      (!s. s IN L /\ aff_dim s = &2 ==> moi_smo_cell_smooth s h) /\
      {w} IN L /\ &0 < delta /\
      (!s. s IN L /\ ~(s = {}) ==> ?t. t IN L /\ aff_dim t = &2 /\ s SUBSET t) /\
      (U,phi) IN sigma /\ w IN U /\ phi w = vec 0 /\ &0 < k /\
      (!s. s IN L /\ aff_dim s = &2 /\ w IN s
           ==> moi_smo_cell_smooth s ((Q:(real^N->bool)->real^N->real^2) s) /\
               (!x y. x IN s /\ y IN s /\ Q s x = Q s y ==> x = y) /\
               Q s w = vec 0 /\
               (!x. x IN s ==> &0 <= Im(cexp(--(ii * Cx(b s))) * Q s x)) /\
               (!e. e IN L /\ aff_dim e = &1 /\ w IN e /\ e SUBSET s
                    ==> ?a. !x. x IN e ==> ?t. &0 <= t /\ Q s x = t % a) /\
               (!x. x IN s INTER U ==> phi x = moi_smo_ang k (b s) (Q s x)))
      ==> ?f v1 v2 th1 th2 e R H rho0.
            moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
            (!s. s IN L /\ aff_dim s = &2 /\ w IN s
                 ==> &0 < det(jacobian (H s) (at (vec 0))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^3) w IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (UNIONS L,sphere(vec 0,&1)) (h:real^N->real^3,h')` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `sphere(vec 0:real^3,&1)`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(h:real^N->real^3) w`; `--basis 3:real^3`]
    ORTHOGONAL_TRANSFORMATION_EXISTS_1) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(h:real^N->real^3) w IN sphere(vec 0,&1)` THEN
    SIMP_TAC[IN_SPHERE_0; NORM_NEG; NORM_BASIS; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^3->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `w:real^N`; `delta:real`;
                 `U:real^N->bool`; `phi:real^N->real^2`; `k:real`; `b:(real^N->bool)->real`;
                 `Q:(real^N->bool)->real^N->real^2`; `f0:real^3->real^3`] MOI_PDG_VS_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v1:(real^N->bool)->real^N` (X_CHOOSE_THEN
    `v2:(real^N->bool)->real^N` (X_CHOOSE_THEN `th1:(real^N->bool)->real` (X_CHOOSE_THEN
    `th2:(real^N->bool)->real` (X_CHOOSE_THEN `e:(real^N->bool)->real` (X_CHOOSE_THEN
    `R:(real^N->bool)->complex->real^N` (X_CHOOSE_THEN `H:(real^N->bool)->complex->complex`
    (X_CHOOSE_THEN `rho0:real` ASSUME_TAC)))))))) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `h':real^3->real^N`; `w:real^N`; `delta:real`;
                 `U:real^N->bool`; `phi:real^N->real^2`; `k:real`; `b:(real^N->bool)->real`;
                 `Q:(real^N->bool)->real^N->real^2`; `f0:real^3->real^3`;
                 `v1:(real^N->bool)->real^N`; `v2:(real^N->bool)->real^N`;
                 `th1:(real^N->bool)->real`; `th2:(real^N->bool)->real`;
                 `e:(real^N->bool)->real`; `R:(real^N->bool)->complex->real^N`;
                 `H:(real^N->bool)->complex->complex`; `rho0:real`] MOI_PDG_VS_SIGNS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`f0:real^3->real^3`; `v1:(real^N->bool)->real^N`;
      `v2:(real^N->bool)->real^N`; `th1:(real^N->bool)->real`; `th2:(real^N->bool)->real`;
      `e:(real^N->bool)->real`; `R:(real^N->bool)->complex->real^N`;
      `H:(real^N->bool)->complex->complex`; `rho0:real`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                 `h:real^N->real^3`; `w:real^N`; `delta:real`;
                 `U:real^N->bool`; `phi:real^N->real^2`; `k:real`; `b:(real^N->bool)->real`;
                 `Q:(real^N->bool)->real^N->real^2`; `f0:real^3->real^3`;
                 `v1:(real^N->bool)->real^N`; `v2:(real^N->bool)->real^N`;
                 `th1:(real^N->bool)->real`; `th2:(real^N->bool)->real`;
                 `e:(real^N->bool)->real`; `R:(real^N->bool)->complex->real^N`;
                 `H:(real^N->bool)->complex->complex`; `rho0:real`] MOI_PDG_VS_FLIP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`moi_pdg_refl o (f0:real^3->real^3)`; `v1:(real^N->bool)->real^N`;
      `v2:(real^N->bool)->real^N`; `th1:(real^N->bool)->real`; `th2:(real^N->bool)->real`;
      `e:(real^N->bool)->real`; `R:(real^N->bool)->complex->real^N`;
      `\s. cnj o (H:(real^N->bool)->complex->complex) s`; `rho0:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[REAL_NEG_GT0] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;


(* The radial cutoff, the interpolations of leaf D1 and the vertex map V. *)

let moi_pdg_rstep = new_definition
 `moi_pdg_rstep (r:real) (z:complex) = smooth_step(&2 * norm z / r - &1)`;;

let moi_pdg_mlin = new_definition
 `moi_pdg_mlin (G:complex->complex) (r:real) (y:complex) =
    frechet_derivative G (at (vec 0)) y +
    moi_pdg_rstep r y % (G y - frechet_derivative G (at (vec 0)) y)`;;

let MOI_PDG_RSTEP_0 = prove
 (`!r z. &0 < r /\ norm z <= r / &2 ==> moi_pdg_rstep r z = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_rstep] THEN MATCH_MP_TAC SMOOTH_STEP_0 THEN
  REWRITE_TAC[REAL_ARITH `&2 * x / r - &1 <= &0 <=> x / r <= &1 / &2`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_RSTEP_1 = prove
 (`!r z. &0 < r /\ r <= norm z ==> moi_pdg_rstep r z = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_rstep] THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN
  REWRITE_TAC[REAL_ARITH `&1 <= &2 * x / r - &1 <=> &1 <= x / r`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_RSTEP_BOUNDS = prove
 (`!r z. &0 <= moi_pdg_rstep r z /\ moi_pdg_rstep r z <= &1`,
  REWRITE_TAC[moi_pdg_rstep; SMOOTH_STEP_BOUNDS]);;

let MOI_PDG_RSTEP_SMOOTH = prove
 (`!r. &0 < r ==> smooth_map_on (:complex) (\z. lift(moi_pdg_rstep r z))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_SMOOTH_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `z:complex` THEN ASM_CASES_TAC `z = vec 0:complex` THENL
   [EXISTS_TAC `ball(vec 0:complex,r / &2)` THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_HALF] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `\z:complex. lift(&0)` THEN
    REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST; IN_BALL_0] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PDG_RSTEP_0 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(:complex) DELETE vec 0` THEN
  ASM_SIMP_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV] THEN
  REWRITE_TAC[moi_pdg_rstep] THEN
  MP_TAC(ISPECL [`(:complex) DELETE vec 0`; `\z:complex. lift(&2 * norm z / r - &1)`]
    SMOOTH_MAP_ON_SMOOTH_STEP_COMPOSE) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\z:complex. lift(drop(lift((&2 / r) * drop(lift(norm z)))) - drop(lift(&1)))` THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LIFT_SUB THEN SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
  REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
  MP_TAC(ISPECL [`(:complex) DELETE vec 0`; `&2 / r`; `\z:complex. lift(norm z)`]
    SMOOTH_MAP_ON_LIFT_CMUL) THEN
  REWRITE_TAC[LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN
  MP_TAC(ISPECL [`(:complex) DELETE vec 0`; `\z:complex. z`] SMOOTH_MAP_ON_LIFT_NORM) THEN
  REWRITE_TAC[SMOOTH_MAP_ON_ID; IN_DELETE] THEN SIMP_TAC[OPEN_DELETE; OPEN_UNIV]);;

let MOI_PDG_MLIN_NEAR0 = prove
 (`!G r y. &0 < r /\ norm y <= r / &2
           ==> moi_pdg_mlin G r y = frechet_derivative G (at (vec 0)) y`,
  SIMP_TAC[moi_pdg_mlin; MOI_PDG_RSTEP_0; VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

let MOI_PDG_MLIN_FAR = prove
 (`!G r y. &0 < r /\ r <= norm y ==> moi_pdg_mlin G r y = G y`,
  SIMP_TAC[moi_pdg_mlin; MOI_PDG_RSTEP_1; VECTOR_MUL_LID] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let MOI_PDG_MLIN_SMOOTH = prove
 (`!(G:complex->complex) u r.
      open u /\ smooth_map_on u G /\ G differentiable at (vec 0) /\ &0 < r
      ==> smooth_map_on u (moi_pdg_mlin G r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (G:complex->complex) (at (vec 0)))` ASSUME_TAC
  THENL [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_pdg_mlin (G:complex->complex) r =
                (\y. frechet_derivative G (at (vec 0)) y +
                     drop(lift(moi_pdg_rstep r y)) %
                     (G y - frechet_derivative G (at (vec 0)) y))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_pdg_mlin; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:complex->bool`; `\y:complex. lift(moi_pdg_rstep r y)`;
                 `\y. (G:complex->complex) y - frechet_derivative G (at (vec 0)) y`]
    SMOOTH_MAP_ON_MUL_DROP_OPEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; MOI_PDG_RSTEP_SMOOTH];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[]]);;

let moi_pdg_hext = new_definition
 `moi_pdg_hext (H0:complex->complex) (c:real) (y:complex) =
    (&1 - moi_pdg_rstep c y) % H0 y +
    moi_pdg_rstep c y % frechet_derivative H0 (at (vec 0)) y`;;

let MOI_PDG_HEXT_NEAR = prove
 (`!(H0:complex->complex) e y. &0 < e /\ norm y <= e / &4
     ==> moi_pdg_hext H0 (e / &2) y = H0 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_hext] THEN
  SUBGOAL_THEN `moi_pdg_rstep (e / &2) y = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_PDG_RSTEP_0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

let MOI_PDG_HEXT_SMOOTH = prove
 (`!(H0:complex->complex) e.
      &0 < e /\ smooth_map_on (ball(vec 0,e)) H0 /\ H0 differentiable at (vec 0)
      ==> smooth_map_on (:complex) (moi_pdg_hext H0 (e / &2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (H0:complex->complex) (at (vec 0)))` ASSUME_TAC
  THENL [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_PDG_SMOOTH_LOCAL THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  X_GEN_TAC `z:complex` THEN ASM_CASES_TAC `norm(z:complex) < e` THENL
   [EXISTS_TAC `ball(vec 0:complex,e)` THEN ASM_REWRITE_TAC[OPEN_BALL; IN_BALL_0] THEN
    SUBGOAL_THEN `moi_pdg_hext (H0:complex->complex) (e / &2) =
                  (\y. drop(lift(&1 - moi_pdg_rstep (e / &2) y)) % H0 y +
                       drop(lift(moi_pdg_rstep (e / &2) y)) %
                       frechet_derivative H0 (at (vec 0)) y)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; moi_pdg_hext; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_ADD_OPEN THEN REWRITE_TAC[OPEN_BALL] THEN
    SUBGOAL_THEN `smooth_map_on (ball(vec 0:complex,e)) (\y. lift(moi_pdg_rstep (e / &2) y))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
      REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC MOI_PDG_RSTEP_SMOOTH THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_MUL_DROP_OPEN THEN
    ASM_REWRITE_TAC[OPEN_BALL; ETA_AX] THEN
    TRY(MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[OPEN_BALL] THEN NO_TAC) THEN
    REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
    ASM_REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST];
    ALL_TAC] THEN
  EXISTS_TAC `(:complex) DIFF cball(vec 0,e / &2)` THEN
  REWRITE_TAC[GSYM closed; CLOSED_CBALL; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `frechet_derivative (H0:complex->complex) (at (vec 0))` THEN
  REWRITE_TAC[GSYM closed; CLOSED_CBALL; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN REWRITE_TAC[moi_pdg_hext] THEN
    SUBGOAL_THEN `moi_pdg_rstep (e / &2) y = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_PDG_RSTEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID];
    MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN
    ASM_REWRITE_TAC[GSYM closed; CLOSED_CBALL]]);;

let MOI_PDG_MLIN_DET0 = prove
 (`!(G:complex->complex) r.
      G differentiable at (vec 0) /\ &0 < r
      ==> det(jacobian (moi_pdg_mlin G r) (at (vec 0))) = det(jacobian G (at (vec 0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(frechet_derivative (G:complex->complex) (at (vec 0)))` ASSUME_TAC
  THENL [ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `jacobian (moi_pdg_mlin (G:complex->complex) r) (at (vec 0)) =
                jacobian (frechet_derivative G (at (vec 0))) (at (vec 0))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PDG_JAC_LOCAL_EQ THEN
    EXISTS_TAC `ball(vec 0:complex,r / &2)` THEN
    ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_HALF; DIFFERENTIABLE_LINEAR] THEN
    REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_PDG_MLIN_NEAR0 THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[MOI_PDG_JAC_LINEAR; jacobian]]);;

let MOI_PDG_VS_LIN = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      MOI_SMO_LIN_STATEMENT /\
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      (!s. s IN L /\ aff_dim s = &2 /\ w IN s ==> &0 < det(jacobian (H s) (at (vec 0))))
      ==> ?rho1 r0. &0 < rho1 /\ rho1 <= rho0 /\ &0 < r0 /\
             (!s. s IN L /\ aff_dim s = &2 /\ w IN s ==> rho1 < e s / &4) /\
             !r s y. &0 < r /\ r < r0 /\ s IN L /\ aff_dim s = &2 /\ w IN s /\
                     y IN moi_pdg_dcone b th1 th2 s INTER cball(vec 0,rho1)
                     ==> &0 < det(jacobian (moi_pdg_mlin (H s) r) (at y))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pos"))) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`\s:real^N->bool. (e:(real^N->bool)->real) s / &8`;
                 `{s:real^N->bool | s IN L /\ aff_dim s = &2 /\ w IN s}`]
    MOI_PDG_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `m1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rho1 = min rho0 m1` THEN
  SUBGOAL_THEN `&0 < rho1 /\ rho1 <= rho0 /\
                (!s. s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s ==> rho1 <= e s / &8)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho1" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `m <= x ==> min r m <= x`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. ?r0. s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s
             ==> &0 < r0 /\
                 !r y. &0 < r /\ r < r0 /\
                       y IN moi_pdg_dcone b th1 th2 s INTER cball(vec 0,rho1)
                       ==> &0 < det(jacobian (moi_pdg_mlin
                                     ((H:(real^N->bool)->complex->complex) s) r) (at y))`
  MP_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
    MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `rho1 <= e(s:real^N->bool) / &8` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `G = moi_pdg_hext ((H:(real^N->bool)->complex->complex) s) (e s / &2)` THEN
    SUBGOAL_THEN `!y. y IN ball(vec 0,e(s:real^N->bool) / &4)
                      ==> (G:complex->complex) y = H s y` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN REPEAT STRIP_TAC THEN EXPAND_TAC "G" THEN
      MATCH_MP_TAC MOI_PDG_HEXT_NEAR THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `smooth_map_on (:complex) (G:complex->complex)` ASSUME_TAC THENL
     [EXPAND_TAC "G" THEN MATCH_MP_TAC MOI_PDG_HEXT_SMOOTH THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `frechet_derivative (G:complex->complex) (at (vec 0)) =
                  frechet_derivative ((H:(real^N->bool)->complex->complex) s) (at (vec 0))`
    ASSUME_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
      MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
      MAP_EVERY EXISTS_TAC [`(H:(real^N->bool)->complex->complex) s`;
                            `e(s:real^N->bool) / &4`] THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_BALL; DIST_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN `!r y. y IN ball(vec 0,e(s:real^N->bool) / &4)
                        ==> moi_pdg_mlin (G:complex->complex) r y =
                            moi_pdg_mlin ((H:(real^N->bool)->complex->complex) s) r y`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_mlin] THEN
      SIMP_TAC[ASSUME `!y. y IN ball(vec 0,e(s:real^N->bool) / &4)
                           ==> (G:complex->complex) y = H s y`;
               ASSUME `frechet_derivative (G:complex->complex) (at (vec 0)) =
                       frechet_derivative ((H:(real^N->bool)->complex->complex) s) (at (vec 0))`;
               ASSUME `(y:complex) IN ball(vec 0,e(s:real^N->bool) / &4)`];
      ALL_TAC] THEN
    SUBGOAL_THEN `!x. x IN moi_pdg_dcone b th1 th2 (s:real^N->bool) INTER cball(vec 0,rho1)
                      ==> x IN ball(vec 0,e s / &4) /\
                          x IN ball(vec 0,e s) INTER
                               moi_pdg_cone2 (cexp(ii * Cx(b s + th1 s)))
                                             (cexp(ii * Cx(b s + th2 s)))`
    (LABEL_TAC "inS") THENL
     [X_GEN_TAC `x:complex` THEN REWRITE_TAC[IN_INTER; IN_CBALL_0; IN_BALL_0; moi_pdg_dcone] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `closed(moi_pdg_dcone b th1 th2 (s:real^N->bool)) /\
                  convex(moi_pdg_dcone b th1 th2 s) /\ conic(moi_pdg_dcone b th1 th2 s) /\
                  (G:complex->complex)(vec 0) = vec 0 /\
                  (!x. x IN moi_pdg_dcone b th1 th2 s INTER cball(vec 0,rho1)
                       ==> ~(det(jacobian G (at x)) = &0))` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[moi_pdg_dcone; MOI_PDG_CONE2_CONVEX; MOI_PDG_CONE2_CONIC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_PDG_CONE2_CLOSED THEN REWRITE_TAC[MOI_PDG_IM_CNJ_UNIT] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN MATCH_MP_TAC SIN_POS_PI THEN
        ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `(G:complex->complex)(vec 0) = (H:(real^N->bool)->complex->complex) s (vec 0)` SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `G:complex->complex`)) (concl th) &&
            not(can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_pdg_mlin"))
                  (concl th)))) THEN
          REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]];
        X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
        USE_THEN "inS" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
          (REWRITE_RULE[GSYM moi_pdg_dcone] (ASSUME `x IN moi_pdg_cone2
             (cexp(ii * Cx(b(s:real^N->bool) + th1 s))) (cexp(ii * Cx(b s + th2 s))) INTER
             cball(vec 0,rho1)`)))) THEN
        SUBGOAL_THEN `jacobian ((H:(real^N->bool)->complex->complex) s) (at x) =
                      jacobian G (at x)` (SUBST1_TAC o SYM) THENL
         [MATCH_MP_TAC MOI_PDG_JAC_LOCAL_EQ THEN
          EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool) / &4)` THEN
          ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
           [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
            ASM_REWRITE_TAC[];
            MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
            EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN
            ASM_REWRITE_TAC[OPEN_BALL] THEN
            MP_TAC(ASSUME `(x:complex) IN ball(vec 0,e(s:real^N->bool)) INTER
                 moi_pdg_cone2 (cexp(ii * Cx(b s + th1 s))) (cexp(ii * Cx(b s + th2 s)))`) THEN
          SIMP_TAC[IN_INTER]];
          ALL_TAC] THEN
        MATCH_MP_TAC MOI_PDG_DET_NZ_INJ THEN CONJ_TAC THENL
         [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
          EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN
          ASM_REWRITE_TAC[OPEN_BALL] THEN
          MP_TAC(ASSUME `(x:complex) IN ball(vec 0,e(s:real^N->bool)) INTER
                 moi_pdg_cone2 (cexp(ii * Cx(b s + th1 s))) (cexp(ii * Cx(b s + th2 s)))`) THEN
          SIMP_TAC[IN_INTER];
          FIRST_X_ASSUM(MP_TAC o SPEC `x:complex` o check (fun th ->
            can (find_term ((=) `moi_pdg_st`)) (concl th) && is_forall(concl th))) THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[]]];
      ALL_TAC] THEN
    UNDISCH_TAC `MOI_SMO_LIN_STATEMENT` THEN REWRITE_TAC[MOI_SMO_LIN_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`G:complex->complex`; `(:complex)`;
                               `moi_pdg_dcone b th1 th2 (s:real^N->bool)`; `rho1:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV]; ALL_TAC] THEN
    SUBGOAL_THEN `!r. (\y. frechet_derivative (G:complex->complex) (at (vec 0)) y +
                          smooth_step(&2 * norm y / r - &1) %
                          (G y - frechet_derivative G (at (vec 0)) y)) =
                      moi_pdg_mlin G r` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; moi_pdg_mlin; moi_pdg_rstep]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`r:real`; `y:complex`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `smooth_map_on (ball(vec 0,e(s:real^N->bool)))
                    (moi_pdg_mlin ((H:(real^N->bool)->complex->complex) s) r)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_PDG_MLIN_SMOOTH THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
    SUBGOAL_THEN `!x. x IN moi_pdg_dcone b th1 th2 (s:real^N->bool) INTER cball(vec 0,rho1)
                      ==> ~(det(jacobian (moi_pdg_mlin
                              ((H:(real^N->bool)->complex->complex) s) r) (at x)) = &0)`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
      USE_THEN "inS" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `x IN moi_pdg_dcone b th1 th2 (s:real^N->bool) INTER cball(vec 0,rho1)`))) THEN
      SUBGOAL_THEN `jacobian (moi_pdg_mlin ((H:(real^N->bool)->complex->complex) s) r) (at x) =
                    jacobian (moi_pdg_mlin G r) (at x)` SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_PDG_JAC_LOCAL_EQ THEN
        EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool) / &4)` THEN
        ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
         [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
          EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN
          ASM_REWRITE_TAC[OPEN_BALL] THEN
          MP_TAC(ASSUME `(x:complex) IN ball(vec 0,e(s:real^N->bool)) INTER
                 moi_pdg_cone2 (cexp(ii * Cx(b s + th1 s))) (cexp(ii * Cx(b s + th2 s)))`) THEN
          SIMP_TAC[IN_INTER]];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`moi_pdg_dcone b th1 th2 (s:real^N->bool) INTER cball(vec 0,rho1)`;
                   `\x. det(jacobian (moi_pdg_mlin
                          ((H:(real^N->bool)->complex->complex) s) r) (at x))`;
                   `y:complex`; `vec 0:complex`] MOI_PDG_SIGN_CONST) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        ASM_REWRITE_TAC[CONVEX_CBALL];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_PDG_JAC_DET_CONT THEN ASM_REWRITE_TAC[OPEN_BALL];
          REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
          USE_THEN "inS" (fun th -> MP_TAC(MATCH_MP th
            (ASSUME `x IN moi_pdg_dcone b th1 th2 (s:real^N->bool) INTER
                     cball(vec 0,rho1)`))) THEN
          SET_TAC[]];
        REWRITE_TAC[IN_INTER; CENTRE_IN_CBALL; moi_pdg_dcone; moi_pdg_cone2; IN_ELIM_THM] THEN
        CONJ_TAC THENL
         [MAP_EVERY EXISTS_TAC [`&0`; `&0`] THEN
          REWRITE_TAC[REAL_LE_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID];
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SIMP_TAC[MOI_PDG_MLIN_DET0;
             ASSUME `(H:(real^N->bool)->complex->complex) s differentiable at (vec 0)`;
             ASSUME `&0 < r`] THEN
    USE_THEN "pos" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(s:real^N->bool) IN L`) (CONJ (ASSUME `aff_dim(s:real^N->bool) = &2`)
            (ASSUME `(w:real^N) IN s`))))) THEN
    REWRITE_TAC[IMP_IMP; REAL_MUL_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0f:(real^N->bool)->real` (LABEL_TAC "r0f")) THEN
  MP_TAC(ISPECL [`r0f:(real^N->bool)->real`;
                 `{s:real^N->bool | s IN L /\ aff_dim s = &2 /\ w IN s}`]
    MOI_PDG_FINITE_POS_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "r0f" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `s IN L /\ aff_dim s = &2 /\ (w:real^N) IN s`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`rho1:real`; `r0:real`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &8 ==> x < e / &4`) THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`r:real`; `s:real^N->bool`; `y:complex`] THEN STRIP_TAC THEN
    USE_THEN "r0f" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(s:real^N->bool) IN L`) (CONJ (ASSUME `aff_dim(s:real^N->bool) = &2`)
            (ASSUME `(w:real^N) IN s`))))) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_PDG_SEC_IS_CONE2 = prove
 (`!k a t1 t2. &0 < k /\ t1 < t2 /\ k * (t2 - t1) < pi
     ==> moi_pdg_sec k a t1 t2 =
         moi_pdg_cone2 (cexp(ii * Cx(k * (a + t1)))) (cexp(ii * Cx(k * (a + t2))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `z:complex` THEN
  ASM_SIMP_TAC[MOI_PDG_CONE2_KPOLAR] THEN REWRITE_TAC[moi_pdg_sec; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MOI_PDG_SEC_MONO = prove
 (`!k a t1 t2 t1' t2'. t1 <= t1' /\ t2' <= t2
     ==> moi_pdg_sec k a t1' t2' SUBSET moi_pdg_sec k a t1 t2`,
  REWRITE_TAC[SUBSET; moi_pdg_sec; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `t:real`] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_GMAP_ANGF = prove
 (`!k b th1 th2 (s:real^N->bool) z.
      ~(z = Cx(&0))
      ==> moi_pdg_gmap k b th1 th2 s z =
          moi_pdg_angf (inv k) (k * (b s + (th1 s + th2 s) / &2)) z`,
  SIMP_TAC[moi_pdg_gmap; moi_pdg_angz]);;

let MOI_PDG_VS_HALF_EXT = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 s t1 t2.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      (!s. s IN L /\ aff_dim s = &2 /\ w IN s ==> &0 < det(jacobian (H s) (at (vec 0)))) /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\ th1 s <= t1 /\ t2 <= th2 s
      ==> ?u g. open u /\ moi_pdg_sec k (b s) t1 t2 DIFF {vec 0} SUBSET u /\
                smooth_map_on u g /\
                (!x. x IN moi_pdg_sec k (b s) t1 t2
                     ==> g x = moi_pdg_pmap L w k b th1 th2 H x) /\
                (!x. x IN moi_pdg_sec k (b s) t1 t2 DIFF {vec 0}
                     ==> &0 < det(jacobian g (at x)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pos") STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_pdg_sec k (b s) t1 t2 SUBSET moi_pdg_ssec k b th1 th2 (s:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_pdg_ssec] THEN MATCH_MP_TAC MOI_PDG_SEC_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Os = {z:complex | Im(cexp(--(ii * Cx(k * (b(s:real^N->bool) +
                                    (th1 s + th2 s) / &2)))) * z) = &0
                                ==> &0 < Re(cexp(--(ii * Cx(k * (b s +
                                    (th1 s + th2 s) / &2)))) * z)}` THEN
  SUBGOAL_THEN `open(Os:complex->bool) /\ ~(Cx(&0) IN Os)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Os" THEN REWRITE_TAC[MOI_PDG_SLIT_OPEN_C; IN_ELIM_THM] THEN
    REWRITE_TAC[COMPLEX_MUL_RZERO; RE_CX; IM_CX; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN moi_pdg_ssec k b th1 th2 (s:real^N->bool) /\ ~(z = Cx(&0))
                    ==> z IN Os` ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN STRIP_TAC THEN EXPAND_TAC "Os" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`k:real`; `b(s:real^N->bool):real`; `th1(s:real^N->bool):real`;
                   `th2(s:real^N->bool):real`; `z:complex`] MOI_PDG_SEC_SLIT) THEN
    REWRITE_TAC[GSYM moi_pdg_ssec] THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on Os (moi_pdg_angf (inv k)
                  (k * (b(s:real^N->bool) + (th1 s + th2 s) / &2)))` ASSUME_TAC THENL
   [EXPAND_TAC "Os" THEN MATCH_MP_TAC MOI_PDG_ANGF_SMOOTH THEN
    REWRITE_TAC[MOI_PDG_SLIT_OPEN_C; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN Os ==> moi_pdg_gmap k b th1 th2 (s:real^N->bool) z =
                  moi_pdg_angf (inv k) (k * (b s + (th1 s + th2 s) / &2)) z` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_GMAP_ANGF THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on Os (moi_pdg_gmap k b th1 th2 (s:real^N->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `moi_pdg_angf (inv k) (k * (b(s:real^N->bool) + (th1 s + th2 s) / &2))` THEN
    SIMP_TAC[ASSUME `!z. z IN Os ==> moi_pdg_gmap k b th1 th2 (s:real^N->bool) z =
                  moi_pdg_angf (inv k) (k * (b s + (th1 s + th2 s) / &2)) z`;
             ASSUME `open(Os:complex->bool)`; ASSUME `smooth_map_on Os (moi_pdg_angf (inv k)
                  (k * (b(s:real^N->bool) + (th1 s + th2 s) / &2)))`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN Os ==> det(jacobian (moi_pdg_gmap k b th1 th2 (s:real^N->bool))
                                    (at z)) = inv k` ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `jacobian (moi_pdg_gmap k b th1 th2 (s:real^N->bool)) (at z) =
                  jacobian (moi_pdg_angf (inv k) (k * (b s + (th1 s + th2 s) / &2))) (at z)`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PDG_JAC_LOCAL_EQ THEN
      EXISTS_TAC `Os:complex->bool` THEN
      SIMP_TAC[ASSUME `!z. z IN Os ==> moi_pdg_gmap k b th1 th2 (s:real^N->bool) z =
                  moi_pdg_angf (inv k) (k * (b s + (th1 s + th2 s) / &2)) z`;
               ASSUME `open(Os:complex->bool)`; ASSUME `(z:complex) IN Os`] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `Os:complex->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_PDG_ANGF_DET THEN UNDISCH_TAC `(z:complex) IN Os` THEN
      EXPAND_TAC "Os" THEN REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  ABBREV_TAC `Ls = frechet_derivative ((H:(real^N->bool)->complex->complex) s) (at (vec 0))` THEN
  SUBGOAL_THEN `linear (Ls:complex->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "Ls" THEN ASM_SIMP_TAC[LINEAR_FRECHET_DERIVATIVE]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Os:complex->bool`;
                        `(Ls:complex->complex) o moi_pdg_gmap k b th1 th2 (s:real^N->bool)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_SING] THEN X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Os:complex->bool`)) (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_pdg_ssec")) (concl th))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ASSUME
      `moi_pdg_sec k (b s) t1 t2 SUBSET moi_pdg_ssec k b th1 th2 (s:real^N->bool)`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0]];
    MATCH_MP_TAC SMOOTH_MAP_ON_LINEAR_O THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN EXPAND_TAC "Ls" THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_EQ) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ASSUME
      `moi_pdg_sec k (b s) t1 t2 SUBSET moi_pdg_ssec k b th1 th2 (s:real^N->bool)`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `x:complex` THEN REWRITE_TAC[IN_DIFF; IN_SING] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:complex) IN Os` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Os:complex->bool`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_pdg_ssec")) (concl th))) THEN
      ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ASSUME
      `moi_pdg_sec k (b s) t1 t2 SUBSET moi_pdg_ssec k b th1 th2 (s:real^N->bool)`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_pdg_gmap k b th1 th2 (s:real^N->bool) differentiable at x` ASSUME_TAC
    THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `Os:complex->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_PDG_DET_CHAIN; DIFFERENTIABLE_LINEAR; MOI_PDG_JAC_LINEAR] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [EXPAND_TAC "Ls" THEN REWRITE_TAC[GSYM jacobian] THEN USE_THEN "pos" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LT_INV]]]);;

let MOI_PDG_HALF_INDEX = prove
 (`!q. (2 * q) DIV 2 = q /\ (2 * q + 1) DIV 2 = q /\ EVEN(2 * q) /\ ~EVEN(2 * q + 1)`,
  GEN_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC;
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `1` THEN ARITH_TAC;
    REWRITE_TAC[EVEN_DOUBLE];
    REWRITE_TAC[EVEN_ADD; EVEN_DOUBLE; ARITH]]);;

let MOI_PDG_VS_D2 = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 R2.
      MOI_SMO_VERTEX_DEGREE_STATEMENT /\ MOI_SMO_VERTEX2_STATEMENT /\
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      (!s. s IN L /\ aff_dim s = &2 /\ w IN s ==> &0 < det(jacobian (H s) (at (vec 0)))) /\
      &0 < R2
      ==> ?P' R1. &0 < R1 /\ R1 < R2 /\ P' continuous_on (:complex) /\
                  (!x. R2 <= norm x ==> P' x = moi_pdg_pmap L w k b th1 th2 H x) /\
                  (?u. open u /\ cball(vec 0,R1) SUBSET u /\ smooth_map_on u P' /\
                       !x. x IN u ==> &0 < det(jacobian P' (at x))) /\
                  (!s t1 t2. s IN L /\ aff_dim s = &2 /\ w IN s /\
                             ((t1 = th1 s /\ t2 = (th1 s + th2 s) / &2) \/
                              (t1 = (th1 s + th2 s) / &2 /\ t2 = th2 s))
                             ==> ?u g. open u /\
                                       {x | x IN moi_pdg_sec k (b s) t1 t2 /\
                                            R1 / &2 <= norm x} SUBSET u /\
                                       smooth_map_on u g /\
                                       (!x. x IN moi_pdg_sec k (b s) t1 t2 /\
                                            R1 / &2 <= norm x ==> g x = P' x) /\
                                       (!x. x IN u /\ norm x < R1 ==> g x = P' x) /\
                                       (!x. x IN moi_pdg_sec k (b s) t1 t2 /\
                                            R1 / &2 <= norm x
                                            ==> &0 < det(jacobian g (at x))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pos") ASSUME_TAC)))) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ABBREV_TAC `TT = {s:real^N->bool | s IN L /\ aff_dim s = &2 /\ w IN s}` THEN
  MP_TAC(ISPEC `TT:(real^N->bool)->bool` FINITE_INDEX_NUMSEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fi:num->real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `tri = \i. (fi:num->real^N->bool) (i DIV 2 + 1)` THEN
  ABBREV_TAC `lo = \i. if EVEN i then (th1:(real^N->bool)->real) (tri i)
                     else (th1 (tri i) + th2 (tri i)) / &2` THEN
  ABBREV_TAC `hi = \i. if EVEN i then ((th1:(real^N->bool)->real) (tri i) + th2 (tri i)) / &2
                     else th2 (tri i)` THEN
  ABBREV_TAC `SS = \i. moi_pdg_sec k ((b:(real^N->bool)->real) ((tri:num->real^N->bool) i))
                                      ((lo:num->real) i) ((hi:num->real) i)` THEN
  ABBREV_TAC `n = 2 * CARD(TT:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `!i. i < n ==> (tri:num->real^N->bool) i IN TT` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EXPAND_TAC "tri" THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `TT:(real^N->bool)->bool`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_NUMSEG] THEN
    UNDISCH_TAC `i:num < n` THEN EXPAND_TAC "n" THEN
    MP_TAC(SPECL [`i:num`; `2`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n ==> (lo:num->real) i < (hi:num->real) i /\
                  (th1:(real^N->bool)->real) ((tri:num->real^N->bool) i) <= lo i /\
                  hi i <= (th2:(real^N->bool)->real) (tri i) /\ k * (hi i - lo i) < pi`
  (LABEL_TAC "lohi") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(tri:num->real^N->bool) i IN TT` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "TT" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(INST [`(tri:num->real^N->bool) i`,`s:real^N->bool`] (SPEC_ALL MOI_PDG_VS_TRI)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["lo"; "hi"] THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t1 t2. s IN TT /\
              ((t1 = (th1:(real^N->bool)->real) s /\ t2 = (th1 s + th2 s) / &2) \/
               (t1 = (th1 s + th2 s) / &2 /\ t2 = th2 s))
              ==> ?i. i < n /\ (SS:num->complex->bool) i = moi_pdg_sec k (b s) t1 t2`
  (LABEL_TAC "idx") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `(s:real^N->bool) IN TT` THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `TT:(real^N->bool)->bool`
                          then GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th] else NO_TAC) THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `2 * (j - 1)`; EXISTS_TAC `2 * (j - 1) + 1`] THEN
    (CONJ_TAC THENL [EXPAND_TAC "n" THEN ASM_ARITH_TAC; ALL_TAC]) THEN
    MAP_EVERY EXPAND_TAC ["SS"; "lo"; "hi"; "tri"] THEN
    REWRITE_TAC[MOI_PDG_HALF_INDEX] THEN
    (SUBGOAL_THEN `j - 1 + 1 = j` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {(SS:num->complex->bool) i | i < n} = (:complex)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:complex` THEN
    MP_TAC(INST [`z:complex`,`z:complex`] (SPEC_ALL MOI_PDG_VS_COVER_ALL)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `z IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` THEN
    REWRITE_TAC[moi_pdg_ssec; moi_pdg_sec; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(s:real^N->bool) IN TT` ASSUME_TAC THENL
     [EXPAND_TAC "TT" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ASM_CASES_TAC `t <= ((th1:(real^N->bool)->real) s + th2 s) / &2` THENL
     [SUBGOAL_THEN `?i. i < n /\ (SS:num->complex->bool) i =
                       moi_pdg_sec k (b(s:real^N->bool)) (th1 s) ((th1 s + th2 s) / &2)`
      MP_TAC THENL [USE_THEN "idx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC];
      SUBGOAL_THEN `?i. i < n /\ (SS:num->complex->bool) i =
                       moi_pdg_sec k (b(s:real^N->bool)) ((th1 s + th2 s) / &2) (th2 s)`
      MP_TAC THENL [USE_THEN "idx" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(SS:num->complex->bool) i` THEN
    (CONJ_TAC THENL
      [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
       ASM_REWRITE_TAC[moi_pdg_sec; IN_ELIM_THM] THEN
       MAP_EVERY EXISTS_TAC [`r:real`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  UNDISCH_TAC `MOI_SMO_VERTEX2_STATEMENT` THEN REWRITE_TAC[MOI_SMO_VERTEX2_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`moi_pdg_pmap L w k b th1 th2 (H:(real^N->bool)->complex->complex)`;
                             `SS:num->complex->bool`; `n:num`; `R2:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_CONT) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[COMPLEX_CMUL] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_HOMOG) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_INJ) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "lohi" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `i:num < n`))) THEN
      SUBGOAL_THEN `&0 < k` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "SS" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_PDG_SEC_IS_CONE2] THEN
      REWRITE_TAC[MOI_PDG_CONE2_CONVEX; MOI_PDG_CONE2_CONIC] THEN
      MATCH_MP_TAC MOI_PDG_CONE2_CLOSED THEN REWRITE_TAC[MOI_PDG_IM_CNJ_UNIT] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN MATCH_MP_TAC SIN_POS_PI THEN
      REWRITE_TAC[REAL_ARITH `k * (a + t2) - k * (a + t1) = k * (t2 - t1)`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "lohi" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `i:num < n`))) THEN
      SUBGOAL_THEN `(tri:num->real^N->bool) i IN TT` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "TT" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      EXPAND_TAC "SS" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(INST [`(tri:num->real^N->bool) i`,`s:real^N->bool`;
                         `(lo:num->real) i`,`t1:real`; `(hi:num->real) i`,`t2:real`]
        (SPEC_ALL MOI_PDG_VS_HALF_EXT)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P':complex->complex` (X_CHOOSE_THEN `R1:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`P':complex->complex`; `R1:real`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t1:real`; `t2:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?i. i < n /\ (SS:num->complex->bool) i = moi_pdg_sec k (b(s:real^N->bool)) t1 t2`
  (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
   [USE_THEN "idx" MATCH_MP_TAC THEN EXPAND_TAC "TT" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `R1:real`)) (concl th) &&
    can (find_term ((=) `SS:num->complex->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;


(* The final map V = P' + rstep r (F - P), its regions, the sector/half/inner cores
   and the ray lemmas used for the clauses of moi_pdg_vp. *)

(* The final vertex data (moi_pdg_fs) and the clauses of moi_pdg_vp. *)

let moi_pdg_vmap = new_definition
 `moi_pdg_vmap (P':complex->complex) (r:real) (Fm:complex->complex) (Pm:complex->complex)
               (z:complex) =
    P' z + moi_pdg_rstep r z % (Fm z - Pm z)`;;

let moi_pdg_uedge = new_definition
 `moi_pdg_uedge (U:real^N->bool) (phi:real^N->real^2) (rho:real) (E:real^N->bool) =
    @u:complex. norm u = &1 /\
                (!t. &0 <= t /\ t < rho ==> chart_inv(U,phi) (Cx t * u) IN E) /\
                (!x. x IN E /\ x IN U /\ norm(phi x) < rho
                     ==> ?t. &0 <= t /\ phi x = Cx t * u)`;;

let moi_pdg_uart = new_definition
 `moi_pdg_uart (k:real) (b:(real^N->bool)->real) (th1:(real^N->bool)->real)
               (th2:(real^N->bool)->real) (s:real^N->bool) =
    cexp(ii * Cx(k * (b s + (th1 s + th2 s) / &2)))`;;

let moi_pdg_fs = new_definition
 `moi_pdg_fs (L:(real^N->bool)->bool) (sigma:((real^N->bool)#(real^N->real^2))->bool)
             (h:real^N->real^3) (w:real^N) (delta:real)
             (U:real^N->bool) (phi:real^N->real^2) (k:real) (b:(real^N->bool)->real)
             (Q:(real^N->bool)->real^N->real^2) (f:real^3->real^3)
             (v1:(real^N->bool)->real^N) (v2:(real^N->bool)->real^N)
             (th1:(real^N->bool)->real) (th2:(real^N->bool)->real)
             (e:(real^N->bool)->real) (R:(real^N->bool)->complex->real^N)
             (H:(real^N->bool)->complex->complex) (rho0:real)
             (rho:real) (r:real) (R1:real) (P':complex->complex) <=>
    moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
    (!s. s IN L /\ aff_dim s = &2 /\ w IN s ==> &0 < det(jacobian (H s) (at (vec 0)))) /\
    &0 < rho /\ rho <= rho0 /\ (!s. s IN L /\ aff_dim s = &2 /\ w IN s ==> rho < e s / &4) /\
    &0 < r /\ r <= rho / &2 /\
    (!s y. s IN L /\ aff_dim s = &2 /\ w IN s /\
           y IN moi_pdg_dcone b th1 th2 s INTER cball(vec 0,rho)
           ==> &0 < det(jacobian (moi_pdg_mlin (H s) r) (at y))) /\
    &0 < R1 /\ R1 < r / &4 /\ P' continuous_on (:complex) /\
    (!x. r / &4 <= norm x ==> P' x = moi_pdg_pmap L w k b th1 th2 H x) /\
    (?u. open u /\ cball(vec 0,R1) SUBSET u /\ smooth_map_on u P' /\
         !x. x IN u ==> &0 < det(jacobian P' (at x))) /\
    (!s t1 t2. s IN L /\ aff_dim s = &2 /\ w IN s /\
               ((t1 = th1 s /\ t2 = (th1 s + th2 s) / &2) \/
                (t1 = (th1 s + th2 s) / &2 /\ t2 = th2 s))
               ==> ?u g. open u /\
                         {x | x IN moi_pdg_sec k (b s) t1 t2 /\ R1 / &2 <= norm x} SUBSET u /\
                         smooth_map_on u g /\
                         (!x. x IN moi_pdg_sec k (b s) t1 t2 /\ R1 / &2 <= norm x
                              ==> g x = P' x) /\
                         (!x. x IN u /\ norm x < R1 ==> g x = P' x) /\
                         (!x. x IN moi_pdg_sec k (b s) t1 t2 /\ R1 / &2 <= norm x
                              ==> &0 < det(jacobian g (at x))))`;;

(* Generic facts on the final map and on rotations of balls. *)

let MOI_PDG_VMAP_INNER = prove
 (`!(P':complex->complex) r Fm Pm z. &0 < r /\ norm z <= r / &2
       ==> moi_pdg_vmap P' r Fm Pm z = P' z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_vmap] THEN
  ASM_SIMP_TAC[MOI_PDG_RSTEP_0; VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

let MOI_PDG_VMAP_FAR = prove
 (`!(P':complex->complex) r Fm Pm z. &0 < r /\ r <= norm z /\ P' z = Pm z
       ==> moi_pdg_vmap P' r Fm Pm z = Fm z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_pdg_vmap] THEN
  ASM_SIMP_TAC[MOI_PDG_RSTEP_1; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC);;

let MOI_PDG_VMAP_CONT = prove
 (`!(P':complex->complex) r Fm Pm s.
       P' continuous_on s /\ &0 < r /\ Fm continuous_on s /\ Pm continuous_on s
       ==> moi_pdg_vmap P' r Fm Pm continuous_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_pdg_vmap P' r Fm Pm =
                (\z. (P':complex->complex) z + moi_pdg_rstep r z % (Fm z - Pm z))`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_pdg_vmap]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_SUB; ETA_AX] THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `(:complex)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_SIMP_TAC[MOI_PDG_RSTEP_SMOOTH]);;

let MOI_PDG_ROT_NORM = prove
 (`!v x:complex. norm v = &1 ==> norm(v * x) = norm x`,
  SIMP_TAC[COMPLEX_NORM_MUL; REAL_MUL_LID]);;

let MOI_PDG_ROT_BALL = prove
 (`!v t0 d x:complex. norm v = &1 /\ x IN ball(t0,d) ==> v * x IN ball(v * t0,d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL; dist; GSYM COMPLEX_SUB_LDISTRIB] THEN
  SIMP_TAC[COMPLEX_NORM_MUL; REAL_MUL_LID]);;

let MOI_PDG_ROT_INV = prove
 (`!v y:complex. norm v = &1 ==> v * (cnj v * y) = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_MUL_ASSOC; COMPLEX_MUL_CNJ] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_MUL_LID]);;

let MOI_PDG_ROT_SMOOTH = prove
 (`!v s t (A:complex->complex).
       open s /\ open t /\ (!x. x IN s ==> v * x IN t) /\ smooth_map_on t A
       ==> smooth_map_on s (A o (\x. v * x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `t:complex->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC MOI_PDG_SMOOTH_LINEAR THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONJ_TAC THEN SIMPLE_COMPLEX_ARITH_TAC]);;

let MOI_PDG_BALL_RE_IM = prove
 (`!t0 eta x. x IN ball(Cx t0,eta) ==> abs(Re x - t0) < eta /\ abs(Im x) < eta`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL; dist] THEN
  MP_TAC(SPEC `Cx t0 - x` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB; IM_SUB; RE_CX; IM_CX] THEN REAL_ARITH_TAC);;

let MOI_PDG_UPBALL = prove
 (`!k a t1 t2 t t0. &0 < k /\ t1 <= t /\ t < t2 /\ &0 < t0
     ==> ?eta. &0 < eta /\
               !x. x IN ball(Cx t0,eta) /\ &0 <= Im x
                   ==> cexp(ii * Cx(k * (a + t))) * x IN moi_pdg_sec k a t1 t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:real`; `a:real`; `t1:real`; `t2:real`; `t:real`; `t0:real`]
    MOI_PDG_UPBOX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:complex` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_PDG_BALL_RE_IM) THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_LOWBALL = prove
 (`!k a t1 t2 t t0. &0 < k /\ t1 < t /\ t <= t2 /\ &0 < t0
     ==> ?eta. &0 < eta /\
               !x. x IN ball(Cx t0,eta) /\ Im x <= &0
                   ==> cexp(ii * Cx(k * (a + t))) * x IN moi_pdg_sec k a t1 t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:real`; `a:real`; `t1:real`; `t2:real`; `t:real`; `t0:real`]
    MOI_PDG_LOWBOX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:complex` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_PDG_BALL_RE_IM) THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_SECBALL = prove
 (`!k a t1 t2 t t0. &0 < k /\ t1 < t /\ t < t2 /\ &0 < t0
     ==> ?eta. &0 < eta /\
               !x. x IN ball(Cx t0,eta)
                   ==> cexp(ii * Cx(k * (a + t))) * x IN moi_pdg_sec k a t1 t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:real`; `a:real`; `t1:real`; `t2:real`; `t:real`; `t0:real`]
    MOI_PDG_UPBALL) THEN
  MP_TAC(SPECL [`k:real`; `a:real`; `t1:real`; `t2:real`; `t:real`; `t0:real`]
    MOI_PDG_LOWBALL) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `eta2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min eta1 eta2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `x:complex` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= Im x` THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `x:complex` o check (fun th ->
      can (find_term ((=) `eta2:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL];
    FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `x:complex` o check (fun th ->
      can (find_term ((=) `eta1:real`)) (concl th) && is_forall (concl th))) THEN
    ASM_REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_POS_NBHD = prove
 (`!s (g:complex->complex) x.
       open s /\ smooth_map_on s g /\ x IN s /\ &0 < det(jacobian g (at x))
       ==> ?d. &0 < d /\ ball(x,d) SUBSET s /\
               !y. y IN ball(x,d) ==> &0 < det(jacobian g (at y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:complex->bool`; `g:complex->complex`] MOI_PDG_JAC_DET_CONT) THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT] THEN
  DISCH_THEN(MP_TAC o SPEC `x:complex`) THEN ASM_REWRITE_TAC[continuous_at] THEN
  DISCH_THEN(MP_TAC o SPEC `det(jacobian (g:complex->complex) (at x))`) THEN
  ASM_REWRITE_TAC[DIST_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `x:complex` (REWRITE_RULE[OPEN_CONTAINS_BALL]
    (ASSUME `open(s:complex->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:complex,d2)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL] THEN REAL_ARITH_TAC;
    X_GEN_TAC `y:complex` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:complex`) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Basic consequences of the final setting moi_pdg_fs. *)

let MOI_PDG_FS_VS = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'
      ==> moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
          &0 < k /\ &0 < rho0 /\ &0 < rho /\ rho <= rho0 /\ &0 < r /\ r <= rho / &2 /\
          &0 < R1 /\ R1 < r / &4`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_fs] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_FS_TRI = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' s.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      s IN L /\ aff_dim s = &2 /\ w IN s
      ==> &0 < k /\ th1 s < th2 s /\ k * (th2 s - th1 s) < &2 * pi /\ &0 < e s /\
          rho < e s / &4 /\ smooth_map_on (ball(vec 0,e s)) (H s) /\
          H s differentiable at (vec 0) /\
          &0 < rho /\ &0 < r /\ r <= rho / &2 /\ &0 < R1 /\ R1 < r / &4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  UNDISCH_TAC `moi_pdg_fs L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H
                 rho0 rho r R1 P'` THEN
  REWRITE_TAC[moi_pdg_fs] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN MP_TAC(SPEC_ALL MOI_PDG_VS_H0) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_PDG_FS_OUTER = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' s z.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\
      z IN moi_pdg_ssec k b th1 th2 s /\ r / &4 <= norm z /\ norm z <= rho
      ==> moi_pdg_vmap P' r (moi_pdg_fmap U phi f h) (moi_pdg_pmap L w k b th1 th2 H) z =
          moi_pdg_mlin (H s) r (moi_pdg_gmap k b th1 th2 s z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_FS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_pdg_fs L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H
                 rho0 rho r R1 P'` THEN
  REWRITE_TAC[moi_pdg_fs] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_SEC_CHART) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_PMAP_EQ) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(P':complex->complex) z =
                moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H z` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_pdg_vmap; moi_pdg_mlin; moi_pdg_fmap] THEN
  SUBGOAL_THEN `moi_pdg_rstep r (moi_pdg_gmap k b th1 th2 (s:real^N->bool) z) =
                moi_pdg_rstep r z` SUBST1_TAC THENL
   [REWRITE_TAC[moi_pdg_rstep] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_FS_CONT = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'
      ==> moi_pdg_vmap P' r (moi_pdg_fmap U phi f h) (moi_pdg_pmap L w k b th1 th2 H)
            continuous_on cball(vec 0,rho)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  UNDISCH_TAC `moi_pdg_fs L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H
                 rho0 rho r R1 P'` THEN
  REWRITE_TAC[moi_pdg_fs] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_PDG_VMAP_CONT THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:complex,rho0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PDG_VS_F_CONT THEN ASM_MESON_TAC[];
      MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:complex)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC MOI_PDG_VS_PMAP_CONT THEN ASM_MESON_TAC[]]);;

(* The sector core: near a point of the outer region, V composed with a rotation
   agrees on one side with a smooth map of positive Jacobian. *)

let MOI_PDG_BALL_NORM = prove
 (`!c d y:real^N. y IN ball(c,d) ==> norm c - d < norm y /\ norm y < norm c + d`,
  REWRITE_TAC[IN_BALL; dist] THEN NORM_ARITH_TAC);;

let MOI_PDG_FS_SECTOR_CORE = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'
    s v t0 eta (S:complex->bool).
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\ norm v = &1 /\
      r / &2 <= t0 /\ t0 < rho /\ &0 < eta /\
      v * Cx t0 IN moi_pdg_ssec k b th1 th2 s /\
      (!x. x IN ball(Cx t0,eta) /\ S x ==> v * x IN moi_pdg_ssec k b th1 th2 s)
      ==> ?d g. &0 < d /\ smooth_map_on (ball(Cx t0,d)) (g:complex->complex) /\
                (!x. x IN ball(Cx t0,d) ==> v * x IN ball(vec 0,rho)) /\
                (!x. x IN ball(Cx t0,d) /\ S x
                     ==> g x = moi_pdg_vmap P' r (moi_pdg_fmap U phi f h)
                                 (moi_pdg_pmap L w k b th1 th2 H) (v * x)) /\
                (!x. x IN ball(Cx t0,d) ==> &0 < det(jacobian g (at x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_FS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  SUBGOAL_THEN `!y. y IN moi_pdg_dcone b th1 th2 (s:real^N->bool) INTER cball(vec 0,rho)
                    ==> &0 < det(jacobian (moi_pdg_mlin
                               ((H:(real^N->bool)->complex->complex) s) r) (at y))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_pdg_fs L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2
                   e R H rho0 rho r R1 P'` THEN
    REWRITE_TAC[moi_pdg_fs] THEN STRIP_TAC THEN X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t0 /\ norm(v * Cx t0) = t0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_PDG_ROT_NORM; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(v * Cx t0 = Cx(&0))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Os = {z:complex | Im(cexp(--(ii * Cx(k * (b(s:real^N->bool) +
                                    (th1 s + th2 s) / &2)))) * z) = &0
                                ==> &0 < Re(cexp(--(ii * Cx(k * (b s +
                                    (th1 s + th2 s) / &2)))) * z)}` THEN
  SUBGOAL_THEN
   `open(Os:complex->bool) /\
    smooth_map_on Os (moi_pdg_angf (inv k) (k * (b(s:real^N->bool) + (th1 s + th2 s) / &2))) /\
    (!z. z IN Os ==> det(jacobian (moi_pdg_angf (inv k)
                        (k * (b(s:real^N->bool) + (th1 s + th2 s) / &2))) (at z)) = inv k) /\
    (!z. z IN moi_pdg_ssec k b th1 th2 s /\ ~(z = Cx(&0)) ==> z IN Os)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Os" THEN REWRITE_TAC[MOI_PDG_SLIT_OPEN_C; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PDG_ANGF_SMOOTH THEN
      REWRITE_TAC[MOI_PDG_SLIT_OPEN_C; IN_ELIM_THM] THEN MESON_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_ANGF_DET THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`k:real`; `b(s:real^N->bool):real`; `th1(s:real^N->bool):real`;
                     `th2(s:real^N->bool):real`; `z:complex`] MOI_PDG_SEC_SLIT) THEN
      REWRITE_TAC[GSYM moi_pdg_ssec] THEN ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v * Cx t0) IN (Os:complex->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `v * Cx t0` (REWRITE_RULE[OPEN_CONTAINS_BALL]
    (ASSUME `open(Os:complex->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d2 = min (min d1 eta) (min (rho - t0) (t0 - r / &4))` THEN
  SUBGOAL_THEN `&0 < d2 /\ d2 <= d1 /\ d2 <= eta /\ d2 <= rho - t0 /\ d2 <= t0 - r / &4`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "d2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(v * Cx t0,d2)
                    ==> y IN (Os:complex->bool) /\ r / &4 < norm y /\ norm y < rho /\
                        ~(y = Cx(&0))` (LABEL_TAC "yb") THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_PDG_BALL_NORM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `d1:real`)) (concl th))) THEN
      UNDISCH_TAC `(y:complex) IN ball(v * Cx t0,d2)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `t0 - d2 < norm(Cx(&0))` THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `Gs = moi_pdg_angf (inv k) (k * (b(s:real^N->bool) + (th1 s + th2 s) / &2))` THEN
  SUBGOAL_THEN `smooth_map_on (ball(v * Cx t0,d2))
                  (moi_pdg_mlin ((H:(real^N->bool)->complex->complex) s) r o Gs)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
    EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN REWRITE_TAC[OPEN_BALL] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `y:complex` THEN
      DISCH_TAC THEN USE_THEN "yb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
        (ASSUME `(y:complex) IN ball(v * Cx t0,d2)`))) THEN
      EXPAND_TAC "Gs" THEN ASM_SIMP_TAC[MOI_PDG_ANGF_NORM] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `Os:complex->bool` THEN
      ASM_REWRITE_TAC[SUBSET] THEN USE_THEN "yb" (fun th -> MESON_TAC[th]);
      MATCH_MP_TAC MOI_PDG_MLIN_SMOOTH THEN ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(Cx t0,d2))
                  ((moi_pdg_mlin ((H:(real^N->bool)->complex->complex) s) r o Gs) o
                   (\x. (v:complex) * x))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_ROT_SMOOTH THEN EXISTS_TAC `ball(v * Cx t0,d2)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_PDG_ROT_BALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(jacobian ((moi_pdg_mlin ((H:(real^N->bool)->complex->complex) s) r o
                   Gs) o (\x. (v:complex) * x)) (at (Cx t0)))` ASSUME_TAC THENL
   [SUBGOAL_THEN `(v * Cx t0) IN ball(v * Cx t0,d2)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    SUBGOAL_THEN `(moi_pdg_mlin ((H:(real^N->bool)->complex->complex) s) r o Gs)
                    differentiable at (v * Cx t0)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(v * Cx t0,d2)` THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_PDG_DET_ROT_COMPOSE] THEN
    MP_TAC(ISPECL [`k:real`; `b:(real^N->bool)->real`; `th1:(real^N->bool)->real`;
                   `th2:(real^N->bool)->real`; `s:real^N->bool`; `v * Cx t0`]
      MOI_PDG_GMAP_ANGF) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                  `h:real^N->real^3`; `w:real^N`; `delta:real`; `U:real^N->bool`;
                  `phi:real^N->real^2`; `k:real`; `b:(real^N->bool)->real`;
                  `Q:(real^N->bool)->real^N->real^2`; `f:real^3->real^3`;
                  `v1:(real^N->bool)->real^N`; `v2:(real^N->bool)->real^N`;
                  `th1:(real^N->bool)->real`; `th2:(real^N->bool)->real`;
                  `e:(real^N->bool)->real`; `R:(real^N->bool)->complex->real^N`;
                  `H:(real^N->bool)->complex->complex`; `rho0:real`; `s:real^N->bool`;
                  `v * Cx t0`] MOI_PDG_VS_SEC_CHART) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(Gs:complex->complex) differentiable at (v * Cx t0) /\
                  moi_pdg_mlin ((H:(real^N->bool)->complex->complex) s) r
                    differentiable at (Gs(v * Cx t0))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `Os:complex->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `ball(vec 0:complex,e(s:real^N->bool))` THEN
        REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_PDG_MLIN_SMOOTH THEN ASM_REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
        UNDISCH_TAC `(Gs:complex->complex)(v * Cx t0) IN
                     ball(vec 0,e(s:real^N->bool)) INTER moi_pdg_dcone b th1 th2 s` THEN
        SIMP_TAC[IN_INTER]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_PDG_DET_CHAIN] THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `cball(vec 0:complex,rho)`)) (concl th))) THEN
      UNDISCH_TAC `(Gs:complex->complex)(v * Cx t0) IN
                   ball(vec 0,e(s:real^N->bool)) INTER moi_pdg_dcone b th1 th2 s` THEN
      REWRITE_TAC[IN_INTER; IN_CBALL_0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `det(jacobian (Gs:complex->complex) (at (v * Cx t0))) = inv k`
      SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_LT_INV]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(Cx t0,d2)`;
                 `(moi_pdg_mlin ((H:(real^N->bool)->complex->complex) s) r o Gs) o
                  (\x. (v:complex) * x)`; `Cx t0`] MOI_PDG_POS_NBHD) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`d:real`; `(moi_pdg_mlin ((H:(real^N->bool)->complex->complex) s) r o Gs) o
               (\x. (v:complex) * x)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t0,d) ==> v * x IN ball(v * Cx t0,d2) /\
                                            x IN ball(Cx t0,eta)` (LABEL_TAC "xb") THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN ball(Cx t0,d2)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC MOI_PDG_ROT_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:complex) IN ball(Cx t0,d2)` THEN REWRITE_TAC[IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t0,d2)` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    USE_THEN "xb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(x:complex) IN ball(Cx t0,d)`))) THEN
    USE_THEN "yb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `v * (x:complex) IN ball(v * Cx t0,d2)`))) THEN
    ASM_REWRITE_TAC[IN_BALL_0];
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    USE_THEN "xb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(x:complex) IN ball(Cx t0,d)`))) THEN
    USE_THEN "yb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `v * (x:complex) IN ball(v * Cx t0,d2)`))) THEN
    SUBGOAL_THEN `v * (x:complex) IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`L:(real^N->bool)->bool`; `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                  `h:real^N->real^3`; `w:real^N`; `delta:real`; `U:real^N->bool`;
                  `phi:real^N->real^2`; `k:real`; `b:(real^N->bool)->real`;
                  `Q:(real^N->bool)->real^N->real^2`; `f:real^3->real^3`;
                  `v1:(real^N->bool)->real^N`; `v2:(real^N->bool)->real^N`;
                  `th1:(real^N->bool)->real`; `th2:(real^N->bool)->real`;
                  `e:(real^N->bool)->real`; `R:(real^N->bool)->complex->real^N`;
                  `H:(real^N->bool)->complex->complex`; `rho0:real`; `rho:real`; `r:real`;
                  `R1:real`; `P':complex->complex`; `s:real^N->bool`; `v * x:complex`]
      MOI_PDG_FS_OUTER) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN EXPAND_TAC "Gs" THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PDG_GMAP_ANGF THEN ASM_REWRITE_TAC[]]);;

(* The half core (D2 region) and the inner core (near the vertex). *)

let MOI_PDG_FS_HALF_CORE = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'
    s t1 t2 v t0 eta (S:complex->bool).
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\
      ((t1 = th1 s /\ t2 = (th1 s + th2 s) / &2) \/
       (t1 = (th1 s + th2 s) / &2 /\ t2 = th2 s)) /\
      norm v = &1 /\ R1 <= t0 /\ t0 < r / &2 /\ &0 < eta /\
      v * Cx t0 IN moi_pdg_sec k (b s) t1 t2 /\
      (!x. x IN ball(Cx t0,eta) /\ S x ==> v * x IN moi_pdg_sec k (b s) t1 t2)
      ==> ?d g. &0 < d /\ smooth_map_on (ball(Cx t0,d)) (g:complex->complex) /\
                (!x. x IN ball(Cx t0,d) ==> v * x IN ball(vec 0,rho)) /\
                (!x. x IN ball(Cx t0,d) /\ S x
                     ==> g x = moi_pdg_vmap P' r (moi_pdg_fmap U phi f h)
                                 (moi_pdg_pmap L w k b th1 th2 H) (v * x)) /\
                (!x. x IN ball(Cx t0,d) ==> &0 < det(jacobian g (at x)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  SUBGOAL_THEN
   `?u g. open u /\
          {x | x IN moi_pdg_sec k (b(s:real^N->bool)) t1 t2 /\ R1 / &2 <= norm x} SUBSET u /\
          smooth_map_on u (g:complex->complex) /\
          (!x. x IN moi_pdg_sec k (b s) t1 t2 /\ R1 / &2 <= norm x ==> g x = P' x) /\
          (!x. x IN moi_pdg_sec k (b s) t1 t2 /\ R1 / &2 <= norm x
               ==> &0 < det(jacobian g (at x)))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_pdg_fs L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2
                   e R H rho0 rho r R1 P'` THEN
    REWRITE_TAC[moi_pdg_fs] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `t1:real`; `t2:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `uh:complex->bool` (X_CHOOSE_THEN `gh:complex->complex`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`uh:complex->bool`; `gh:complex->complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t0 /\ norm(v * Cx t0) = t0` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_PDG_ROT_NORM; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(v * Cx t0) IN (u:complex->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `u:complex->bool`)) (concl th) && is_binary "SUBSET" (concl th))) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `v * Cx t0` (REWRITE_RULE[OPEN_CONTAINS_BALL]
    (ASSUME `open(u:complex->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d2 = min (min d1 eta) (min (r / &2 - t0) (t0 - R1 / &2))` THEN
  SUBGOAL_THEN `&0 < d2 /\ d2 <= d1 /\ d2 <= eta /\ d2 <= r / &2 - t0 /\ d2 <= t0 - R1 / &2`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "d2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(v * Cx t0,d2)
                    ==> y IN (u:complex->bool) /\ R1 / &2 < norm y /\ norm y < r / &2`
  (LABEL_TAC "yb") THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_PDG_BALL_NORM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `d1:real`)) (concl th) && is_binary "SUBSET" (concl th))) THEN
      UNDISCH_TAC `(y:complex) IN ball(v * Cx t0,d2)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(v * Cx t0,d2)) (g:complex->complex)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_REWRITE_TAC[SUBSET] THEN USE_THEN "yb" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(Cx t0,d2)) ((g:complex->complex) o (\x. (v:complex) * x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_ROT_SMOOTH THEN EXISTS_TAC `ball(v * Cx t0,d2)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_PDG_ROT_BALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < det(jacobian ((g:complex->complex) o (\x. (v:complex) * x)) (at (Cx t0)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(g:complex->complex) differentiable at (v * Cx t0)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `u:complex->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_PDG_DET_ROT_COMPOSE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(Cx t0,d2)`; `(g:complex->complex) o (\x. (v:complex) * x)`; `Cx t0`]
    MOI_PDG_POS_NBHD) THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `(g:complex->complex) o (\x. (v:complex) * x)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t0,d) ==> v * x IN ball(v * Cx t0,d2) /\
                                            x IN ball(Cx t0,eta)` (LABEL_TAC "xb") THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:complex) IN ball(Cx t0,d2)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC MOI_PDG_ROT_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:complex) IN ball(Cx t0,d2)` THEN REWRITE_TAC[IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(Cx t0,d2)` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    USE_THEN "xb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(x:complex) IN ball(Cx t0,d)`))) THEN
    USE_THEN "yb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `v * (x:complex) IN ball(v * Cx t0,d2)`))) THEN
    REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    USE_THEN "xb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(x:complex) IN ball(Cx t0,d)`))) THEN
    USE_THEN "yb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `v * (x:complex) IN ball(v * Cx t0,d2)`))) THEN
    SUBGOAL_THEN `v * (x:complex) IN moi_pdg_sec k (b(s:real^N->bool)) t1 t2`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `norm(v * (x:complex)) <= r / &2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_PDG_VMAP_INNER; o_THM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_FS_INNER_CORE = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'
    v t0.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      norm v = &1 /\ &0 < t0 /\ t0 < R1
      ==> ?d g. &0 < d /\ smooth_map_on (ball(Cx t0,d)) (g:complex->complex) /\
                (!x. x IN ball(Cx t0,d) ==> v * x IN ball(vec 0,rho)) /\
                (!x. x IN ball(Cx t0,d)
                     ==> g x = moi_pdg_vmap P' r (moi_pdg_fmap U phi f h)
                                 (moi_pdg_pmap L w k b th1 th2 H) (v * x)) /\
                (!x. x IN ball(Cx t0,d) ==> &0 < det(jacobian g (at x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  SUBGOAL_THEN `?u. open u /\ cball(vec 0,R1) SUBSET u /\
                    smooth_map_on u (P':complex->complex) /\
                    !x. x IN u ==> &0 < det(jacobian P' (at x))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_pdg_fs L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2
                   e R H rho0 rho r R1 P'` THEN
    REWRITE_TAC[moi_pdg_fs] THEN STRIP_TAC THEN
    EXISTS_TAC `u:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(v * Cx t0) = t0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_PDG_ROT_NORM; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(v * Cx t0) IN (u:complex->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term ((=) `u:complex->bool`)) (concl th) && is_binary "SUBSET" (concl th))) THEN
    ASM_REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `v * Cx t0` (REWRITE_RULE[OPEN_CONTAINS_BALL]
    (ASSUME `open(u:complex->bool)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `d2 = min d1 (R1 - t0)` THEN
  SUBGOAL_THEN `&0 < d2 /\ d2 <= d1 /\ d2 <= R1 - t0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d2" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(v * Cx t0,d2) ==> y IN (u:complex->bool) /\ norm y < R1`
  (LABEL_TAC "yb") THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_PDG_BALL_NORM) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        can (find_term ((=) `d1:real`)) (concl th) && is_binary "SUBSET" (concl th))) THEN
      UNDISCH_TAC `(y:complex) IN ball(v * Cx t0,d2)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `d2:real` THEN EXISTS_TAC `(P':complex->complex) o (\x. (v:complex) * x)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. x IN ball(Cx t0,d2) ==> v * x IN (u:complex->bool) /\ norm(v * x) < R1`
  (LABEL_TAC "xb") THENL
   [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN USE_THEN "yb" MATCH_MP_TAC THEN
    MATCH_MP_TAC MOI_PDG_ROT_BALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PDG_ROT_SMOOTH THEN EXISTS_TAC `u:complex->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN USE_THEN "xb" (fun th -> MESON_TAC[th]);
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    USE_THEN "xb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(x:complex) IN ball(Cx t0,d2)`))) THEN
    REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    USE_THEN "xb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(x:complex) IN ball(Cx t0,d2)`))) THEN
    REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PDG_VMAP_INNER THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
    USE_THEN "xb" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th
      (ASSUME `(x:complex) IN ball(Cx t0,d2)`))) THEN
    SUBGOAL_THEN `(P':complex->complex) differentiable at (v * x)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `u:complex->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_PDG_DET_ROT_COMPOSE]]);;

(* Ray lemmas: one-sided and two-sided smooth extensions of V along a ray. *)

let MOI_PDG_VS_HALF_UPPER = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 a.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> ?s t1 t2 t. s IN L /\ aff_dim s = &2 /\ w IN s /\
                      ((t1 = th1 s /\ t2 = (th1 s + th2 s) / &2) \/
                       (t1 = (th1 s + th2 s) / &2 /\ t2 = th2 s)) /\
                      t1 <= t /\ t < t2 /\
                      cexp(ii * Cx a) = cexp(ii * Cx(k * (b s + t)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_UPPER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `t < (th1(s:real^N->bool) + th2 s) / &2` THENL
   [MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `th1(s:real^N->bool):real`;
                          `(th1(s:real^N->bool) + th2 s) / &2`; `t:real`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `(th1(s:real^N->bool) + th2 s) / &2`;
                          `th2(s:real^N->bool):real`; `t:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_VS_HALF_LOWER = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 a.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0
      ==> ?s t1 t2 t. s IN L /\ aff_dim s = &2 /\ w IN s /\
                      ((t1 = th1 s /\ t2 = (th1 s + th2 s) / &2) \/
                       (t1 = (th1 s + th2 s) / &2 /\ t2 = th2 s)) /\
                      t1 < t /\ t <= t2 /\
                      cexp(ii * Cx a) = cexp(ii * Cx(k * (b s + t)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_LOWER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `t <= (th1(s:real^N->bool) + th2 s) / &2` THENL
   [MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `th1(s:real^N->bool):real`;
                          `(th1(s:real^N->bool) + th2 s) / &2`; `t:real`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `(th1(s:real^N->bool) + th2 s) / &2`;
                          `th2(s:real^N->bool):real`; `t:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_ARG_UNIT = prove
 (`!v. norm v = &1 ==> cexp(ii * Cx(Arg v)) = v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(CONJUNCT2(CONJUNCT2(SPEC `v:complex` ARG))) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN MESON_TAC[]);;

let MOI_PDG_FS_RAY_UP = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'
    v t0.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      norm v = &1 /\ &0 < t0 /\ t0 < rho
      ==> ?d g. &0 < d /\ smooth_map_on (ball(Cx t0,d)) (g:complex->complex) /\
                (!x. x IN ball(Cx t0,d) ==> v * x IN ball(vec 0,rho)) /\
                (!x. x IN ball(Cx t0,d) /\ &0 <= Im x
                     ==> g x = moi_pdg_vmap P' r (moi_pdg_fmap U phi f h)
                                 (moi_pdg_pmap L w k b th1 th2 H) (v * x)) /\
                (!x. x IN ball(Cx t0,d) ==> &0 < det(jacobian g (at x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  FIRST_ASSUM(LABEL_TAC "argv" o MATCH_MP MOI_PDG_ARG_UNIT) THEN
  ASM_CASES_TAC `t0 < R1` THENL
   [MP_TAC(SPEC_ALL MOI_PDG_FS_INNER_CORE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `g:complex->complex`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `g:complex->complex`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  ASM_CASES_TAC `t0 < r / &2` THENL
   [MP_TAC(INST [`Arg v`,`a:real`] (SPEC_ALL MOI_PDG_VS_HALF_UPPER)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `t1:real`
      (X_CHOOSE_THEN `t2:real` (X_CHOOSE_THEN `t:real`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `v:complex`)) THEN
    MP_TAC(SPECL [`k:real`; `b(s:real^N->bool):real`; `t1:real`; `t2:real`; `t:real`;
                  `t0:real`] MOI_PDG_UPBALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `v * Cx t0 IN moi_pdg_sec k (b(s:real^N->bool)) t1 t2` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL; IM_CX; REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(INST [`\x:complex. &0 <= Im x`,`S:complex->bool`]
      (SPEC_ALL MOI_PDG_FS_HALF_CORE)) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  MP_TAC(INST [`Arg v`,`a:real`] (SPEC_ALL MOI_PDG_VS_UPPER)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `t:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `v:complex`)) THEN
  MP_TAC(SPECL [`k:real`; `b(s:real^N->bool):real`; `th1(s:real^N->bool):real`;
                `th2(s:real^N->bool):real`; `t:real`; `t0:real`] MOI_PDG_UPBALL) THEN
  ASM_REWRITE_TAC[GSYM moi_pdg_ssec] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `v * Cx t0 IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL; IM_CX; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(INST [`\x:complex. &0 <= Im x`,`S:complex->bool`]
    (SPEC_ALL MOI_PDG_FS_SECTOR_CORE)) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* The lower-side ray lemma. *)

let MOI_PDG_FS_RAY_LOW = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'
    v t0.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      norm v = &1 /\ &0 < t0 /\ t0 < rho
      ==> ?d g. &0 < d /\ smooth_map_on (ball(Cx t0,d)) (g:complex->complex) /\
                (!x. x IN ball(Cx t0,d) ==> v * x IN ball(vec 0,rho)) /\
                (!x. x IN ball(Cx t0,d) /\ Im x <= &0
                     ==> g x = moi_pdg_vmap P' r (moi_pdg_fmap U phi f h)
                                 (moi_pdg_pmap L w k b th1 th2 H) (v * x)) /\
                (!x. x IN ball(Cx t0,d) ==> &0 < det(jacobian g (at x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  FIRST_ASSUM(LABEL_TAC "argv" o MATCH_MP MOI_PDG_ARG_UNIT) THEN
  ASM_CASES_TAC `t0 < R1` THENL
   [MP_TAC(SPEC_ALL MOI_PDG_FS_INNER_CORE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `g:complex->complex`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`d:real`; `g:complex->complex`] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  ASM_CASES_TAC `t0 < r / &2` THENL
   [MP_TAC(INST [`Arg v`,`a:real`] (SPEC_ALL MOI_PDG_VS_HALF_LOWER)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `t1:real`
      (X_CHOOSE_THEN `t2:real` (X_CHOOSE_THEN `t:real`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
    FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `v:complex`)) THEN
    MP_TAC(SPECL [`k:real`; `b(s:real^N->bool):real`; `t1:real`; `t2:real`; `t:real`;
                  `t0:real`] MOI_PDG_LOWBALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `v * Cx t0 IN moi_pdg_sec k (b(s:real^N->bool)) t1 t2` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL; IM_CX; REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(INST [`\x:complex. Im x <= &0`,`S:complex->bool`]
      (SPEC_ALL MOI_PDG_FS_HALF_CORE)) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  MP_TAC(INST [`Arg v`,`a:real`] (SPEC_ALL MOI_PDG_VS_LOWER)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `t:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `v:complex`)) THEN
  MP_TAC(SPECL [`k:real`; `b(s:real^N->bool):real`; `th1(s:real^N->bool):real`;
                `th2(s:real^N->bool):real`; `t:real`; `t0:real`] MOI_PDG_LOWBALL) THEN
  ASM_REWRITE_TAC[GSYM moi_pdg_ssec] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `v * Cx t0 IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[CENTRE_IN_BALL; IM_CX; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(INST [`\x:complex. Im x <= &0`,`S:complex->bool`]
    (SPEC_ALL MOI_PDG_FS_SECTOR_CORE)) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

(* Two-sided extension inside a sector or a half, and rotating back. *)

let MOI_PDG_FS_RAY_FULL = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'
    s t v t0.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\ th1 s < t /\ t < th2 s /\
      (~(t = (th1 s + th2 s) / &2) \/ r / &2 <= t0) /\
      cexp(ii * Cx(k * (b s + t))) = v /\ &0 < t0 /\ t0 < rho
      ==> ?d g. &0 < d /\ smooth_map_on (ball(Cx t0,d)) (g:complex->complex) /\
                (!x. x IN ball(Cx t0,d) ==> v * x IN ball(vec 0,rho)) /\
                (!x. x IN ball(Cx t0,d)
                     ==> g x = moi_pdg_vmap P' r (moi_pdg_fmap U phi f h)
                                 (moi_pdg_pmap L w k b th1 th2 H) (v * x)) /\
                (!x. x IN ball(Cx t0,d) ==> &0 < det(jacobian g (at x)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  SUBGOAL_THEN `norm(v:complex) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN REWRITE_TAC[NORM_CEXP_II]; ALL_TAC] THEN
  ASM_CASES_TAC `t0 < R1` THENL
   [MP_TAC(SPEC_ALL MOI_PDG_FS_INNER_CORE) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  ASM_CASES_TAC `t0 < r / &2` THENL
   [SUBGOAL_THEN `~(t = (th1(s:real^N->bool) + th2 s) / &2)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `t < (th1(s:real^N->bool) + th2 s) / &2` THENL
     [MP_TAC(SPECL [`k:real`; `b(s:real^N->bool):real`; `th1(s:real^N->bool):real`;
                    `(th1(s:real^N->bool) + th2 s) / &2`; `t:real`; `t0:real`]
        MOI_PDG_SECBALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `v * Cx t0 IN moi_pdg_sec k (b(s:real^N->bool)) (th1 s)
                                  ((th1 s + th2 s) / &2)` ASSUME_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
      MP_TAC(INST [`\x:complex. T`,`S:complex->bool`;
                   `th1(s:real^N->bool):real`,`t1:real`;
                   `(th1(s:real^N->bool) + th2 s) / &2`,`t2:real`]
        (SPEC_ALL MOI_PDG_FS_HALF_CORE)) THEN
      REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      MP_TAC(SPECL [`k:real`; `b(s:real^N->bool):real`; `(th1(s:real^N->bool) + th2 s) / &2`;
                    `th2(s:real^N->bool):real`; `t:real`; `t0:real`]
        MOI_PDG_SECBALL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `v * Cx t0 IN moi_pdg_sec k (b(s:real^N->bool)) ((th1 s + th2 s) / &2)
                                  (th2 s)` ASSUME_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
      MP_TAC(INST [`\x:complex. T`,`S:complex->bool`;
                   `(th1(s:real^N->bool) + th2 s) / &2`,`t1:real`;
                   `th2(s:real^N->bool):real`,`t2:real`]
        (SPEC_ALL MOI_PDG_FS_HALF_CORE)) THEN
      REWRITE_TAC[] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  MP_TAC(SPECL [`k:real`; `b(s:real^N->bool):real`; `th1(s:real^N->bool):real`;
                `th2(s:real^N->bool):real`; `t:real`; `t0:real`] MOI_PDG_SECBALL) THEN
  ASM_REWRITE_TAC[GSYM moi_pdg_ssec] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `v * Cx t0 IN moi_pdg_ssec k b th1 th2 (s:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  MP_TAC(INST [`\x:complex. T`,`S:complex->bool`] (SPEC_ALL MOI_PDG_FS_SECTOR_CORE)) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_ROT_BACK = prove
 (`!(V:complex->complex) g v t0 d.
      norm v = &1 /\ smooth_map_on (ball(Cx t0,d)) g /\
      (!x. x IN ball(Cx t0,d) ==> g x = V(v * x)) /\
      (!x. x IN ball(Cx t0,d) ==> &0 < det(jacobian g (at x)))
      ==> smooth_map_on (ball(v * Cx t0,d)) V /\
          !y. y IN ball(v * Cx t0,d) ==> &0 < det(jacobian V (at y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(cnj v) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_CNJ]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(v * Cx t0,d) ==> cnj v * y IN ball(Cx t0,d)` ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`cnj v`; `v * Cx t0`; `d:real`; `y:complex`] MOI_PDG_ROT_BALL) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cnj v * (v * Cx t0) = Cx t0` SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_MUL_ASSOC; COMPLEX_MUL_CNJ] THEN
      ASM_REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_MUL_LID];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN ball(v * Cx t0,d)
                    ==> ((g:complex->complex) o (\y. cnj v * y)) y = (V:complex->complex) y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:complex` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `cnj v * y IN ball(Cx t0,d)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_PDG_ROT_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on (ball(v * Cx t0,d)) ((g:complex->complex) o (\y. cnj v * y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_ROT_SMOOTH THEN EXISTS_TAC `ball(Cx t0,d)` THEN
    ASM_SIMP_TAC[OPEN_BALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
    EXISTS_TAC `(g:complex->complex) o (\y. cnj v * y)` THEN ASM_SIMP_TAC[OPEN_BALL];
    X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `((g:complex->complex) o (\y. cnj v * y)) differentiable at y`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(v * Cx t0,d)` THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`(g:complex->complex) o (\y. cnj v * y)`; `V:complex->complex`;
                   `ball(v * Cx t0,d)`; `y:complex`] MOI_PDG_JAC_LOCAL_EQ) THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `cnj v * y IN ball(Cx t0,d)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(g:complex->complex) differentiable at (cnj v * y)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(Cx t0,d)` THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_PDG_DET_ROT_COMPOSE]]);;


(* Edge and middle directions, off-ray points, the vertex package from the final
   setting (MOI_PDG_FS_VP) and the existence of the final setting (MOI_PDG_FS_EXISTS). *)

(* Edge and middle directions in the vertex chart. *)

let MOI_PDG_UEDGE_UNIQUE = prove
 (`!(U:real^N->bool) (phi:real^N->real^2) rho (E:real^N->bool) u u'.
      &0 < rho /\ cball(vec 0,rho) SUBSET IMAGE phi U /\
      (!y. y IN IMAGE phi U ==> chart_inv(U,phi) y IN U /\ phi(chart_inv(U,phi) y) = y) /\
      norm u = &1 /\ (!t. &0 <= t /\ t < rho ==> chart_inv(U,phi) (Cx t * u) IN E) /\
      norm u' = &1 /\
      (!x. x IN E /\ x IN U /\ norm(phi x) < rho ==> ?t. &0 <= t /\ phi x = Cx t * u')
      ==> u = u'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx(rho / &2) * u IN IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (is_binary "SUBSET" o concl)) THEN
    REWRITE_TAC[IN_CBALL_0; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = chart_inv(U:real^N->bool,phi:real^N->real^2) (Cx(rho / &2) * u)` THEN
  SUBGOAL_THEN `(x:real^N) IN U /\ phi x = Cx(rho / &2) * u` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN E` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t = rho / &2` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:complex->real`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; CX_INJ] THEN
  MATCH_MP_TAC(TAUT `~p ==> (p \/ q ==> q)`) THEN ASM_REAL_ARITH_TAC);;

let MOI_PDG_UEDGE_EQ = prove
 (`!(U:real^N->bool) (phi:real^N->real^2) rho (E:real^N->bool) u.
      &0 < rho /\ cball(vec 0,rho) SUBSET IMAGE phi U /\
      (!y. y IN IMAGE phi U ==> chart_inv(U,phi) y IN U /\ phi(chart_inv(U,phi) y) = y) /\
      norm u = &1 /\ (!t. &0 <= t /\ t < rho ==> chart_inv(U,phi) (Cx t * u) IN E) /\
      (!x. x IN E /\ x IN U /\ norm(phi x) < rho ==> ?t. &0 <= t /\ phi x = Cx t * u)
      ==> moi_pdg_uedge U phi rho E = u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `norm(moi_pdg_uedge U phi rho E) = &1 /\
    (!t. &0 <= t /\ t < rho
         ==> chart_inv(U,phi) (Cx t * moi_pdg_uedge U phi rho E) IN (E:real^N->bool)) /\
    (!x. x IN E /\ x IN U /\ norm(phi x) < rho
         ==> ?t. &0 <= t /\ phi x = Cx t * moi_pdg_uedge U phi rho E)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_pdg_uedge] THEN CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `u:complex` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `phi:real^N->real^2`; `rho:real`; `E:real^N->bool`;
                 `moi_pdg_uedge (U:real^N->bool) (phi:real^N->real^2) rho E`; `u:complex`]
    MOI_PDG_UEDGE_UNIQUE) THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_VS_EDGES = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 E.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      E IN L /\ aff_dim E = &1 /\ w IN E
      ==> ?s. s IN L /\ aff_dim s = &2 /\ w IN s /\
              (E = segment[w,v1 s] \/ E = segment[w,v2 s])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_pdg_vs] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_PDG_VS_UNIT_RAY = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 s a t.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\ th1 s <= a /\ a <= th2 s /\
      &0 <= t /\ t < e s
      ==> chart_inv(U,phi) (Cx t * cexp(ii * Cx(k * (b s + a)))) =
          R s (Cx t * cexp(ii * Cx(b s + a)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `Cx t * cexp(ii * Cx(k * (b(s:real^N->bool) + a))) IN
                moi_pdg_ssec k b th1 th2 s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_SSEC_CONIC THEN ASM_REWRITE_TAC[MOI_PDG_SSEC_UNIT] THEN
    EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(INST [`Cx t * cexp(ii * Cx(k * (b(s:real^N->bool) + a)))`,`z:complex`]
    (SPEC_ALL MOI_PDG_VS_SEC_CHART)) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; NORM_CEXP_II] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  SIMP_TAC[MOI_PDG_GMAP_HOMOG; ASSUME `&0 <= t`] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOI_PDG_GMAP_UNIT THEN ASM_REWRITE_TAC[]);;

(* The edge directions and the middle directions of the final data. *)

let MOI_PDG_VS_EDGE_DIR = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 s.
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      s IN L /\ aff_dim s = &2 /\ w IN s
      ==> (!t. &0 <= t /\ t < e s
               ==> chart_inv(U,phi) (Cx t * cexp(ii * Cx(k * (b s + th1 s)))) IN
                   segment[w,v1 s] /\
                   chart_inv(U,phi) (Cx t * cexp(ii * Cx(k * (b s + th2 s)))) IN
                   segment[w,v2 s]) /\
          (!x. x IN segment[w,v1 s] /\ x IN U
               ==> ?t. &0 <= t /\ phi x = Cx t * cexp(ii * Cx(k * (b s + th1 s)))) /\
          (!x. x IN segment[w,v2 s] /\ x IN U
               ==> ?t. &0 <= t /\ phi x = Cx t * cexp(ii * Cx(k * (b s + th2 s))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(INST [`th1(s:real^N->bool):real`,`a:real`] (SPEC_ALL MOI_PDG_VS_UNIT_RAY)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(INST [`th2(s:real^N->bool):real`,`a:real`] (SPEC_ALL MOI_PDG_VS_UNIT_RAY)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[SUBSET]
      (ASSUME `segment[w:real^N,(v1:(real^N->bool)->real^N) s] SUBSET s`)) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(MATCH_MP (ASSUME `!x. x IN segment[w:real^N,(v1:(real^N->bool)->real^N) s]
                       ==> ?t. &0 <= t /\ (Q:(real^N->bool)->real^N->real^2) s x =
                                         Cx t * cexp(ii * Cx(b s + th1 s))`)
      (ASSUME `(x:real^N) IN segment[w,(v1:(real^N->bool)->real^N) s]`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(phi:real^N->real^2) x = moi_smo_ang k (b(s:real^N->bool))
                    ((Q:(real^N->bool)->real^N->real^2) s x)` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PDG_ANG_POLAR0 THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[SUBSET]
      (ASSUME `segment[w:real^N,(v2:(real^N->bool)->real^N) s] SUBSET s`)) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(MATCH_MP (ASSUME `!x. x IN segment[w:real^N,(v2:(real^N->bool)->real^N) s]
                       ==> ?t. &0 <= t /\ (Q:(real^N->bool)->real^N->real^2) s x =
                                         Cx t * cexp(ii * Cx(b s + th2 s))`)
      (ASSUME `(x:real^N) IN segment[w,(v2:(real^N->bool)->real^N) s]`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(phi:real^N->real^2) x = moi_smo_ang k (b(s:real^N->bool))
                    ((Q:(real^N->bool)->real^N->real^2) s x)` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PDG_ANG_POLAR0 THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PDG_FS_UEDGE = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' s.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      s IN L /\ aff_dim s = &2 /\ w IN s
      ==> moi_pdg_uedge U phi rho (segment[w,v1 s]) = cexp(ii * Cx(k * (b s + th1 s))) /\
          moi_pdg_uedge U phi rho (segment[w,v2 s]) = cexp(ii * Cx(k * (b s + th2 s))) /\
          (!t. &0 <= t /\ t < rho
               ==> chart_inv(U,phi) (Cx t * cexp(ii * Cx(k * (b s + th1 s)))) IN
                   segment[w,v1 s] /\
                   chart_inv(U,phi) (Cx t * cexp(ii * Cx(k * (b s + th2 s)))) IN
                   segment[w,v2 s]) /\
          (!x. x IN segment[w,v1 s] /\ x IN U
               ==> ?t. &0 <= t /\ phi x = Cx t * cexp(ii * Cx(k * (b s + th1 s)))) /\
          (!x. x IN segment[w,v2 s] /\ x IN U
               ==> ?t. &0 <= t /\ phi x = Cx t * cexp(ii * Cx(k * (b s + th2 s))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  MP_TAC(SPEC_ALL MOI_PDG_FS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_EDGE_DIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. &0 <= t /\ t < rho
        ==> chart_inv(U,phi) (Cx t * cexp(ii * Cx(k * (b(s:real^N->bool) + th1 s)))) IN
            segment[w:real^N,v1 s] /\
            chart_inv(U,phi) (Cx t * cexp(ii * Cx(k * (b s + th2 s)))) IN
            segment[w,(v2:(real^N->bool)->real^N) s]`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:complex,rho) SUBSET IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(vec 0:complex,rho0)` THEN
    ASM_SIMP_TAC[SUBSET_CBALL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_PDG_UEDGE_EQ THEN ASM_SIMP_TAC[NORM_CEXP_II]);;

let MOI_PDG_FS_UEDGE_PROP = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' E.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      E IN L /\ aff_dim E = &1 /\ w IN E
      ==> norm(moi_pdg_uedge U phi rho E) = &1 /\
          (!t. &0 <= t /\ t < rho
               ==> chart_inv (U,phi) (Cx t * moi_pdg_uedge U phi rho E) IN E) /\
          (!x. x IN E /\ x IN U /\ norm(phi x) < rho
               ==> ?t. &0 <= t /\ phi x = Cx t * moi_pdg_uedge U phi rho E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_EDGES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(SPEC_ALL MOI_PDG_FS_UEDGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  ASM_SIMP_TAC[NORM_CEXP_II]);;

let MOI_PDG_FS_UART = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' s.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      s IN L /\ aff_dim s = &2 /\ w IN s
      ==> norm(moi_pdg_uart k b th1 th2 s) = &1 /\
          (!t. &0 < t /\ t < rho
               ==> chart_inv(U,phi) (Cx t * moi_pdg_uart k b th1 th2 s) IN
                   relative_interior s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  MP_TAC(SPEC_ALL MOI_PDG_FS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_pdg_uart; NORM_CEXP_II] THEN X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  MP_TAC(INST [`(th1(s:real^N->bool) + th2 s) / &2`,`a:real`]
    (SPEC_ALL MOI_PDG_VS_UNIT_RAY)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Off-ray points and the middle rays far from the vertex. *)

let MOI_PDG_ROT_BALL_BACK = prove
 (`!v t0 d y z:complex. norm v = &1 /\ v * t0 = z /\ y IN ball(z,d)
       ==> cnj v * y IN ball(t0,d) /\ v * (cnj v * y) = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MOI_PDG_ROT_INV] THEN
  MP_TAC(ISPECL [`cnj v`; `z:complex`; `d:real`; `y:complex`] MOI_PDG_ROT_BALL) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CNJ] THEN
  SUBGOAL_THEN `cnj v * z = t0` SUBST1_TAC THENL
   [EXPAND_TAC "z" THEN REWRITE_TAC[COMPLEX_MUL_ASSOC; COMPLEX_MUL_CNJ] THEN
    ASM_REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_MUL_LID];
    SIMP_TAC[]]);;

let MOI_PDG_FS_EDGE_FACTS = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' s.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      s IN L /\ aff_dim s = &2 /\ w IN s
      ==> segment[w,v1 s] IN L /\ aff_dim(segment[w,v1 s]) = &1 /\ w IN segment[w,v1 s] /\
          moi_pdg_uedge U phi rho (segment[w,v1 s]) = cexp(ii * Cx(k * (b s + th1 s))) /\
          segment[w,v2 s] IN L /\ aff_dim(segment[w,v2 s]) = &1 /\ w IN segment[w,v2 s] /\
          moi_pdg_uedge U phi rho (segment[w,v2 s]) = cexp(ii * Cx(k * (b s + th2 s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  MP_TAC(SPEC_ALL MOI_PDG_FS_UEDGE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[]);;

let MOI_PDG_FS_OFFRAY = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' z.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      z IN ball(vec 0,rho) /\ ~(z = vec 0) /\
      (!E t. E IN L /\ aff_dim E = &1 /\ w IN E /\ &0 < t
             ==> ~(z = Cx t * moi_pdg_uedge U phi rho E)) /\
      (!s t. s IN L /\ aff_dim s = &2 /\ w IN s /\ &0 < t
             ==> ~(z = Cx t * moi_pdg_uart k b th1 th2 s))
      ==> ?d. &0 < d /\ ball(z,d) SUBSET ball(vec 0,rho) /\
              smooth_map_on (ball(z,d))
                (moi_pdg_vmap P' r (moi_pdg_fmap U phi f h) (moi_pdg_pmap L w k b th1 th2 H)) /\
              !y. y IN ball(z,d)
                  ==> &0 < det(jacobian (moi_pdg_vmap P' r (moi_pdg_fmap U phi f h)
                                           (moi_pdg_pmap L w k b th1 th2 H)) (at y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  SUBGOAL_THEN `&0 < norm(z:complex) /\ norm z < rho` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:complex) IN ball(vec 0,rho)` THEN UNDISCH_TAC `~(z:complex = vec 0)` THEN
    REWRITE_TAC[IN_BALL_0; GSYM NORM_POS_LT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(INST [`Arg z`,`a:real`] (SPEC_ALL MOI_PDG_VS_UPPER)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `Cx(norm z) * cexp(ii * Cx(k * (b(s:real^N->bool) + t))) = z /\
                cexp(ii * Cx(k * (b(s:real^N->bool) + t))) * Cx(norm z) = z`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `cexp(ii * Cx(Arg z))`)) THEN
    MP_TAC(CONJUNCT2(CONJUNCT2(SPEC `z:complex` ARG))) THEN
    MESON_TAC[COMPLEX_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z = Cx(norm z) * cexp(ii * Cx(k * (b(s:real^N->bool) + th1 s)))) /\
                ~(z = Cx(norm z) * cexp(ii * Cx(k * (b s + (th1 s + th2 s) / &2))))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC_ALL MOI_PDG_FS_EDGE_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`segment[w:real^N,(v1:(real^N->bool)->real^N) s]`;
                                    `norm(z:complex)`] o check (fun th ->
        can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_pdg_uedge"))
            (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `norm(z:complex)`] o check (fun th ->
        can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_pdg_uart"))
            (concl th) && is_forall (concl th))) THEN
      ASM_REWRITE_TAC[moi_pdg_uart]];
    ALL_TAC] THEN
  SUBGOAL_THEN `th1(s:real^N->bool) < t` ASSUME_TAC THENL
   [ASM_CASES_TAC `t:real = th1(s:real^N->bool)` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(z = Cx(norm z) * cexp(ii * Cx(k * (b(s:real^N->bool) + th1 s))))` THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t = (th1(s:real^N->bool) + th2 s) / &2)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(z = Cx(norm z) * cexp(ii * Cx(k * (b(s:real^N->bool) +
                                                  (th1 s + th2 s) / &2))))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(INST [`cexp(ii * Cx(k * (b(s:real^N->bool) + t)))`,`v:complex`;
               `norm(z:complex)`,`t0:real`] (SPEC_ALL MOI_PDG_FS_RAY_FULL)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                   (moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H)`;
                 `g:complex->complex`; `cexp(ii * Cx(k * (b(s:real^N->bool) + t)))`;
                 `norm(z:complex)`; `d:real`] MOI_PDG_ROT_BACK) THEN
  ASM_REWRITE_TAC[NORM_CEXP_II] THEN STRIP_TAC THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`cexp(ii * Cx(k * (b(s:real^N->bool) + t)))`; `Cx(norm(z:complex))`;
                 `d:real`; `y:complex`; `z:complex`] MOI_PDG_ROT_BALL_BACK) THEN
  ASM_REWRITE_TAC[NORM_CEXP_II] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cnj(cexp(ii * Cx(k * (b(s:real^N->bool) + t)))) * y` o
    check (fun th -> can (find_term ((=) `ball(vec 0:complex,rho)`)) (concl th) &&
                     is_forall (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let MOI_PDG_FS_ARTFAR = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' s t0.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P' /\
      s IN L /\ aff_dim s = &2 /\ w IN s /\ rho / &4 <= t0 /\ t0 < rho
      ==> ?d. &0 < d /\
              smooth_map_on (ball(Cx t0,d))
                (\x. moi_pdg_vmap P' r (moi_pdg_fmap U phi f h)
                       (moi_pdg_pmap L w k b th1 th2 H) (moi_pdg_uart k b th1 th2 s * x)) /\
              (!x. x IN ball(Cx t0,d) ==> moi_pdg_uart k b th1 th2 s * x IN ball(vec 0,rho))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  MP_TAC(SPEC_ALL MOI_PDG_FS_TRI) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(INST [`(th1(s:real^N->bool) + th2 s) / &2`,`t:real`;
               `moi_pdg_uart k b th1 th2 (s:real^N->bool)`,`v:complex`]
    (SPEC_ALL MOI_PDG_FS_RAY_FULL)) THEN
  REWRITE_TAC[moi_pdg_uart] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `g:complex->complex` THEN
  ASM_SIMP_TAC[OPEN_BALL]);;

(* The vertex package from the final setting. *)

let MOI_PDG_FS_VP = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'.
      moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'
      ==> moi_pdg_vp L sigma h w delta U phi rho R1 f
            (moi_pdg_vmap P' r (moi_pdg_fmap U phi f h) (moi_pdg_pmap L w k b th1 th2 H))
            (moi_pdg_uedge U phi rho) (moi_pdg_uart k b th1 th2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PDG_FS_VS) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cball(vec 0:complex,rho) SUBSET cball(vec 0,rho0)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_CBALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. r / &4 <= norm x
         ==> (P':complex->complex) x =
             moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H x) /\
    (?u. open u /\ cball(vec 0,R1) SUBSET u /\ smooth_map_on u P' /\
         !x. x IN u ==> &0 < det(jacobian P' (at x)))` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_pdg_fs L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2
                   e R H rho0 rho r R1 P'` THEN
    REWRITE_TAC[moi_pdg_fs] THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; EXISTS_TAC `u:complex->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `R1 < rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:complex,rho) SUBSET IMAGE (phi:real^N->real^2) U` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(vec 0:complex,rho0)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN cball(vec 0,rho)
                    ==> chart_inv (U:real^N->bool,phi:real^N->real^2) z IN ball(w,delta)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:complex) IN cball(vec 0,rho0)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:complex` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `delta:real`)) (concl th))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                  (moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H)
                continuous_on cball(vec 0,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PDG_FS_CONT THEN
    MAP_EVERY EXISTS_TAC [`sigma:((real^N->bool)#(real^N->real^2))->bool`; `delta:real`;
      `Q:(real^N->bool)->real^N->real^2`; `v1:(real^N->bool)->real^N`;
      `v2:(real^N->bool)->real^N`; `e:(real^N->bool)->real`;
      `R:(real^N->bool)->complex->real^N`; `rho0:real`; `R1:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN cball(vec 0,rho) /\ rho / &2 <= norm z
        ==> moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
              (moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H) z =
            moi_pdg_st f (h(chart_inv (U,phi) z)) /\
            ~((f(h(chart_inv (U:real^N->bool,phi:real^N->real^2) z)))$3 = &1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM moi_pdg_fmap] THEN MATCH_MP_TAC MOI_PDG_VMAP_FAR THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPEC_ALL MOI_PDG_VS_F_LOCAL) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:complex) IN cball(vec 0,rho)` THEN
        REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
        SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?u0. open u0 /\ cball(vec 0,R1) SUBSET u0 /\
         smooth_map_on u0 (moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                             (moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H)) /\
         !y. y IN u0 ==> &0 < det(jacobian (moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                             (moi_pdg_pmap L w k b th1 th2 H)) (at y))`
  ASSUME_TAC THENL
   [EXISTS_TAC `(u:complex->bool) INTER ball(vec 0,r / &2)` THEN
    SUBGOAL_THEN `!y. y IN (u:complex->bool) INTER ball(vec 0,r / &2)
                      ==> moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                            (moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H) y = P' y`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:complex` THEN REWRITE_TAC[IN_INTER; IN_BALL_0] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_PDG_VMAP_INNER THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL];
      REWRITE_TAC[SUBSET_INTER] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0; IN_BALL_0] THEN X_GEN_TAC `y:complex` THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `P':complex->complex` THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `u:complex->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      X_GEN_TAC `y:complex` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`P':complex->complex`;
                     `moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                        (moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H)`;
                     `(u:complex->bool) INTER ball(vec 0,r / &2)`; `y:complex`]
        MOI_PDG_JAC_LOCAL_EQ) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `u:complex->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!E:real^N->bool. E IN L /\ aff_dim E = &1 /\ w IN E
        ==> norm(moi_pdg_uedge (U:real^N->bool) phi rho E) = &1 /\
            (!t. &0 <= t /\ t < rho
                 ==> chart_inv (U,phi) (Cx t * moi_pdg_uedge U phi rho E) IN E) /\
            (!x. x IN E /\ x IN U /\ norm(phi x) < rho
                 ==> ?t. &0 <= t /\ phi x = Cx t * moi_pdg_uedge U phi rho E)`
  ASSUME_TAC THENL
   [X_GEN_TAC `E:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL MOI_PDG_FS_UEDGE_PROP) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN L /\ aff_dim s = &2 /\ w IN s
        ==> norm(moi_pdg_uart k b th1 th2 s) = &1 /\
            (!t. &0 < t /\ t < rho
                 ==> chart_inv (U,phi) (Cx t * moi_pdg_uart k b th1 th2 s) IN
                     relative_interior s)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL MOI_PDG_FS_UART) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ball(vec 0,rho) /\ ~(z = vec 0) /\
        (!E t. E IN L /\ aff_dim E = &1 /\ w IN E /\ &0 < t
               ==> ~(z = Cx t * moi_pdg_uedge U phi rho E)) /\
        (!s t. s IN L /\ aff_dim s = &2 /\ w IN s /\ &0 < t
               ==> ~(z = Cx t * moi_pdg_uart k b th1 th2 s))
        ==> ?d. &0 < d /\ ball(z,d) SUBSET ball(vec 0,rho) /\
                smooth_map_on (ball(z,d))
                  (moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                     (moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H)) /\
                !y. y IN ball(z,d)
                    ==> &0 < det(jacobian (moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                                             (moi_pdg_pmap L w k b th1 th2 H)) (at y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL MOI_PDG_FS_OFFRAY) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v t0. ((?E. E IN L /\ aff_dim E = &1 /\ w IN E /\ v = moi_pdg_uedge U phi rho E) \/
            (?s. s IN L /\ aff_dim s = &2 /\ w IN s /\ v = moi_pdg_uart k b th1 th2 s)) /\
           &0 < t0 /\ t0 < rho
           ==> (?d g. &0 < d /\ smooth_map_on (ball(Cx t0,d)) (g:complex->complex) /\
                      (!x. x IN ball(Cx t0,d) ==> v * x IN ball(vec 0,rho)) /\
                      (!x. x IN ball(Cx t0,d) /\ &0 <= Im x
                           ==> g x = moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                                       (moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H)
                                       (v * x)) /\
                      (!x. x IN ball(Cx t0,d) ==> &0 < det(jacobian g (at x)))) /\
               (?d g. &0 < d /\ smooth_map_on (ball(Cx t0,d)) (g:complex->complex) /\
                      (!x. x IN ball(Cx t0,d) ==> v * x IN ball(vec 0,rho)) /\
                      (!x. x IN ball(Cx t0,d) /\ Im x <= &0
                           ==> g x = moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                                       (moi_pdg_pmap L w k b th1 th2 H) (v * x)) /\
                      (!x. x IN ball(Cx t0,d) ==> &0 < det(jacobian g (at x))))`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:complex` THEN X_GEN_TAC `t0:real` THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `norm(v:complex) = &1` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC_ALL MOI_PDG_FS_RAY_UP) THEN ASM_REWRITE_TAC[];
      MP_TAC(SPEC_ALL MOI_PDG_FS_RAY_LOW) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t0. s IN L /\ aff_dim s = &2 /\ w IN s /\ rho / &4 <= t0 /\ t0 < rho
           ==> ?d. &0 < d /\
                   smooth_map_on (ball(Cx t0,d))
                     (\x. moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
                            (moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H)
                            (moi_pdg_uart k b th1 th2 s * x)) /\
                   (!x. x IN ball(Cx t0,d)
                        ==> moi_pdg_uart k b th1 th2 s * x IN ball(vec 0,rho))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN X_GEN_TAC `t0:real` THEN STRIP_TAC THEN
    MP_TAC(SPEC_ALL MOI_PDG_FS_ARTFAR) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_pdg_vp] THEN ASM_REWRITE_TAC[]);;

(* Existence of the final setting. *)

let MOI_PDG_FS_EXISTS = prove
 (`!L sigma (h:real^N->real^3) w delta U phi k b Q f v1 v2 th1 th2 e R H rho0.
      MOI_SMO_LIN_STATEMENT /\ MOI_SMO_VERTEX2_STATEMENT /\
      MOI_SMO_VERTEX_DEGREE_STATEMENT /\
      moi_pdg_vs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 /\
      (!s. s IN L /\ aff_dim s = &2 /\ w IN s ==> &0 < det(jacobian (H s) (at (vec 0))))
      ==> ?rho r R1 P'.
            moi_pdg_fs L sigma h w delta U phi k b Q f v1 v2 th1 th2 e R H rho0 rho r R1 P'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_LIN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho1:real` (X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `r = min (r0 / &2) (rho1 / &2)` THEN
  SUBGOAL_THEN `&0 < r /\ r < r0 /\ r <= rho1 / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(INST [`r / &4`,`R2:real`] (SPEC_ALL MOI_PDG_VS_D2)) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P':complex->complex` (X_CHOOSE_THEN `R1:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`rho1:real`; `r:real`; `R1:real`; `P':complex->complex`] THEN
  REWRITE_TAC[moi_pdg_fs] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;


(* The vertex package from the leaves (through moi_pdg_vp_statement). *)

let MOI_PDG_VP_FROM_LEAVES = prove
 (`!u:N->bool. MOI_SMO_LIN_STATEMENT /\ MOI_SMO_VERTEX2_STATEMENT /\
              MOI_SMO_CREASE_ORIENT_STATEMENT /\ MOI_SMO_VERTEX_DEGREE_STATEMENT /\
              MOI_SMO_SURFACE_COMPLEX_STATEMENT u
              ==> moi_pdg_vp_statement u`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_pdg_vp_statement] THEN
  MAP_EVERY X_GEN_TAC [`L:(real^N->bool)->bool`;
                       `sigma:((real^N->bool)#(real^N->real^2))->bool`;
                       `h:real^N->real^3`; `h':real^3->real^N`; `w:real^N`; `delta:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!s. s IN (L:(real^N->bool)->bool) /\ ~(s = {})
                    ==> ?t. t IN L /\ aff_dim t = &2 /\ s SUBSET t`
  ASSUME_TAC THENL
   [UNDISCH_TAC `MOI_SMO_SURFACE_COMPLEX_STATEMENT (u:N->bool)` THEN
    REWRITE_TAC[MOI_SMO_SURFACE_COMPLEX_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPEC `L:(real^N->bool)->bool`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `h':real^3->real^N`] THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_smo_conical_pd L sigma (h:real^N->real^3)` THEN
  REWRITE_TAC[moi_smo_conical_pd] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` (X_CHOOSE_THEN `phi:real^N->real^2`
    (X_CHOOSE_THEN `k:real` (X_CHOOSE_THEN `b:(real^N->bool)->real`
    (X_CHOOSE_THEN `Q:(real^N->bool)->real^N->real^2` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(SPEC_ALL MOI_PDG_VS_POS_EXISTS) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun u -> is_const u && fst(dest_const u) = "moi_smo_ang")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC_ALL MOI_PDG_FS_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`U:real^N->bool`; `phi:real^N->real^2`; `rho:real`; `R1:real`; `f:real^3->real^3`;
    `moi_pdg_vmap P' r (moi_pdg_fmap (U:real^N->bool) phi f h)
       (moi_pdg_pmap (L:(real^N->bool)->bool) w k b th1 th2 H)`;
    `moi_pdg_uedge (U:real^N->bool) phi rho`;
    `moi_pdg_uart k (b:(real^N->bool)->real) th1 th2`] THEN
  MP_TAC(SPEC_ALL MOI_PDG_FS_VP) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem MOI_SMO_PD2_FROM_LEAVES.                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_SMO_PD2_FROM_LEAVES = prove
 (`!u:N->bool. MOI_SMO_LIN_STATEMENT /\ MOI_SMO_VERTEX2_STATEMENT /\
              MOI_SMO_CREASE_STATEMENT /\ MOI_SMO_CREASE_ORIENT_STATEMENT /\
              MOI_SMO_VERTEX_DEGREE_STATEMENT /\
              MOI_SMO_LOCAL_HOMEO_SPHERE_STATEMENT u /\
              MOI_SMO_SURFACE_COMPLEX_STATEMENT u
              ==> MOI_SMO_PD2_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_PDG_PD2_FROM_VP THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PDG_VP_FROM_LEAVES THEN ASM_REWRITE_TAC[]);;

