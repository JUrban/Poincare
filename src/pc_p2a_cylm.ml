(* ========================================================================= *)
(* pc_p2a_cylm: geometry of the cylinder models of p2b_cyl_model (MT Prop    *)
(* 9.83 (2),(3)) at one time slice, for MT Prop 9.58 (pc_p2a_kap0) and Thm   *)
(* 9.59 (pc_p2a_asv):                                                        *)
(* (1) reduction to the standard cylinder: a slice lam cylinder_flow(t/lam)  *)
(*     is c times cylinder_flow 0 with c = lam - t after the radial power    *)
(*     map of RFB_CYL_SETUP, which commutes with rfs_twist;                  *)
(* (2) unit balls have volume at least 1/40 once c >= 1/2, uniformly in c;   *)
(* (3) balls grow at most linearly (P2ACM_STD_BALL_UPPER).                   *)
(* ========================================================================= *)

needs "src/pc_rf_basic.ml";;
needs "src/pc_smt_product.ml";;
needs "src/pc_grg_dist2.ml";;
needs "src/pc_p2b_gpb.ml";;
needs "src/pc_p2b_cap.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The standard model and the reduction of a slice lam                      *)
(* cylinder_flow(t / lam) to (lam - t) cylinder_flow 0.                     *)
(* ========================================================================= *)

(* A covering of a slice by real^3 minus the origin, one-to-one or two-to-  *)
(* one through rfs_twist, locally a parametrization, whose pullback metric  *)
(* is c times the round cylinder cylinder_flow 0 = (2 / |y|^2) delta.       *)

let p2acm_std = new_definition
 `p2acm_std (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
            (q:real^3->B) (c:real) <=>
    &0 < c /\
    IMAGE q {y:real^3 | ~(y = vec 0)} = topspace top /\
    (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) q) /\
    ((!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (q y = q z <=> z = y)) \/
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (q y = q z <=> z = y \/ z = rfs_twist y))) /\
    (!y. ~(y = vec 0) ==> rfs_pullback atlas q g y = c %% cylinder_flow (&0) y)`;;

(* ------------------------------------------------------------------------- *)
(* Small facts: the twist, the round cylinder, pullbacks of matrix fields.   *)
(* ------------------------------------------------------------------------- *)

let P2ACM_TWIST_NZ = prove
 (`!y:real^3. ~(y = vec 0) ==> ~(rfs_twist y = vec 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[rfs_twist; VECTOR_NEG_EQ_0; VECTOR_MUL_EQ_0; REAL_INV_EQ_0;
              REAL_POW_EQ_0; NORM_EQ_0] THEN
  ASM_REWRITE_TAC[]);;

let P2ACM_TWIST_NORM2 = prove
 (`!y:real^3. ~(y = vec 0) ==> norm(rfs_twist y) pow 2 = inv(norm y pow 2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; CONV_TAC REAL_FIELD]);;

let P2ACM_RPOW_ARITH = prove
 (`!x e. &0 < x ==> inv(x rpow e) * inv x = inv(x rpow (&2 * e + &1)) * x rpow e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x rpow (&2 * e + &1) = x rpow e * x rpow e * x` SUBST1_TAC THENL
   [SUBGOAL_THEN `&2 * e + &1 = e + e + &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RPOW_ADD; RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < x rpow e` MP_TAC THENL [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < x` THEN CONV_TAC REAL_FIELD);;

(* The radial power maps commute with the twist. *)

let P2ACM_PW_TWIST = prove
 (`!e y:real^3.
     ~(y = vec 0)
     ==> ((norm(rfs_twist y) pow 2) rpow e) % rfs_twist y =
         rfs_twist(((norm y pow 2) rpow e) % y)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[P2ACM_TWIST_NORM2] THEN
  REWRITE_TAC[rfs_twist] THEN
  ASM_SIMP_TAC[RFB_PW_NORM2] THEN
  REWRITE_TAC[RPOW_INV; VECTOR_MUL_RNEG; VECTOR_MUL_ASSOC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC P2ACM_RPOW_ARITH THEN ASM_SIMP_TAC[REAL_POW_LT; NORM_POS_LT]);;

let P2ACM_CYL0 = prove
 (`!y:real^3. cylinder_flow (&0) y = (&2 / norm y pow 2) %% mat 1`,
  REWRITE_TAC[cylinder_flow; REAL_SUB_RZERO; MATRIX_CMUL_LID] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; MATRIX_CMUL_LZERO; MATRIX_ADD_RID]);;

let P2ACM_MPULLBACK_PT = prove
 (`!(h:real^N->real^N) (G:real^N->real^N^N) G' y.
     G (h y) = G' (h y) ==> mpullback h G y = mpullback h G' y`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[mpullback]);;

let P2ACM_MPULLBACK_CMUL = prove
 (`!(h:real^N->real^N) (G:real^N->real^N^N) c y.
     mpullback h (\w. c %% G w) y = c %% mpullback h G y`,
  REWRITE_TAC[mpullback; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

let P2ACM_MPULLBACK_ID_LOCAL = prove
 (`!(k:real^N->real^N) (G:real^N->real^N^N) s y.
     open s /\ y IN s /\ (!w. w IN s ==> k w = w) ==> mpullback k G y = G y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `frechet_derivative (k:real^N->real^N) (at y) = (\x. x)` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    UNDISCH_TAC `open(s:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `d:real`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `ball(y:real^N,d) SUBSET s` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[mpullback; MATRIX_ID; TRANSP_MAT; MATRIX_MUL_LID; MATRIX_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Precomposition of a local parametrization with a diffeomorphism of real^3 *)
(* minus the origin, in the ball form of the model.                          *)
(* ------------------------------------------------------------------------- *)

let P2ACM_DIFFEO_FACTS = prove
 (`!(h:real^3->real^3) h'.
     diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0) h h'
     ==> !w. ~(w = vec 0)
             ==> ~(h w = vec 0) /\ ~(h' w = vec 0) /\ h'(h w) = w /\ h(h' w) = w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (h:real^3->real^3) ((:real^3) DELETE vec 0) = (:real^3) DELETE vec 0` THEN
    UNDISCH_TAC `(w:real^3) IN (:real^3) DELETE vec 0` THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (h':real^3->real^3) ((:real^3) DELETE vec 0) = (:real^3) DELETE vec 0` THEN
    UNDISCH_TAC `(w:real^3) IN (:real^3) DELETE vec 0` THEN SET_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let P2ACM_PARAM_PRECOMP = prove
 (`!top atlas (p:real^3->B) (h:real^3->real^3) h' y r.
     smooth_manifold_atlas top atlas /\
     diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0) h h' /\
     ~(y = vec 0) /\ &0 < r /\ r < norm(h' y) /\
     mfd_param top atlas (ball(h' y,r)) p
     ==> ?r'. &0 < r' /\ r' < norm y /\ mfd_param top atlas (ball(y,r')) (p o h')`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dif") MP_TAC)) THEN
  STRIP_TAC THEN
  USE_THEN "dif" (LABEL_TAC "hh" o MATCH_MP P2ACM_DIFFEO_FACTS) THEN
  USE_THEN "dif" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `!b:real^3. b IN ball((h':real^3->real^3) y,r) ==> ~(b = vec 0)`
  (LABEL_TAC "bnz") THENL
   [X_GEN_TAC `b:real^3` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `dist((h':real^3->real^3) y,vec 0) < r` THEN
    REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t = {w:real^3 | w IN (:real^3) DELETE vec 0 /\
                              (h':real^3->real^3) w IN ball(h' y,r)}` THEN
  SUBGOAL_THEN `!w:real^3. w IN t <=> ~(w = vec 0) /\ (h':real^3->real^3) w IN ball(h' y,r)`
  (LABEL_TAC "tdef") THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM; IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `open(t:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3->bool) SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET; IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `ball((h':real^3->real^3) y,r) SUBSET (:real^3) DELETE vec 0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBSET; IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `diffeomorphism_on t (ball((h':real^3->real^3) y,r)) h' (h:real^3->real^3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[diffeomorphism_on; OPEN_BALL] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `b:real^3` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `(w:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        DISCH_TAC THEN EXISTS_TAC `(h:real^3->real^3) b` THEN
        SUBGOAL_THEN `~(b:real^3 = vec 0)` ASSUME_TAC THENL
         [USE_THEN "bnz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `~(b:real^3 = vec 0)` ASSUME_TAC THENL
         [USE_THEN "bnz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `(h':real^3->real^3) w` THEN
        ASM_SIMP_TAC[]];
      ASM_SIMP_TAC[];
      X_GEN_TAC `b:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(b:real^3 = vec 0)` ASSUME_TAC THENL
       [USE_THEN "bnz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas t ((p:real^3->B) o (h':real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`ball((h':real^3->real^3) y,r)`; `ball((h':real^3->real^3) y,r)`;
                          `h:real^3->real^3`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  UNDISCH_TAC `open(t:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  EXISTS_TAC `min d (norm(y:real^3) / &2)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `t:real^3->bool` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y:real^3,d)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* From a covering whose pullback is c times the pullback by h of            *)
(* (2 / |z|^2) delta, for a diffeomorphism h of real^3 minus the origin      *)
(* commuting with the twist, to                                              *)
(* the standard model p o h'.                                                *)
(* ------------------------------------------------------------------------- *)

let P2ACM_STD_FROM_DIFFEO = prove
 (`!top atlas (g:B->real^3^3) (p:real^3->B) (h:real^3->real^3) h' c.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ &0 < c /\
     diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0) h h' /\
     (!y. ~(y = vec 0) ==> h(rfs_twist y) = rfs_twist(h y)) /\
     IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     ((!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) \/
      (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y \/ z = rfs_twist y))) /\
     (!y. ~(y = vec 0)
          ==> rfs_pullback atlas p g y =
              c %% mpullback h (\z. (&2 / norm z pow 2) %% mat 1) y)
     ==> p2acm_std (top,atlas) g (p o h') c`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dif")
   (CONJUNCTS_THEN2 (LABEL_TAC "tw") (CONJUNCTS_THEN2 (LABEL_TAC "img")
   (CONJUNCTS_THEN2 (LABEL_TAC "loc") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (LABEL_TAC "pb"))))))))) THEN
  USE_THEN "dif" (LABEL_TAC "hh" o MATCH_MP P2ACM_DIFFEO_FACTS) THEN
  SUBGOAL_THEN `!a b:real^3. ~(a = vec 0) /\ ~(b = vec 0)
                             ==> ((h':real^3->real^3) a = h' b <=> a = b)`
  (LABEL_TAC "hinj") THENL
   [REPEAT STRIP_TAC THEN EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    DISCH_THEN(MP_TAC o AP_TERM `h:real^3->real^3`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. ~(z = vec 0) ==> h'(rfs_twist z) = rfs_twist(h' z)`
  (LABEL_TAC "tw'") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((h':real^3->real^3) z = vec 0) /\ (h:real^3->real^3) (h' z) = z`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "tw" (MP_TAC o SPEC `(h':real^3->real^3) z`) THEN
    REWRITE_TAC[ASSUME `~((h':real^3->real^3) z = vec 0)`;
                ASSUME `(h:real^3->real^3) (h' z) = z`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "hh" (fun th -> SIMP_TAC[th; P2ACM_TWIST_NZ;
                                      ASSUME `~((h':real^3->real^3) z = vec 0)`]);
    ALL_TAC] THEN
  REWRITE_TAC[p2acm_std] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the image *)
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (h':real^3->real^3) {y | ~(y = vec 0)} = {y | ~(y = vec 0)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN
      EQ_TAC THENL
       [STRIP_TAC THEN ASM_SIMP_TAC[];
        DISCH_TAC THEN EXISTS_TAC `(h:real^3->real^3) w` THEN ASM_SIMP_TAC[]];
      ASM_REWRITE_TAC[]];
    (* local parametrizations *)
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `(h':real^3->real^3) z`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC P2ACM_PARAM_PRECOMP THEN
    MAP_EVERY EXISTS_TAC [`h:real^3->real^3`; `r:real`] THEN ASM_REWRITE_TAC[];
    (* injective or twisted *)
    USE_THEN "inj" DISJ_CASES_TAC THENL
     [DISJ1_TAC THEN MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(h':real^3->real^3) a`; `(h':real^3->real^3) b`]) THEN
      ASM_SIMP_TAC[];
      DISJ2_TAC THEN MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN STRIP_TAC THEN
      REWRITE_TAC[o_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`(h':real^3->real^3) a`; `(h':real^3->real^3) b`]) THEN
      REMOVE_THEN "tw'" (fun th -> ASM_SIMP_TAC[GSYM th; P2ACM_TWIST_NZ])];
    (* the pullback *)
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((h':real^3->real^3) y = vec 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    USE_THEN "dif" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
    SUBGOAL_THEN `(h':real^3->real^3) differentiable at y` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^3->real^3) differentiable at ((h':real^3->real^3) y)` ASSUME_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `(:real^3) DELETE vec 0` THEN
      ASM_REWRITE_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) ((p:real^3->B) ((h':real^3->real^3) y))) o p)
      differentiable
      at (h' y)`
    ASSUME_TAC THENL
     [USE_THEN "loc" (MP_TAC o SPEC `(h':real^3->real^3) y`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `ball((h':real^3->real^3) y,r)`; `p:real^3->B`;
                     `(h':real^3->real^3) y`] APX_PARAM_LOCAL_REP) THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `N':real^3->bool`
        (X_CHOOSE_THEN `k:real^3->real^3` STRIP_ASSUME_TAC))) THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `N:real^3->bool` THEN
      ASM_MESON_TAC[diffeomorphism_on];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`; `p:real^3->B`;
                   `h':real^3->real^3`; `g:B->real^3^3`; `y:real^3`]
                  P2BX_RFS_PULLBACK_COMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `mpullback (h':real^3->real^3) (rfs_pullback atlas (p:real^3->B) g) y =
      mpullback h' (\w. c %% mpullback h (\z. (&2 / norm z pow 2) %% mat 1) w) y`
    SUBST1_TAC THENL
     [MATCH_MP_TAC P2ACM_MPULLBACK_PT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[P2ACM_MPULLBACK_CMUL; ETA_AX] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[P2BX_MPULLBACK_COMPOSE] THEN
    REWRITE_TAC[P2ACM_CYL0] THEN
    MP_TAC(ISPECL [`(h:real^3->real^3) o (h':real^3->real^3)`;
                   `(\z. (&2 / norm z pow 2) %% mat 1):real^3->real^3^3`;
                   `(:real^3) DELETE vec 0`; `y:real^3`] P2ACM_MPULLBACK_ID_LOCAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_DELETE; OPEN_UNIV; IN_DELETE; IN_UNIV; o_THM] THEN
      ASM_SIMP_TAC[];
      SIMP_TAC[]]]);;

(* The reduction: a slice lam cylinder_flow(t / lam) of a cylinder model is  *)
(* (lam - t) cylinder_flow 0 in the coordinates of the radial power map.     *)

let P2ACM_CYL_STD = prove
 (`!top atlas (g:B->real^3^3) (p:real^3->B) lam t.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     &0 < lam /\ t <= &0 /\
     IMAGE p {y:real^3 | ~(y = vec 0)} = topspace top /\
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p) /\
     ((!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y)) \/
      (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (p y = p z <=> z = y \/ z = rfs_twist y))) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas p g y = lam %% cylinder_flow (t / lam) y)
     ==> ?q. p2acm_std (top,atlas) g q (lam - t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPEC `t / lam` RFB_CYL_SETUP) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[REAL_LT_01] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(p:real^3->B) o
              (\y:real^3. ((norm y pow 2) rpow (--e / (&2 * e + &1))) % y)` THEN
  MATCH_MP_TAC P2ACM_STD_FROM_DIFFEO THEN
  EXISTS_TAC `\y:real^3. ((norm y pow 2) rpow e) % y` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[P2ACM_PW_TWIST];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[IN_DELETE; IN_UNIV; MATRIX_CMUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < lam` THEN CONV_TAC REAL_FIELD]);;

(* ========================================================================= *)
(* In the standard model with c >= 1/2 every unit ball contains a compact    *)
(* set of volume at least 1/40 (the image of a closed Euclidean ball         *)
(* cball(z0,rho), rho = |z0| / (4 sqrt(2c)), about a preimage z0 of the      *)
(* centre; q is injective on ball(z0,|z0|/2) because the twist reverses the  *)
(* direction of z0).                                                         *)
(* ========================================================================= *)

let P2ACM_BALL_NZ = prove
 (`!z0 a:real^3.
     ~(z0 = vec 0) /\ a IN ball(z0,norm z0 / &2)
     ==> &0 < a dot z0 /\ norm z0 / &2 < norm a /\ ~(a = vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL; dist] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(z0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(z0:real^3) / &2 < norm(a:real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`z0:real^3`; `a:real^3`] NORM_TRIANGLE_SUB) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `norm(z0:real^3) / &2 < norm(vec 0:real^3)` THEN
    REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `norm(z0 - a:real^3) * norm z0 < norm(z0:real^3) / &2 * norm z0` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`z0 - a:real^3`; `z0:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
  SUBGOAL_THEN `&0 < norm(z0:real^3) * norm z0` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DOT_LSUB; DOT_SQUARE_NORM; REAL_POW_2] THEN REAL_ARITH_TAC);;

let P2ACM_CBALL_NORM = prove
 (`!z0 y:real^3 rho.
     y IN cball(z0,rho) ==> norm z0 - rho <= norm y /\ norm y <= norm z0 + rho`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z0:real^3`; `y:real^3`] NORM_TRIANGLE_SUB) THEN
  MP_TAC(ISPECL [`y:real^3`; `z0:real^3`] NORM_TRIANGLE_SUB) THEN
  MP_TAC(ISPECL [`y:real^3`; `z0:real^3`] NORM_SUB) THEN
  ASM_REAL_ARITH_TAC);;

let P2ACM_CYL0_QF = prove
 (`!c (y:real^3) w.
     w dot ((c %% cylinder_flow (&0) y) ** w) = c * &2 / norm y pow 2 * (w dot w)`,
  REWRITE_TAC[P2ACM_CYL0; MATRIX_CMUL_ASSOC; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID;
              DOT_RMUL] THEN
  REAL_ARITH_TAC);;

(* q is injective near any point of real^3 minus the origin. *)

let P2ACM_STD_INJ_NEAR = prove
 (`!top atlas (g:B->real^3^3) q c z0 a b.
     p2acm_std (top,atlas) g q c /\ ~(z0 = vec 0) /\
     a IN ball(z0,norm z0 / &2) /\ b IN ball(z0,norm z0 / &2) /\ q a = q b
     ==> a = b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2acm_std] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`z0:real^3`; `a:real^3`] P2ACM_BALL_NZ) THEN
  MP_TAC(ISPECL [`z0:real^3`; `b:real^3`] P2ACM_BALL_NZ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3`; `b:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3`; `b:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    SUBGOAL_THEN `&0 < inv(norm(a:real^3) pow 2) * (a dot z0)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; NORM_POS_LT];
      ALL_TAC] THEN
    UNDISCH_TAC `&0 < b dot (z0:real^3)` THEN
    ASM_REWRITE_TAC[rfs_twist; DOT_LNEG; DOT_LMUL] THEN REAL_ARITH_TAC]);;

let P2ACM_STD_PARAM_NEAR = prove
 (`!top atlas (g:B->real^3^3) q c z0.
     smooth_manifold_atlas top atlas /\ p2acm_std (top,atlas) g q c /\ ~(z0 = vec 0)
     ==> mfd_param top atlas (ball(z0,norm z0 / &2)) q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MFP_PARAM_LOCAL THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2ACM_STD_INJ_NEAR THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `q:real^3->B`; `c:real`; `z0:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z0:real^3`; `w:real^3`] P2ACM_BALL_NZ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p2acm_std (top,atlas) (g:B->real^3^3) q c` THEN REWRITE_TAC[p2acm_std] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `ball(z0:real^3,norm z0 / &2)` OPEN_CONTAINS_BALL) THEN
  REWRITE_TAC[OPEN_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(w:real^3,min r d)` THEN
  REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(w:real^3,d)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(w:real^3,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC]);;

(* The arithmetic of the quadratic-form bound on cball(z0,rho). *)

let P2ACM_QF_ARITH = prove
 (`!c n rho y w2.
     &0 <= c /\ &0 < n - rho /\ n - rho <= y /\ &0 <= w2
     ==> c * &2 / y pow 2 * w2 <= (sqrt(&2 * c) / (n - rho)) pow 2 * w2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &2 * c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_POW_DIV; SQRT_POW_2] THEN
  SUBGOAL_THEN `inv(y pow 2) <= inv((n - rho) pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_POW_LE2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&2 * c * w2) * (inv((n - rho) pow 2) - inv(y pow 2))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* Points of cball(z0,rho) lie in the unit ball about q z0 when            *)
(* sqrt(2c) rho < |z0| - rho: the image of the straight segment.           *)

let P2ACM_STD_SEG_BALL = prove
 (`!top atlas (g:B->real^3^3) q c z0 rho z.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2acm_std (top,atlas) g q c /\ ~(z0 = vec 0) /\
     &0 < rho /\ rho <= norm z0 / &4 /\ sqrt(&2 * c) * rho < norm z0 - rho /\
     z IN cball(z0,rho)
     ==> q z IN mfd_ball (top,atlas) g (q z0) (&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o GEN_REWRITE_RULE I [p2acm_std]) THEN
  SUBGOAL_THEN `&0 < norm(z0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `D = ball(z0:real^3,norm z0 / &2)` THEN
  SUBGOAL_THEN `open(D:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param top atlas D (q:real^3->B)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC P2ACM_STD_PARAM_NEAR THEN
    MAP_EVERY EXISTS_TAC [`g:B->real^3^3`; `c:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(z0:real^3,rho) SUBSET D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN D ==> ~(y = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`z0:real^3`; `y:real^3`] P2ACM_BALL_NZ) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[z0:real^3,z] SUBSET cball(z0,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; CENTRE_IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (D:real^3->bool)`; `open_set_atlas (D:real^3->bool)`;
                 `D:real^3->bool`; `\x:real^3. x`; `z0:real^3`; `z:real^3`]
                GRGD_CHART_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "pt") (CONJUNCTS_THEN2 (LABEL_TAC "c1") (K ALL_TAC))) THEN
  (let seg = `\t. chart_inv (D:real^3->bool,(\x:real^3. x)) (z0 + t % (z - z0))` in
   let cyl = `\y:real^3. c %% cylinder_flow (&0) y` in
   MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                  `D:real^3->bool`; `q:real^3->B`; cyl; seg; `&0`; `&1`]
                 MFD_PARAM_C1_CURVE_LENGTH) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
     CONV_TAC SYM_CONV THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o check (fun th ->
       can (find_term ((=) `rfs_pullback:((B->bool)#(B->real^3)->bool)->(real^3->B)->(B->real^3^3)->real^3->real^3^3`)) (concl th))) THEN
     ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
     REWRITE_TAC[rfs_pullback];
     ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1M") (LABEL_TAC "len")) THEN
   MP_TAC(ISPECL [`subtopology euclidean (D:real^3->bool)`; `open_set_atlas (D:real^3->bool)`;
                  cyl; `D:real^3->bool`; `\x:real^3. x`; `z0:real^3`; `z:real^3`; `&0`;
                  `(sqrt(&2 * c) / (norm(z0:real^3) - rho)) pow 2`; `cball(z0:real^3,rho)`]
                 GRGD_SEGMENT_LENGTH_UPPER) THEN
   ANTS_TAC THENL
    [ASM_SIMP_TAC[OPEN_SET_ATLAS; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID] THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
       ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN REWRITE_TAC[ETA_AX] THEN
         ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01];
         ASM_SIMP_TAC[SUBSET; IN_DELETE; IN_UNIV]];
       ALL_TAC] THEN
     MAP_EVERY X_GEN_TAC [`y:real^3`; `v:real^3`] THEN DISCH_TAC THEN
     SUBGOAL_THEN `(y:real^3) IN D` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
     ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; P2ACM_CYL0_QF; DOT_SQUARE_NORM] THEN
     MP_TAC(ISPECL [`z0:real^3`; `y:real^3`; `rho:real`] P2ACM_CBALL_NORM) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
      [REWRITE_TAC[REAL_MUL_LZERO] THEN
       REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
       ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; NORM_POS_LE; REAL_LT_IMP_LE; REAL_POS] THEN
       REAL_ARITH_TAC;
       MATCH_MP_TAC P2ACM_QF_ARITH THEN ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE; REAL_LT_IMP_LE] THEN
       ASM_REAL_ARITH_TAC];
     ALL_TAC] THEN
   DISCH_TAC THEN
   USE_THEN "c1M" (MP_TAC o MATCH_MP MFD_C1_CURVE_JOINABLE) THEN
   MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                  mk_comb(mk_comb(`(o):(real^3->B)->(real->real^3)->real->B`, `q:real^3->B`), seg);
                  `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `chart_inv (D:real^3->bool,(\x:real^3. x)) (z0 + &0 % (z - z0)) = z0 /\
                 chart_inv (D:real^3->bool,(\x:real^3. x)) (z0 + &1 % (z - z0)) = z`
   STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [USE_THEN "pt" (MP_TAC o SPEC `&0`);
       USE_THEN "pt" (MP_TAC o SPEC `&1`)] THEN
     REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
     SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN VECTOR_ARITH_TAC;
     ALL_TAC] THEN
   ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN DISCH_TAC THEN
   REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `sqrt((sqrt(&2 * c) / (norm(z0:real^3) - rho)) pow 2) * dist(z0:real^3,z)` THEN
   CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 < norm(z0:real^3) - rho` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= sqrt(&2 * c) / (norm(z0:real^3) - rho)` ASSUME_TAC THENL
    [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
      [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
     ALL_TAC] THEN
   ASM_SIMP_TAC[POW_2_SQRT] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC `sqrt(&2 * c) / (norm(z0:real^3) - rho) * rho` THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `(z:real^3) IN cball(z0,rho)` THEN REWRITE_TAC[IN_CBALL];
     ASM_SIMP_TAC[REAL_FIELD `&0 < d ==> s / d * r = (s * r) / d`; REAL_LT_LDIV_EQ] THEN
     ASM_REAL_ARITH_TAC]));;

let P2ACM_QF_ARITH2 = prove
 (`!c n y w2.
     &0 <= c /\ &0 < y /\ y <= n /\ &0 <= w2
     ==> (&2 * c / n pow 2) * w2 <= c * &2 / y pow 2 * w2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv(n pow 2) <= inv(y pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_POW_LE2; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&2 * c * w2) * (inv(y pow 2) - inv(n pow 2))` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* The image of cball(z0,rho), rho <= |z0| / 4: compact, with volume at    *)
(* least (2c / (|z0| + rho)^2)^(3/2) (4/3) pi rho^3.                       *)

let P2ACM_STD_CBALL_VOL = prove
 (`!top atlas (g:B->real^3^3) q c z0 rho.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2acm_std (top,atlas) g q c /\ ~(z0 = vec 0) /\ &0 < rho /\ rho <= norm z0 / &4
     ==> compact_in top (IMAGE q (cball(z0,rho))) /\
         ?v. mfd_has_volume (top,atlas) g (IMAGE q (cball(z0,rho))) v /\
             sqrt((&2 * c / (norm z0 + rho) pow 2) pow 3) * (&4 / &3 * pi * rho pow 3) <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o GEN_REWRITE_RULE I [p2acm_std]) THEN
  SUBGOAL_THEN `&0 < norm(z0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `D = ball(z0:real^3,norm z0 / &2)` THEN
  SUBGOAL_THEN `mfd_param top atlas D (q:real^3->B)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC P2ACM_STD_PARAM_NEAR THEN
    MAP_EVERY EXISTS_TAC [`g:B->real^3^3`; `c:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cball(z0:real^3,rho) SUBSET D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN D ==> ~(y = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`z0:real^3`; `y:real^3`] P2ACM_BALL_NZ) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact_in top (IMAGE (q:real^3->B) (cball(z0,rho)))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology euclidean (D:real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `IMAGE (q:real^3->B) (cball(z0,rho))`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &2 * c / (norm(z0:real^3) + rho) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_has_volume (euclidean,open_set_atlas (:real^3))
      (\x:real^3. (&2 * c / (norm(z0:real^3) + rho) pow 2) %% mat 1) (cball(z0,rho))
      (sqrt((&2 * c / (norm z0 + rho) pow 2) pow 3) * (&4 / &3 * pi * rho pow 3))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                   `(\x:real^3. mat 1):real^3->real^3^3`; `cball(z0:real^3,rho)`;
                   `&4 / &3 * pi * rho pow 3`; `&2 * c / (norm(z0:real^3) + rho) pow 2`]
                  MFD_HAS_VOLUME_SCALE) THEN
    ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; DIMINDEX_3] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`(:real^3)`; `cball(z0:real^3,rho)`; `&4 / &3 * pi * rho pow 3`]
                  MFD_HAS_VOLUME_EUCLIDEAN) THEN
    REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV; GSYM open_set_atlas] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_CBALL; VOLUME_CBALL;
                 REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `q':B->real^3` o REWRITE_RULE[mfd_param] o
    check (fun th -> can (find_term ((=) `mfd_param:(B)topology->((B->bool)#(B->real^3)->bool)->(real^3->bool)->(real^3->B)->bool`)) (concl th))) THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `(\x:real^3. (&2 * c / (norm(z0:real^3) + rho) pow 2) %% mat 1):real^3->real^3^3`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `D:real^3->bool`; `IMAGE (q:real^3->B) D`; `q:real^3->B`; `q':B->real^3`;
                 `cball(z0:real^3,rho)`;
                 `sqrt((&2 * c / (norm(z0:real^3) + rho) pow 2) pow 3) *
                  (&4 / &3 * pi * rho pow 3)`;
                 `v:real`; `&1`] P2BC_VOLUME_PB_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GEOL_EUCLID_FACTS; REAL_POS] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_CMUL THEN ASM_REWRITE_TAC[GEOL_EUCLID_FACTS];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[SQRT_1; REAL_MUL_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mfd_pullback_metric (open_set_atlas (:real^3)) atlas (q:real^3->B) g y =
                rfs_pullback atlas q g y`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_pullback_metric; rfs_pullback; GEOL_EUCLID_FACTS] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[P2ACM_CYL0_QF] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID; DOT_RMUL] THEN
  MP_TAC(ISPECL [`z0:real^3`; `y:real^3`; `rho:real`] P2ACM_CBALL_NORM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2ACM_QF_ARITH2 THEN
  ASM_SIMP_TAC[DOT_POS_LE; REAL_LT_IMP_LE; NORM_POS_LT]);;

(* The arithmetic of the choice rho = |z0| / (4 sqrt(2c)). *)

let P2ACM_VOL_ARITH0 = prove
 (`!c n s rho.
     &1 <= s /\ s pow 2 = &2 * c /\ &0 < n /\ rho = n / (&4 * s)
     ==> &1 / &40 <= sqrt((&2 * c / (n + rho) pow 2) pow 3) * (&4 / &3 * pi * rho pow 3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rho /\ s * rho = n / &4 /\ rho <= n / &4` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < s ==> &0 < &4 * s`] THEN
      MP_TAC(SPECL [`n:real`; `&1`; `s:real`] REAL_LE_LMUL) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `rho = n / (&4 * s)` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `&2 * c / (n + rho) pow 2 = (s / (n + rho)) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_DIV] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((s / (n + rho)) pow 2) pow 3 = ((s / (n + rho)) pow 3) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < n + rho` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (s / (n + rho)) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[POW_2_SQRT] THEN
  SUBGOAL_THEN `(s / (n + rho)) pow 3 * (&4 / &3 * pi * rho pow 3) =
                &4 / &3 * pi * ((n / &4) / (n + rho)) pow 3`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `s * rho = n / &4`)] THEN
    REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN
    UNDISCH_TAC `&0 < n + rho` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &5 <= (n / &4) / (n + rho)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 / &5) pow 3 <= ((n / &4) / (n + rho)) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= pi` ASSUME_TAC THENL
   [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&3 * (&1 / &5) pow 3 <= pi * ((n / &4) / (n + rho)) pow 3` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* Unit balls of the standard model contain a compact set of volume at     *)
(* least 1/40 when c >= 1/2.                                               *)

let P2ACM_STD_BALL_VOL = prove
 (`!top atlas (g:B->real^3^3) q c x.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2acm_std (top,atlas) g q c /\ &1 / &2 <= c /\ x IN topspace top
     ==> ?K v. compact_in top K /\ K SUBSET mfd_ball (top,atlas) g x (&1) /\
               mfd_has_volume (top,atlas) g K v /\ &1 / &40 <= v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2acm_std]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:B` o MATCH_MP (SET_RULE
    `IMAGE (f:real^3->B) s = t ==> !y. y IN t ==> ?z. z IN s /\ f z = y`)) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM))) THEN
  SUBGOAL_THEN `&0 < norm(z0:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= sqrt(&2 * c) /\ sqrt(&2 * c) pow 2 = &2 * c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `rho = norm(z0:real^3) / (&4 * sqrt(&2 * c))` THEN
  SUBGOAL_THEN `&0 < rho /\ sqrt(&2 * c) * rho = norm(z0:real^3) / &4 /\ rho <= norm z0 / &4`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&1 <= sqrt(&2 * c)` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= s ==> &0 < &4 * s`] THEN
      MP_TAC(SPECL [`norm(z0:real^3)`; `&1`; `sqrt(&2 * c)`] REAL_LE_LMUL) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `q:real^3->B`; `c:real`; `z0:real^3`; `rho:real`] P2ACM_STD_CBALL_VOL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (q:real^3->B) (cball(z0,rho))`; `v:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2ACM_STD_SEG_BALL THEN
    MAP_EVERY EXISTS_TAC [`c:real`; `rho:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt((&2 * c / (norm(z0:real^3) + rho) pow 2) pow 3) *
                (&4 / &3 * pi * rho pow 3)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2ACM_VOL_ARITH0 THEN
    EXISTS_TAC `sqrt(&2 * c)` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "rho" THEN REWRITE_TAC[]]);;

(* The form used with LIM_VOL: every volume of the unit ball is >= 1/40.   *)

let P2ACM_STD_UNIT_BALL = prove
 (`!top atlas (g:B->real^3^3) q c x v.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2acm_std (top,atlas) g q c /\ &1 / &2 <= c /\ x IN topspace top /\
     mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x (&1)) v
     ==> &1 / &40 <= v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `q:real^3->B`; `c:real`; `x:B`] P2ACM_STD_BALL_VOL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:B->bool` (X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `w:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:B->real^3^3`; `K:B->bool`; `mfd_ball (top,atlas) (g:B->real^3^3) x (&1)`;
                 `w:real`; `v:real`] MFD_HAS_VOLUME_MONO) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* In the standard model, lengths of curves are at least sqrt(c) times the   *)
(* change of |apx_sval| (apx_sval z = sqrt 2 log|z| is the line coordinate   *)
(* of cylinder_flow 0, and |apx_sval| is invariant under the twist).  Local  *)
(* estimate by lifting through the injective parametrizations q on           *)
(* ball(z0,|z0|/2) (APX_SVAL_LENGTH_LOWER), globalized along [0,1] by        *)
(* CONNECTED_INDUCTION_SIMPLE.                                               *)
(* ========================================================================= *)

let P2ACM_SVAL_TWIST = prove
 (`!z:real^3. ~(z = vec 0) ==> apx_sval(rfs_twist z) = --(apx_sval z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[apx_sval] THEN
  SUBGOAL_THEN `&0 < norm(z:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(rfs_twist (z:real^3)) = inv(norm z)` SUBST1_TAC THENL
   [REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    UNDISCH_TAC `&0 < norm(z:real^3)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_INV] THEN REAL_ARITH_TAC);;

let P2ACM_STD_FVAL = prove
 (`!top atlas (g:B->real^3^3) q c z z'.
     p2acm_std (top,atlas) g q c /\ ~(z = vec 0) /\ ~(z' = vec 0) /\ q z = q z'
     ==> abs(apx_sval z) = abs(apx_sval z')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2acm_std] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`z:real^3`; `z':real^3`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[P2ACM_SVAL_TWIST; REAL_ABS_NEG]);;

(* The local estimate, for a curve inside one injective chart image. *)

let P2ACM_STD_LOCAL_LEN = prove
 (`!top atlas (g:B->real^3^3) q c z0 gamma x y z1 z2.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2acm_std (top,atlas) g q c /\ ~(z0 = vec 0) /\
     mfd_c1_curve (top,atlas) gamma x y /\
     (!t. x <= t /\ t <= y ==> gamma t IN IMAGE q (ball(z0,norm z0 / &2))) /\
     ~(z1 = vec 0) /\ q z1 = gamma x /\ ~(z2 = vec 0) /\ q z2 = gamma y
     ==> sqrt c * abs(abs(apx_sval z2) - abs(apx_sval z1)) <= mfd_length atlas g gamma x y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o GEN_REWRITE_RULE I [p2acm_std]) THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(z0:real^3,norm z0 / &2)) (q:real^3->B)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2ACM_STD_PARAM_NEAR THEN
    MAP_EVERY EXISTS_TAC [`g:B->real^3^3`; `c:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. w IN ball(z0,norm z0 / &2) ==> ~(w = vec 0)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`z0:real^3`; `w:real^3`] P2ACM_BALL_NZ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `ball(z0:real^3,norm z0 / &2)`; `q:real^3->B`; `gamma:real->B`;
                 `x:real`; `y:real`] MFD_PARAM_C1_CURVE_LIFT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:real->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x <= y` ASSUME_TAC THENL
   [ASM_MESON_TAC[mfd_c1_curve]; ALL_TAC] THEN
  SUBGOAL_THEN `(cc:real->real^3) x IN ball(z0,norm z0 / &2) /\ gamma x = (q:real^3->B)(cc x) /\
                cc y IN ball(z0,norm z0 / &2) /\ gamma y = q(cc y)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(apx_sval z1) = abs(apx_sval((cc:real->real^3) x)) /\
                abs(apx_sval z2) = abs(apx_sval(cc y))` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC P2ACM_STD_FVAL THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `q:real^3->B`; `c:real`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_length atlas (g:B->real^3^3) gamma x y =
                mfd_length atlas g ((q:real^3->B) o (cc:real->real^3)) x y` SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_LENGTH_EQ THEN REWRITE_TAC[IN_REAL_INTERVAL; o_THM] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `ball(z0:real^3,norm z0 / &2)`; `q:real^3->B`;
                 `\w:real^3. c %% cylinder_flow (&0) w`; `cc:real->real^3`; `x:real`; `y:real`]
                MFD_PARAM_C1_CURVE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_pullback")) (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[rfs_pullback];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `riemannian_metric (open_set_atlas (ball(z0:real^3,norm z0 / &2))) (cylinder_flow (&0))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RFB_OPEN_SET_RIEMANNIAN THEN REWRITE_TAC[OPEN_BALL] THEN
    MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `(:real^3) DELETE vec 0` THEN
    ASM_SIMP_TAC[RFB_CYL_METRIC_FIELD; REAL_LT_01; OPEN_BALL; SUBSET; IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (ball(z0:real^3,norm z0 / &2))`;
                 `open_set_atlas (ball(z0:real^3,norm z0 / &2))`; `cylinder_flow (&0)`;
                 `cc:real->real^3`; `x:real`; `y:real`; `c:real`] MFD_LENGTH_SCALE) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; OPEN_BALL; REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(apx_sval((cc:real->real^3) y) - apx_sval(cc x))` THEN
  REWRITE_TAC[REAL_ABS_SUB_ABS] THEN
  MATCH_MP_TAC APX_SVAL_LENGTH_LOWER THEN ASM_REWRITE_TAC[OPEN_BALL]);;

(* Every point of the model has a preimage; the value |apx_sval| at it. *)

let P2ACM_STD_PREIM = prove
 (`!top atlas (g:B->real^3^3) q c m.
     p2acm_std (top,atlas) g q c /\ m IN topspace top
     ==> ~((@z. ~(z = vec 0) /\ q z = m) = vec 0) /\ q(@z. ~(z = vec 0) /\ q z = m) = m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2acm_std] THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  UNDISCH_TAC `IMAGE (q:real^3->B) {y:real^3 | ~(y = vec 0)} = topspace top` THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `m:B`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The global estimate along a C^1 curve on [0,1]. *)

let P2ACM_STD_CURVE_LOWER = prove
 (`!top atlas (g:B->real^3^3) q c gamma z z'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2acm_std (top,atlas) g q c /\ mfd_c1_curve (top,atlas) gamma (&0) (&1) /\
     ~(z = vec 0) /\ q z = gamma(&0) /\ ~(z' = vec 0) /\ q z' = gamma(&1)
     ==> sqrt c * abs(abs(apx_sval z') - abs(apx_sval z)) <= mfd_length atlas g gamma (&0) (&1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `F0 = \m:B. abs(apx_sval(@w. ~(w = vec 0) /\ (q:real^3->B) w = m))` THEN
  SUBGOAL_THEN `!w:real^3. ~(w = vec 0) ==> (F0:B->real) (q w) = abs(apx_sval w)`
  (LABEL_TAC "F0") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN EXPAND_TAC "F0" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC P2ACM_STD_FVAL THEN
    MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                          `g:B->real^3^3`; `q:real^3->B`; `c:real`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `q:real^3->B`; `c:real`; `(q:real^3->B) w`] P2ACM_STD_PREIM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [p2acm_std]) THEN
      ASM SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN real_interval[&0,&1]
                    ==> ?w:real^3. ~(w = vec 0) /\ (q:real^3->B) w = gamma t`
  (LABEL_TAC "pre") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `q:real^3->B`; `c:real`; `(gamma:real->B) t`] P2ACM_STD_PREIM) THEN
    ASM_MESON_TAC[MFD_C1_CURVE_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u:real^1. u IN interval[lift(&0),lift(&1)]
               ==> !t. &0 <= t /\ t <= drop u
                       ==> sqrt c * abs((F0:B->real)(gamma t) - F0(gamma(&0))) <=
                           mfd_length atlas (g:B->real^3^3) gamma (&0) t`
  MP_TAC THENL
   [MP_TAC(ISPECL
     [`\u:real^1. !t. &0 <= t /\ t <= drop u
                      ==> sqrt c * abs((F0:B->real)(gamma t) - F0(gamma(&0))) <=
                          mfd_length atlas (g:B->real^3^3) gamma (&0) t`;
      `interval[lift(&0),lift(&1)]`] CONNECTED_INDUCTION_SIMPLE) THEN
    REWRITE_TAC[CONNECTED_INTERVAL] THEN ANTS_TAC THENL
     [ALL_TAC;
      DISCH_TAC THEN X_GEN_TAC `u:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`lift(&0)`; `u:real^1`]) THEN
      ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_LE_REFL; REAL_POS] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `t = &0` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_MUL_RZERO; mfd_length;
                  REAL_INTEGRAL_REFL; REAL_LE_REFL]] THEN
    X_GEN_TAC `a:real^1` THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    USE_THEN "pre" (MP_TAC o SPEC `drop a`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `wa:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `q:real^3->B`; `c:real`; `wa:real^3`] P2ACM_STD_PARAM_NEAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `open_in (subtopology euclideanreal (real_interval[&0,&1]))
        {t | t IN topspace(subtopology euclideanreal (real_interval[&0,&1])) /\
             (gamma:real->B) t IN IMAGE (q:real^3->B) (ball(wa,norm wa / &2))}`
    MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [mfd_c1_curve] o
        check (fun th -> can (find_term ((=) `gamma:real->B`)) (concl th) &&
                         can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_c1_curve"))
                             (concl th))) THEN
      REWRITE_TAC[continuous_map] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `oo:real->bool` STRIP_ASSUME_TAC o
      REWRITE_RULE[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; OPEN_IN_SUBTOPOLOGY;
                   GSYM REAL_OPEN_IN]) THEN
    SUBGOAL_THEN `(drop a) IN oo` ASSUME_TAC THENL
     [UNDISCH_TAC `{t | t IN real_interval[&0,&1] /\
                        (gamma:real->B) t IN IMAGE (q:real^3->B) (ball(wa,norm wa / &2))} =
                   oo INTER real_interval[&0,&1]` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `drop a`) THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `wa:real^3` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[NORM_POS_LT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `real_open (oo:real->bool)` THEN REWRITE_TAC[real_open] THEN
    DISCH_THEN(MP_TAC o SPEC `drop a`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `interval[lift(&0),lift(&1)] INTER ball(a:real^1,d)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
      ASM_REWRITE_TAC[IN_INTER; IN_INTERVAL_1; LIFT_DROP; CENTRE_IN_BALL];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[IN_INTER; IN_INTERVAL_1; LIFT_DROP; IN_BALL; DIST_REAL; GSYM drop] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (LABEL_TAC "Px"))) THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `t <= drop x` THENL
     [USE_THEN "Px" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* drop x < t <= drop y: the local estimate on [drop x,t] *)
    SUBGOAL_THEN `!s. drop x <= s /\ s <= t
                      ==> (gamma:real->B) s IN IMAGE (q:real^3->B) (ball(wa,norm wa / &2))`
    ASSUME_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      UNDISCH_TAC `{t | t IN real_interval[&0,&1] /\
                        (gamma:real->B) t IN IMAGE (q:real^3->B) (ball(wa,norm wa / &2))} =
                   oo INTER real_interval[&0,&1]` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real`) THEN
      SUBGOAL_THEN `s IN real_interval[&0,&1] /\ (s:real) IN oo` (fun th -> SIMP_TAC[th]) THEN
      CONJ_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `oo:real->bool`)) (concl th) && is_forall(concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `gamma:real->B`; `&0`; `drop x`; `&1`] MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `gamma:real->B`; `drop x`; `t:real`; `&1`] MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `gamma:real->B`; `&0`; `drop x`; `t:real`] MFD_LENGTH_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `gamma:real->B`; `&0`; `t:real`; `&1`] MFD_LENGTH_COMBINE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2 o CONJUNCT2) THEN
    USE_THEN "pre" (MP_TAC o SPEC `drop x`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `wx:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qwx"))) THEN
    USE_THEN "pre" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `wt:real^3` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qwt"))) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `q:real^3->B`; `c:real`; `wa:real^3`; `gamma:real->B`; `drop x`; `t:real`;
                   `wx:real^3`; `wt:real^3`] P2ACM_STD_LOCAL_LEN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "Px" (MP_TAC o SPEC `drop x`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "F0" (MP_TAC o SPEC `wx:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "F0" (MP_TAC o SPEC `wt:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    REMOVE_THEN "qwx" (SUBST_ALL_TAC o SYM) THEN
    REMOVE_THEN "qwt" (SUBST_ALL_TAC o SYM) THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && is_comb(lhand(concl th)) &&
      fst(strip_comb(lhand(concl th))) = `F0:B->real`))) THEN
    SUBGOAL_THEN `&0 <= sqrt c` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [p2acm_std]) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt c * (abs(abs(apx_sval wt) - abs(apx_sval wx)) +
                          abs(abs(apx_sval wx) - (F0:B->real)(gamma(&0))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `lift(&1)`) THEN
  REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; REAL_POS; REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(q:real^3->B) z = gamma(&0)`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(q:real^3->B) z' = gamma(&1)`)) THEN
  ASM_SIMP_TAC[]);;

(* ========================================================================= *)
(* Balls in the standard model grow at most linearly.  A ball of radius R    *)
(* about q z0 lies in the image of the shell exp(-K) <= |z| <= exp(K),       *)
(* K = |log|z0|| + R / sqrt(2c) (by the length estimate above); the          *)
(* shell is covered by 6 (N + 1) boxes, N <= 2K, each inside an open         *)
(* half-space on which q is injective (the twist reverses the sign of every  *)
(* coordinate), with image volume at most a constant depending only on c.    *)
(* ========================================================================= *)

(* Subadditivity of volume. *)

let P2ACM_VOL_UNION_LE = prove
 (`!top atlas (g:B->real^3^3) S1 S2 v w.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_has_volume (top,atlas) g S1 v /\ mfd_has_volume (top,atlas) g S2 w
     ==> ?u. mfd_has_volume (top,atlas) g (S1 UNION S2) u /\ u <= v + w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((B->bool)#(B->real^3))->bool) (S1:B->bool) /\
                mfd_lebesgue_measurable (top,atlas) (S2:B->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_HAS_INTEGRAL_IMP_MEASURABLE; mfd_has_volume]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_lebesgue_measurable (top,atlas:((B->bool)#(B->real^3))->bool)
                  ((S2:B->bool) DIFF S1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_LEBESGUE_MEASURABLE_DIFF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `(S2:B->bool) DIFF S1`; `S2:B->bool`; `w:real`] MFD_HAS_VOLUME_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `v + mfd_volume (top,atlas) (g:B->real^3^3) (S2 DIFF S1)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `(S1:B->bool) UNION S2 = S1 UNION (S2 DIFF S1)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MFD_HAS_VOLUME_UNION THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let P2ACM_VOL_UNIONS_LE = prove
 (`!top atlas (g:B->real^3^3) Fs.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ FINITE Fs /\
     (!K. K IN Fs ==> ?v. mfd_has_volume (top,atlas) g K v)
     ==> ?u. mfd_has_volume (top,atlas) g (UNIONS Fs) u /\
             u <= sum Fs (\K. mfd_volume (top,atlas) g K)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SPEC_TAC(`Fs:(B->bool)->bool`,`Fs:(B->bool)->bool`) THEN
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[UNIONS_0; SUM_CLAUSES; REAL_LE_REFL; MFD_HAS_VOLUME_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`K:B->bool`; `Fs:(B->bool)->bool`] THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?vk. mfd_has_volume (top,atlas) (g:B->real^3^3) K vk` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `K:B->bool`; `UNIONS Fs:B->bool`; `vk:real`; `u:real`] P2ACM_VOL_UNION_LE) THEN
  ASM_REWRITE_TAC[UNIONS_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u':real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u':real` THEN ASM_SIMP_TAC[SUM_CLAUSES] THEN
  SUBGOAL_THEN `mfd_volume (top,atlas) (g:B->real^3^3) K = vk` SUBST1_TAC THENL
   [MATCH_MP_TAC MFD_HAS_VOLUME_VOLUME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The boxes: a/4 <= s z_k <= 3a and |z_i| <= 3a, for s = 1 or s = -1. *)

let p2acm_box = new_definition
 `p2acm_box (a:real) (k:num) (s:real) =
    interval[(lambda i. if i = k then (if s = &1 then a / &4 else --(&3 * a))
                        else --(&3 * a)):real^3,
             (lambda i. if i = k then (if s = &1 then &3 * a else --(a / &4))
                        else &3 * a)]`;;

let P2ACM_IN_BOX = prove
 (`!a k s (z:real^3).
     1 <= k /\ k <= 3 /\ (s = &1 \/ s = --(&1))
     ==> (z IN p2acm_box a k s <=>
          a / &4 <= s * z$k /\ s * z$k <= &3 * a /\
          !i. 1 <= i /\ i <= 3 ==> abs(z$i) <= &3 * a)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    DISJ_CASES_TAC)) THEN
  ASM_SIMP_TAC[p2acm_box; IN_INTERVAL; LAMBDA_BETA; DIMINDEX_3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN EQ_TAC THEN STRIP_TAC THEN
  (REPEAT CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     X_GEN_TAC `i:num` THEN STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
     ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] ORELSE
   (X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC)));;

let P2ACM_BOX_FACTS = prove
 (`!a k s (z:real^3).
     &0 < a /\ 1 <= k /\ k <= 3 /\ (s = &1 \/ s = --(&1)) /\ z IN p2acm_box a k s
     ==> a / &4 <= s * z$k /\ a / &4 <= norm z /\ norm z <= &9 * a`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:real`; `k:num`; `s:real`; `z:real^3`] P2ACM_IN_BOX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z:real^3)$k)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `a / &4 <= s * (z:real^3)$k` THEN
      UNDISCH_TAC `s = &1 \/ s = --(&1)` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[COMPONENT_LE_NORM]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:3)) (\i. abs((z:real^3)$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
                            MP_TAC(SPEC `3` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC]);;

(* Every point with a <= |z| <= 3a lies in one of the six boxes of size a. *)

let P2ACM_BOX_COVER = prove
 (`!a (z:real^3).
     &0 < a /\ a <= norm z /\ norm z <= &3 * a
     ==> ?k s. 1 <= k /\ k <= 3 /\ (s = &1 \/ s = --(&1)) /\ z IN p2acm_box a k s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= 3 ==> abs((z:real^3)$i) <= &3 * a` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(z:real^3)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM; DIMINDEX_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= 3 /\ a / &3 <= abs((z:real^3)$k)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `z:real^3` NORM_LE_L1) THEN REWRITE_TAC[DIMINDEX_3; SUM_3] THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `a / &3 <= abs((z:real^3)$1)` THENL
     [EXISTS_TAC `1` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `a / &3 <= abs((z:real^3)$2)` THENL
     [EXISTS_TAC `2` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `3` THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((z:real^3)$k) <= &3 * a` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&3 * a`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `k:num` THEN ASM_CASES_TAC `&0 <= (z:real^3)$k` THENL
   [EXISTS_TAC `&1`; EXISTS_TAC `--(&1)`] THEN
  ASM_SIMP_TAC[P2ACM_IN_BOX] THEN ASM_REAL_ARITH_TAC);;

(* q is injective on the open half-space a/8 < s z_k, and parametrizes it. *)

let P2ACM_STD_HALF_PARAM = prove
 (`!top atlas (g:B->real^3^3) q c a k s.
     smooth_manifold_atlas top atlas /\ p2acm_std (top,atlas) g q c /\ &0 < a /\
     1 <= k /\ k <= 3 /\ (s = &1 \/ s = --(&1))
     ==> mfd_param top atlas {z:real^3 | a / &8 < s * z$k} q`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o GEN_REWRITE_RULE I [p2acm_std]) THEN
  SUBGOAL_THEN `!z:real^3. a / &8 < s * z$k ==> ~(z = vec 0)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `a / &8 < s * (vec 0:real^3)$k` THEN
    REWRITE_TAC[VEC_COMPONENT; REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open {z:real^3 | a / &8 < s * z$k}` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
      concl th = `s = &1 \/ s = --(&1)`)) THENL
     [REWRITE_TAC[REAL_MUL_LID; GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT];
      SUBGOAL_THEN `{z:real^3 | a / &8 < --(&1) * z$k} = {z | z$k < --(a / &8)}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MFP_PARAM_LOCAL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0) /\ ~(y:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `rfs_twist`)) (concl th))) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `y:real^3`]) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`; `y:real^3`]) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `a / &8 < s * (y:real^3)$k` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[rfs_twist; VECTOR_NEG_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SUBGOAL_THEN `&0 < inv(norm(x:real^3) pow 2)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_POW_LT; NORM_POS_LT]; ALL_TAC] THEN
      UNDISCH_TAC `a / &8 < s * (x:real^3)$k` THEN UNDISCH_TAC `&0 < a` THEN
      ABBREV_TAC `u = inv(norm(x:real^3) pow 2)` THEN
      ABBREV_TAC `xk = (x:real^3)$k` THEN
      REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `&0 < u * (s * xk)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `open {z:real^3 | a / &8 < s * z$k}` THEN
  GEN_REWRITE_TAC LAND_CONV [OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(w:real^3,min r d)` THEN
  REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(w:real^3,d)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(w:real^3,r)` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC]);;

(* Image volume of a box: at most a constant depending only on c. *)

let P2ACM_STD_BOX_VOL = prove
 (`!top atlas (g:B->real^3^3) q c a k s.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2acm_std (top,atlas) g q c /\ &0 < a /\ 1 <= k /\ k <= 3 /\ (s = &1 \/ s = --(&1))
     ==> ?v. mfd_has_volume (top,atlas) g (IMAGE q (p2acm_box a k s)) v /\
             v <= &31104 * pi * c * sqrt(&32 * c)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC o GEN_REWRITE_RULE I [p2acm_std]) THEN
  ABBREV_TAC `U = {z:real^3 | a / &8 < s * z$k}` THEN
  SUBGOAL_THEN `mfd_param top atlas U (q:real^3->B)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN MATCH_MP_TAC P2ACM_STD_HALF_PARAM THEN
    MAP_EVERY EXISTS_TAC [`g:B->real^3^3`; `c:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2acm_box a k s SUBSET (U:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_TAC THEN MP_TAC(SPECL [`a:real`; `k:num`; `s:real`; `z:real^3`] P2ACM_BOX_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':B->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact_in top (IMAGE (q:real^3->B) (p2acm_box a k s))` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `subtopology euclidean (U:real^3->bool)` THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; p2acm_box; COMPACT_INTERVAL] THEN
    ASM_REWRITE_TAC[GSYM p2acm_box];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `IMAGE (q:real^3->B) (p2acm_box a k s)`] MFD_HAS_VOLUME_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real`) THEN
  EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `q':B->real^3` o REWRITE_RULE[mfd_param] o check (fun th ->
    can (find_term ((=) `U:real^3->bool`)) (concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "mfd_param")) (concl th))) THEN
  SUBGOAL_THEN `measurable(p2acm_box a k s) /\
                measure(p2acm_box a k s) <= &972 * pi * a pow 3` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `measurable(p2acm_box a k s)` ASSUME_TAC THENL
     [REWRITE_TAC[p2acm_box; MEASURABLE_INTERVAL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(cball(vec 0:real^3,&9 * a))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_SUBSET THEN ASM_REWRITE_TAC[MEASURABLE_CBALL] THEN
      REWRITE_TAC[SUBSET; IN_CBALL_0] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`a:real`; `k:num`; `s:real`; `z:real^3`] P2ACM_BOX_FACTS) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[VOLUME_CBALL; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`euclidean:(real^3)topology`; `open_set_atlas (:real^3)`;
                 `(\x:real^3. mat 1):real^3->real^3^3`;
                 `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `U:real^3->bool`; `IMAGE (q:real^3->B) U`; `q:real^3->B`; `q':B->real^3`;
                 `p2acm_box a k s`; `measure(p2acm_box a k s)`; `v:real`;
                 `&32 * c / a pow 2`] P2BC_VOLUME_PB_COMPARE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GEOL_EUCLID_FACTS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
      MP_TAC(ISPECL [`(:real^3)`; `p2acm_box a k s`; `measure(p2acm_box a k s)`]
                    MFD_HAS_VOLUME_EUCLIDEAN) THEN
      REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBTOPOLOGY_UNIV; GSYM open_set_atlas] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `mfd_pullback_metric (open_set_atlas (:real^3)) atlas (q:real^3->B) g y =
                  rfs_pullback atlas q g y` SUBST1_TAC THENL
     [REWRITE_TAC[mfd_pullback_metric; rfs_pullback; GEOL_EUCLID_FACTS] THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID; IN_UNIV];
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `k:num`; `s:real`; `y:real^3`] P2ACM_BOX_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `a / &4 <= norm(vec 0:real^3)` THEN
      REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[P2ACM_CYL0_QF] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
    SUBGOAL_THEN `&2 / norm(y:real^3) pow 2 <= &32 / a pow 2` MP_TAC THENL
     [REWRITE_TAC[real_div] THEN
      SUBGOAL_THEN `inv(norm(y:real^3) pow 2) <= inv((a / &4) pow 2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_DIV; REAL_INV_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= c * (w dot (w:real^3))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[DOT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&32 / a pow 2 - &2 / norm(y:real^3) pow 2) * (c * (w dot (w:real^3))) >= &0`
    MP_TAC THENL
     [REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&32 * c / a pow 2) * sqrt(&32 * c / a pow 2) * measure(p2acm_box a k s)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &32 * c / a pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&32 * c / a pow 2) * sqrt(&32 * c / a pow 2) * (&972 * pi * a pow 3)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `sqrt(&32 * c / a pow 2) = sqrt(&32 * c) / a` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ARITH `&32 * c / a pow 2 = (&32 * c) / a pow 2`] THEN
      ASM_SIMP_TAC[SQRT_DIV; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE; REAL_POW_LE;
                   POW_2_SQRT];
      ALL_TAC] THEN
    UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD]);;

(* The shell exp(-K) < |w| < exp(K) lies in the union of the boxes of the    *)
(* sizes exp(-K) exp(n), n <= N, once 2K < N + 1.                            *)

let P2ACM_SHELL_IN_BOXES = prove
 (`!K N (w:real^3).
     &0 <= K /\ &2 * K < &N + &1 /\ exp(--K) < norm w /\ norm w < exp K
     ==> ?n k s. n <= N /\ 1 <= k /\ k <= 3 /\ (s = &1 \/ s = --(&1)) /\
                 w IN p2acm_box (exp(--K) * exp(&n)) k s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. norm(w:real^3) <= exp(--K) * exp(&(n + 1))` MP_TAC THENL
   [EXISTS_TAC `N:num` THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp K` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE; GSYM REAL_OF_NUM_ADD] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min"))) THEN
  SUBGOAL_THEN `(n:num) <= N` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~((N:num) < n) ==> n <= N`) THEN DISCH_TAC THEN
    REMOVE_THEN "min" (MP_TAC o SPEC `N:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `exp K` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_EXP_ADD; REAL_EXP_MONO_LE; GSYM REAL_OF_NUM_ADD] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(--K) * exp(&n) <= norm(w:real^3)` ASSUME_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[REAL_EXP_0; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o MATCH_MP (MESON[num_CASES; ADD1]
      `~(n = 0) ==> ?m. n = m + 1`)) THEN
    REMOVE_THEN "min" (MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[ARITH_RULE `m < m + 1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`exp(--K) * exp(&n)`; `w:real^3`] P2ACM_BOX_COVER) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(--K) * exp(&(n + 1))` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_EXP_ADD] THEN
    SUBGOAL_THEN `&0 <= (exp(--K) * exp(&n)) * (&3 - exp(&1))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_MUL; REAL_EXP_POS_LT] THEN
      MP_TAC E_APPROX_32 THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `k:num`; `s:real`] THEN ASM_REWRITE_TAC[]]);;

(* Linear volume growth of balls in the standard model. *)

let P2ACM_STD_BALL_UPPER = prove
 (`!top atlas (g:B->real^3^3) q c x.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     p2acm_std (top,atlas) g q c /\ x IN topspace top
     ==> ?A B. !R v. &0 < R /\ mfd_has_volume (top,atlas) g (mfd_ball (top,atlas) g x R) v
                     ==> v <= A * R + B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `q:real^3->B`; `c:real`; `x:B`] P2ACM_STD_PREIM) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z0 = @z:real^3. ~(z = vec 0) /\ (q:real^3->B) z = x` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2acm_std]; ALL_TAC] THEN
  ABBREV_TAC `C1 = &31104 * pi * c * sqrt(&32 * c)` THEN
  SUBGOAL_THEN `&0 <= C1` ASSUME_TAC THENL
   [EXPAND_TAC "C1" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; PI_POS_LE; REAL_LT_IMP_LE; SQRT_POS_LE; REAL_LE_MUL];
    ALL_TAC] THEN
  ABBREV_TAC `L0 = abs(log(norm(z0:real^3)))` THEN
  SUBGOAL_THEN `&0 < sqrt(&2) * sqrt c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&12 * C1 / (sqrt(&2) * sqrt c)`; `&6 * C1 * (&2 * L0 + &2)`] THEN
  MAP_EVERY X_GEN_TAC [`R:real`; `v:real`] THEN STRIP_TAC THEN
  ABBREV_TAC `K = L0 + R / (sqrt(&2) * sqrt c)` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN EXPAND_TAC "L0" THEN
    MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&2 * K` FLOOR_POS) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN `&N <= &2 * K /\ &2 * K < &N + &1` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&2 * K` FLOOR) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Ix = {n:num | n <= N} CROSS ({1,2,3} CROSS {&1,--(&1)})` THEN
  ABBREV_TAC `box = \i:num#num#real. IMAGE (q:real^3->B)
                      (p2acm_box (exp(--K) * exp(&(FST i))) (FST(SND i)) (SND(SND i)))` THEN
  SUBGOAL_THEN `FINITE(Ix:num#num#real->bool) /\ CARD Ix = (N + 1) * 3 * 2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ix" THEN
    SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LE; FINITE_INSERT; FINITE_EMPTY; CARD_CROSS;
             CARD_NUMSEG_LE; CARD_CLAUSES; IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i:num#num#real. i IN Ix
                    ==> 1 <= FST(SND i) /\ FST(SND i) <= 3 /\
                        (SND(SND i) = &1 \/ SND(SND i) = --(&1)) /\ FST i <= N`
  ASSUME_TAC THENL
   [EXPAND_TAC "Ix" THEN REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; IN_INSERT;
                                    NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i:num#num#real. i IN Ix
                    ==> ?w. mfd_has_volume (top,atlas) (g:B->real^3^3)
                              ((box:num#num#real->B->bool) i) w /\ w <= C1`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num#num#real` THEN DISCH_TAC THEN EXPAND_TAC "box" THEN EXPAND_TAC "C1" THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC P2ACM_STD_BOX_VOL THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `IMAGE (box:num#num#real->B->bool) Ix`] P2ACM_VOL_UNIONS_LE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `sum (IMAGE (box:num#num#real->B->bool) Ix) (\K. mfd_volume (top,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) K)
                <= &((N + 1) * 3 * 2) * C1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (Ix:num#num#real->bool) ((\K. mfd_volume (top,atlas) (g:B->real^3^3) K) o box)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_IMAGE_LE THEN ASM_REWRITE_TAC[o_THM] THEN
      X_GEN_TAC `i:num#num#real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num#num#real` o check (fun th ->
        can (find_term ((=) `C1:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
      ASM_MESON_TAC[MFD_HAS_VOLUME_VOLUME; MFD_HAS_VOLUME_POS_LE];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `CARD(Ix:num#num#real->bool) = (N + 1) * 3 * 2`)) THEN
      ASM_SIMP_TAC[GSYM SUM_CONST] THEN MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[o_THM] THEN
      X_GEN_TAC `i:num#num#real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num#num#real` o check (fun th ->
        can (find_term ((=) `C1:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
      ASM_MESON_TAC[MFD_HAS_VOLUME_VOLUME]];
    ALL_TAC] THEN
  (* the ball lies in the union of the boxes *)
  SUBGOAL_THEN `mfd_ball (top,atlas) (g:B->real^3^3) x R SUBSET
                UNIONS (IMAGE (box:num#num#real->B->bool) Ix)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `m:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(m:B) IN topspace top` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `g:B->real^3^3`; `x:B`; `R:real`] MFD_BALL_OPEN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `q:real^3->B`; `c:real`; `m:B`] P2ACM_STD_PREIM) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `w = @z:real^3. ~(z = vec 0) /\ (q:real^3->B) z = m` THEN STRIP_TAC THEN
    UNDISCH_TAC `(m:B) IN mfd_ball (top,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) x R` THEN
    REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sqrt c * abs(abs(apx_sval w) - abs(apx_sval z0)) <=
                  mfd_dist (top,atlas) (g:B->real^3^3) x m` ASSUME_TAC THENL
     [MATCH_MP_TAC APX_DIST_GE_CURVES THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `gam:real->B` THEN STRIP_TAC THEN
      MATCH_MP_TAC P2ACM_STD_CURVE_LOWER THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `q:real^3->B`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(log(norm(w:real^3))) < K` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < sqrt(&2) /\ &0 < sqrt c` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
      SUBGOAL_THEN `abs(apx_sval w) = sqrt(&2) * abs(log(norm(w:real^3))) /\
                    abs(apx_sval z0) = sqrt(&2) * abs(log(norm(z0:real^3)))`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[apx_sval; REAL_ABS_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`];
        ALL_TAC] THEN
      SUBGOAL_THEN `(sqrt(&2) * sqrt c) * (abs(log(norm(w:real^3))) - L0) < R` ASSUME_TAC THENL
       [EXPAND_TAC "L0" THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `mfd_dist (top,atlas) (g:B->real^3^3) x m` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `sqrt c * abs(abs(apx_sval w) - abs(apx_sval z0))` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * d = b * a * d`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "K" THEN
      SUBGOAL_THEN `&0 < sqrt(&2) * sqrt c` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x - l < y ==> x < l + y`) THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `exp(--K) < norm(w:real^3) /\ norm w < exp K` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `norm(w:real^3) = exp(log(norm w))` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN ASM_REWRITE_TAC[NORM_POS_LT];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`K:real`; `N:num`; `w:real^3`] P2ACM_SHELL_IN_BOXES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `s:real`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN EXISTS_TAC `(n:num,k:num,s:real)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "Ix" THEN REWRITE_TAC[IN_CROSS; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      EXPAND_TAC "box" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:real^3` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `v <= u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:B->real^3^3`; `mfd_ball (top,atlas) (g:B->real^3^3) x R`;
                   `UNIONS (IMAGE (box:num#num#real->B->bool) Ix)`; `v:real`; `u:real`]
                  MFD_HAS_VOLUME_MONO) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&((N + 1) * 3 * 2) * C1 <= &12 * C1 / (sqrt(&2) * sqrt c) * R +
                &6 * C1 * (&2 * L0 + &2)` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `&N <= &2 * L0 + &2 * R / (sqrt(&2) * sqrt c)` MP_TAC THENL
     [UNDISCH_TAC `&N <= &2 * K` THEN EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&2 * L0 + &2 * R / (sqrt(&2) * sqrt c) - &N) * C1 >= &0` MP_TAC THENL
     [REWRITE_TAC[real_ge] THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

