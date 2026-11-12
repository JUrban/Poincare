(* ========================================================================= *)
(* pc_p2b_x1: X1 = P2B_SPLIT_CYL_STATEMENT in route form,                    *)
(* P2B_SPLIT_CYL_ROUTE |- !w. P2B_SPLIT_CYL_ROUTE_STATEMENT w                *)
(* (SPLIT_ROUND ==> SPLIT_CYL).  The double cover is transported into B      *)
(* along an injection B#bool -> B.                                           *)
(* Route: at every time t <= s0 the slices are locally split and R > 0      *)
(* (RFA_P2B_REQ_SMP_SPLIT_PT); the shifted flow g(t + s0) is in the class   *)
(* on t < 0 and smooth up to 0; a global parallel unit field of g(s0) is    *)
(* parallel at all earlier times (P2BX0_SECMIN_ZERO_ALL,                     *)
(* P2BX0_GSPLIT_FROM_KER); SPLIT_ROUND and P2BX2_MODEL_AT_ZERO give the      *)
(* model.  Without a global field: the double cover of the line field.      *)
(* ========================================================================= *)

needs "src/pc_p2b_shrinkcl.ml";;
needs "src/pc_p2b_x2.ml";;
needs "src/pc_rfa_splitend.ml";;
needs "src/pc_pde_gauge.ml";;
needs "src/pc_p2b_parons.ml";;
needs "src/pc_smt_orient.ml";;
needs "src/pc_mfd_transport.ml";;
needs "src/pc_mfd_lift.ml";;
needs "src/pc_p2b_kglob.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The shifted flow, R > 0 everywhere, and the case of a global parallel     *)
(* unit field at the zero-plane time.                                        *)
(* ------------------------------------------------------------------------- *)

let P2BX1_DERIV_SHIFT = prove
 (`!(f:real->real) d c s.
     ((\t. f(t + c)) has_real_derivative d) (atreal s)
     ==> (f has_real_derivative d) (atreal (s + c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `f = (\t. (f:real->real)(t + c)) o (\u. u - c)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; REAL_SUB_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `d = d * &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_DIFF_CHAIN_ATREAL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&1 = &1 - &0` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_SUB THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ID; HAS_REAL_DERIVATIVE_CONST];
    ASM_REWRITE_TAC[REAL_ARITH `(s + c) - c = s`]]);;

(* The flow shifted by s0 < b is in the class on t < 0, smooth up to 0. *)

let P2BX1_SHIFT_CLASS = prove
 (`!kappa top atlas (g:real->B->real^3^3) b s0.
     p2b_ancflow0 kappa (top,atlas) g b /\ s0 < b
     ==> p2b_ancflow0 kappa (top,atlas) (\t. g(t + s0)) (&0) /\
         (!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0) (\t. g(t + s0))) /\
         (!s x u v. s <= &0 /\ x IN topspace top /\ ~collinear {vec 0,u,v}
                    ==> &0 <= mfd_sectional atlas (g(s + s0)) x u v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_ancflow0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "cp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "nf")
    (CONJUNCTS_THEN2 (LABEL_TAC "dr") (LABEL_TAC "kn"))))))))))
    ASSUME_TAC) THEN
  SUBGOAL_THEN `!a. a < &0 ==> rfs_flow_upto (top,atlas) a (&0)
                                 (\t. (g:real->B->real^3^3)(t + s0))`
  (LABEL_TAC "upto") THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\t. (g:real->B->real^3^3)(t + s0)) = (\t. g(s0 + t))` SUBST1_TAC THENL
     [ABS_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2BX0_FLOW_UPTO_SHIFT THEN
    MAP_EVERY EXISTS_TAC [`s0 + a - &1`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [USE_THEN "rf" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `a:real` THEN DISCH_TAC THEN
    USE_THEN "upto" (MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; SIMP_TAC[rfs_flow_upto]];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "cp" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN USE_THEN "nf" MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `x:B`; `dR:real`] THEN STRIP_TAC THEN
    USE_THEN "dr" MATCH_MP_TAC THEN MAP_EVERY EXISTS_TAC [`s + s0:real`; `x:B`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`\t. mfd_scalar atlas ((g:real->B->real^3^3) t) x`; `dR:real`;
                   `s0:real`; `s:real`] P2BX1_DERIV_SHIFT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC P2BX2_KNC_VIEW_MONO THEN MATCH_MP_TAC P2BSK_KNC_SHIFT THEN
    EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* No sectional curvature at a point: abs Rm = 0 there. *)

let P2BX1_RM_NORM_ZERO = prove
 (`!(atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) y.
     (!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas g y u v = &0)
     ==> mfd_rm_norm atlas g y = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm] THEN
  SUBGOAL_THEN `{abs(mfd_sectional atlas (g:B->real^3^3) y u v) | u,v | ~collinear {vec 0,u,v}} =
                {&0}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `r:real` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[REAL_ABS_0];
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(SPEC `basis 1:real^3` P2BX0_NONCOLLINEAR_EXISTS) THEN
      SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
      DISCH_THEN(X_CHOOSE_TAC `u:real^3`) THEN
      MAP_EVERY EXISTS_TAC [`u:real^3`; `basis 1:real^3`] THEN ASM_SIMP_TAC[REAL_ABS_0]];
    REWRITE_TAC[SUP_SING]]);;

(* In the class the scalar curvature is positive everywhere at every time:   *)
(* R(x,t) = 0 would make the slice g(t) flat (SMP, part (ii)), against the   *)
(* non-flatness of the class at time t.                                      *)

let P2BX1_SCALAR_POS = prove
 (`!kappa top atlas (g:real->B->real^3^3) b t x.
     p2b_ancflow0 kappa (top,atlas) g b /\ t < b /\ x IN topspace top
     ==> &0 < mfd_scalar atlas (g t) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`; `t:real`] P2BX1_SHIFT_CLASS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "sec0"))) THEN
  MP_TAC(REWRITE_RULE[p2b_ancflow0] (ASSUME
    `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "cp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "nf")
    (CONJUNCTS_THEN2 (LABEL_TAC "dr") (LABEL_TAC "kn")))))))))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) t)` STRIP_ASSUME_TAC THENL
   [USE_THEN "upto" (MP_TAC o SPEC `--(&1)`) THEN
    REWRITE_TAC[REAL_ARITH `--(&1) < &0`; rfs_flow_upto; ricci_flow_on; REAL_ADD_LID] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  (* R >= 2 abs Rm >= 0 *)
  SUBGOAL_THEN `!y. y IN topspace top
                    ==> &0 <= mfd_rm_norm atlas ((g:real->B->real^3^3) t) y /\
                        mfd_rm_norm atlas (g t) y <= mfd_scalar atlas (g t) y / &2`
  (LABEL_TAC "half") THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `(g:real->B->real^3^3) t`; `y:B`] P2AU_MFD_SCALAR_ABS_3) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC P2BX0_RM_NORM_LE_HALF_SCALAR THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `mfd_scalar atlas ((g:real->B->real^3^3) t) x = &0` THENL
   [ALL_TAC;
    USE_THEN "half" (MP_TAC o SPEC `x:B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]] THEN
  (* R(x,t) = 0: the slice g(t) is flat *)
  SUBGOAL_THEN `!y u v. y IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> mfd_sectional atlas ((g:real->B->real^3^3) t) y u v = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `\u. (g:real->B->real^3^3)(u + t)`; `--(&1)`; `&0`; `x:B`; `&0`]
          (REWRITE_RULE[P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT]
                       (ISPEC `UNIV:B->bool` RFA_P2B_REQ_SMP_SPLIT_PT))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `--(&1) < &0`; REAL_LE_REFL] THEN CONJ_TAC THENL
       [USE_THEN "upto" MATCH_MP_TAC THEN REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN USE_THEN "sec0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[REAL_ADD_LID] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&0`; `y:B`; `u:real^3`; `v:real^3`]) THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; REAL_LE_REFL; REAL_ARITH `--(&1) < &0`];
    ALL_TAC] THEN
  USE_THEN "nf" (MP_TAC o SPEC `t:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) t`; `y:B`]
                P2BX1_RM_NORM_ZERO) THEN
  ANTS_TAC THENL [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                  ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A global parallel unit field of g(s0) gives the cylinder model of g(t +   *)
(* s0).  The shifted flow is in the class on t < 0 and smooth up to 0;       *)
(* sec_min = 0 and R > 0 at all times t <= 0; the field is parallel at all   *)
(* earlier times (P2BX0_GSPLIT_FROM_KER); SPLIT_ROUND (b = 0) and            *)
(* P2BX2_MODEL_AT_ZERO.                                                      *)
(* ------------------------------------------------------------------------- *)

let P2BX1_ORIENTABLE_CASE0 = prove
 (`!w:B->bool.
     P2B_SPLIT_ROUND_STATEMENT w
     ==> !kappa top atlas (g:real->B->real^3^3) b s0 X.
           p2b_ancflow0 kappa (top,atlas) g b /\ p2b_lorient top atlas /\ s0 < b /\
           p2b_parallel_on atlas (g s0) (topspace top) X /\
           (!y. y IN topspace top ==> X y dot (g s0 y ** X y) = &1)
           ==> p2b_cyl_model (top,atlas) (\t. g(t + s0))`,
  GEN_TAC THEN REWRITE_TAC[P2B_SPLIT_ROUND_STATEMENT] THEN DISCH_THEN(LABEL_TAC "sr") THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`; `s0:real`; `X:B->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`; `s0:real`] P2BX1_SHIFT_CLASS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "sec0"))) THEN
  SUBGOAL_THEN `connected_space (top:B topology) /\ ~(topspace top = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b` THEN
    SIMP_TAC[p2b_ancflow0];
    ALL_TAC] THEN
  (* sec_min = 0 at all times t <= 0 of the shifted flow *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\t. (g:real->B->real^3^3)(t + s0)`; `X:B->real^3`] P2BX0_SECMIN_ZERO_ALL) THEN
  REWRITE_TAC[REAL_ADD_LID] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* R > 0 at all times t <= 0 of the shifted flow *)
  SUBGOAL_THEN `!t x. t <= &0 /\ x IN topspace top
                      ==> &0 < mfd_scalar atlas ((g:real->B->real^3^3)(t + s0)) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX1_SCALAR_POS THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `top:B topology`; `b:real`] THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the field is parallel for every earlier slice *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\t. (g:real->B->real^3^3)(t + s0)`; `X:B->real^3`] P2BX0_GSPLIT_FROM_KER) THEN
  REWRITE_TAC[REAL_ADD_LID] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `p2b_gsplit (top,atlas) (\t. (g:real->B->real^3^3)(t + s0)) {s | s < &0} X`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_gsplit (top,atlas) (\t. (g:real->B->real^3^3)(t + s0)) {s | s <= &0} X` THEN
    REWRITE_TAC[p2b_gsplit; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* SPLIT_ROUND with b = 0, then the end time *)
  USE_THEN "sr" (MP_TAC o SPECL [`kappa:real`; `top:B topology`;
                                 `atlas:((B->bool)#(B->real^3))->bool`;
                                 `\t. (g:real->B->real^3^3)(t + s0)`; `&0`; `X:B->real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC P2BX2_MODEL_AT_ZERO THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_cyl_model")) (concl th))) THEN
  REWRITE_TAC[]);;

(* The same with the class of the route (p2b_ksep contains p2b_lorient). *)

let P2BX1_ORIENTABLE_CASE = prove
 (`!w:B->bool.
     P2B_SPLIT_ROUND_STATEMENT w
     ==> !kappa top atlas (g:real->B->real^3^3) b s0 X.
           p2b_ancflow kappa (top,atlas) g b /\ s0 < b /\
           p2b_parallel_on atlas (g s0) (topspace top) X /\
           (!y. y IN topspace top ==> X y dot (g s0 y ** X y) = &1)
           ==> p2b_cyl_model (top,atlas) (\t. g(t + s0))`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP P2BX1_ORIENTABLE_CASE0) THEN
  REWRITE_TAC[p2b_ancflow; p2b_ksep] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`kappa:real`; `b:real`; `X:B->real^3`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Two unit parallel fields of a metric field with nonzero scalar curvature  *)
(* at one point of a connected open set agree up to one sign on the whole    *)
(* set.  Their inner product is constant (metric compatibility of the        *)
(* Christoffel symbols); the orthogonal part Z = W - c V at the point is     *)
(* killed by the curvature, and a second parallel direction would kill all   *)
(* of it (R = 0); |Z|^2 = 1 - c^2 is constant, so Z = 0 everywhere and c =   *)
(* +-1.                                                                      *)
(* ------------------------------------------------------------------------- *)

let P2BX1_PAR_DOT_DERIV = prove
 (`!U (G:real^N->real^N^N) V W y.
     metric_field U G /\ y IN U /\ smooth_map_on U V /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative V (at z) w + christoffel G z w (V z) = vec 0) /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0)
     ==> ((\z. lift(V z dot (G z ** W z))) has_derivative (\w. vec 0)) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (U:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^N->real^N^N`;
                 `frechet_derivative ((vectorize:real^N^N->real^(N,N)finite_prod) o
                                      (G:real^N->real^N^N)) (at (y:real^N))`;
                 `V:real^N->real^N`; `frechet_derivative (V:real^N->real^N) (at y)`;
                 `W:real^N->real^N`; `frechet_derivative (W:real^N->real^N) (at y)`; `y:real^N`]
                LRG_HAS_DERIVATIVE_DOT_MATVEC) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[LRG_METRIC_FIELD_DIFF];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      ASM_MESON_TAC[LRG_SMOOTH_FRECHET_DIFFERENTIABLE];
      REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
      ASM_MESON_TAC[LRG_SMOOTH_FRECHET_DIFFERENTIABLE]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `(f:real^N->real^1) = g ==> (h has_derivative f) net
                                                  ==> (h has_derivative g) net`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `w:real^N` THEN
  REWRITE_TAC[GSYM mderiv] THEN
  SUBGOAL_THEN `frechet_derivative (V:real^N->real^N) (at y) w = --(christoffel G y w (V y)) /\
                frechet_derivative (W:real^N->real^N) (at y) w = --(christoffel G y w (W y))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC(VECTOR_ARITH `a + b = vec 0 ==> a = --b:real^N`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ; MATRIX_VECTOR_MUL_RNEG; DOT_LNEG; DOT_RNEG; DOT_RADD] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `(V:real^N->real^N) y`; `(W:real^N->real^N) y`] LRG_CHRISTOFFEL_DOT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `(W:real^N->real^N) y`; `(V:real^N->real^N) y`] LRG_CHRISTOFFEL_DOT) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `christoffel G y w ((V:real^N->real^N) y)`; `(W:real^N->real^N) y`]
                LRG_METRIC_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `w:real^N`;
                 `(W:real^N->real^N) y`; `(V:real^N->real^N) y`] LRG_MDERIV_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(V:real^N->real^N) y`; `(W:real^N->real^N) y`; `w:real^N`] LRG_MDERIV_SYM) THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`;
                 `(W:real^N->real^N) y`; `(V:real^N->real^N) y`; `w:real^N`] LRG_MDERIV_SYM) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2BX1_PAR_SIGN_LOCAL = prove
 (`!U (G:real^3->real^3^3) V W y0.
     metric_field U G /\ connected U /\ y0 IN U /\ smooth_map_on U V /\ smooth_map_on U W /\
     (!z w. z IN U ==> frechet_derivative V (at z) w + christoffel G z w (V z) = vec 0) /\
     (!z w. z IN U ==> frechet_derivative W (at z) w + christoffel G z w (W z) = vec 0) /\
     (!z. z IN U ==> V z dot (G z ** V z) = &1) /\
     (!z. z IN U ==> W z dot (G z ** W z) = &1) /\
     ~(lscalar G y0 = &0)
     ==> (!z. z IN U ==> W z = V z) \/ (!z. z IN U ==> W z = --(V z))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "pv") (CONJUNCTS_THEN2 (LABEL_TAC "pw")
    (CONJUNCTS_THEN2 (LABEL_TAC "uv") (CONJUNCTS_THEN2 (LABEL_TAC "uw") ASSUME_TAC))))))))) THEN
  SUBGOAL_THEN `open (U:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  (* the inner product is constant *)
  MP_TAC(ISPECL [`\z. lift((V:real^3->real^3) z dot ((G:real^3->real^3^3) z ** W z))`;
                 `U:real^3->bool`] HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX1_PAR_DOT_DERIV THEN
    EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^1` (LABEL_TAC "c1")) THEN
  ABBREV_TAC `c = drop c1` THEN
  SUBGOAL_THEN `!z. z IN U ==> (V:real^3->real^3) z dot ((G:real^3->real^3^3) z ** W z) = c`
  (LABEL_TAC "dc") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "c" THEN
    USE_THEN "c1" (fun th -> MP_TAC(MP (SPEC `z:real^3` th) (ASSUME `(z:real^3) IN U`))) THEN
    BETA_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  (* |W - c V|^2 = 1 - c^2 everywhere *)
  SUBGOAL_THEN `!z. z IN U
                    ==> ((W:real^3->real^3) z - c % V z) dot
                        ((G:real^3->real^3^3) z ** (W z - c % V z)) = &1 - c pow 2`
  (LABEL_TAC "zz") THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_LSUB; DOT_RSUB;
                DOT_LMUL; DOT_RMUL] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `z:real^3`;
                   `(W:real^3->real^3) z`; `(V:real^3->real^3) z`] LRG_METRIC_SYM) THEN
    USE_THEN "dc" (fun th -> MP_TAC(MP (SPEC `z:real^3` th) (ASSUME `(z:real^3) IN U`))) THEN
    USE_THEN "uv" (fun th -> MP_TAC(MP (SPEC `z:real^3` th) (ASSUME `(z:real^3) IN U`))) THEN
    USE_THEN "uw" (fun th -> MP_TAC(MP (SPEC `z:real^3` th) (ASSUME `(z:real^3) IN U`))) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  (* the unit field V is nonzero at y0 *)
  SUBGOAL_THEN `~((V:real^3->real^3) y0 = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    USE_THEN "uv" (fun th -> MP_TAC(MP (SPEC `y0:real^3` th) (ASSUME `(y0:real^3) IN U`))) THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* at y0 the orthogonal part vanishes *)
  SUBGOAL_THEN `(W:real^3->real^3) y0 - c % V y0 = vec 0` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(lscalar (G:real^3->real^3^3) y0 = &0)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `!u v. lriemann (G:real^3->real^3^3) y0 u v ((V:real^3->real^3) y0) = vec 0 /\
                        lriemann G y0 u v ((W:real^3->real^3) y0) = vec 0`
    (LABEL_TAC "kill") THENL
     [REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC P2BX0_LRIEMANN_PARALLEL THEN
      EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!u v w. lriemann (G:real^3->real^3^3) y0 u v w = vec 0` ASSUME_TAC THENL
     [MATCH_MP_TAC P2BX0_TWO_KILLED_RIEMANN0 THEN
      MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `(V:real^3->real^3) y0`;
                            `(W:real^3->real^3) y0 - c % V y0`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[COLLINEAR_LEMMA_ALT; DE_MORGAN_THM; NOT_EXISTS_THM] THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `l:real` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(V:real^3->real^3) y0 dot ((G:real^3->real^3^3) y0 **
                                                (W y0 - c % V y0)) = &0` MP_TAC THENL
         [REWRITE_TAC[MATRIX_VECTOR_MUL_SUB_LDISTRIB; MATRIX_VECTOR_MUL_RMUL; DOT_RSUB;
                      DOT_RMUL] THEN
          USE_THEN "dc" (fun th -> MP_TAC(MP (SPEC `y0:real^3` th) (ASSUME `(y0:real^3) IN U`))) THEN
          USE_THEN "uv" (fun th -> MP_TAC(MP (SPEC `y0:real^3` th) (ASSUME `(y0:real^3) IN U`))) THEN
          REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
        USE_THEN "uv" (fun th -> MP_TAC(MP (SPEC `y0:real^3` th) (ASSUME `(y0:real^3) IN U`))) THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_RID] THEN DISCH_TAC THEN
        UNDISCH_TAC `~((W:real^3->real^3) y0 - c % V y0 = vec 0)` THEN
        ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
        MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
        MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `y0:real^3`] LRIEMANN_TRILINEAR) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT2 o CONJUNCT2) THEN
        DISCH_THEN(fun th -> REWRITE_TAC[BETA_RULE(MATCH_MP LINEAR_SUB th);
                                         BETA_RULE(MATCH_MP LINEAR_CMUL th)]) THEN
        USE_THEN "kill" (fun th -> REWRITE_TAC[th]) THEN VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[lscalar; lricci; VEC_COMPONENT; SUM_0; REAL_MUL_RZERO];
    ALL_TAC] THEN
  (* hence c^2 = 1 and W = c V everywhere *)
  SUBGOAL_THEN `c pow 2 = &1` ASSUME_TAC THENL
   [USE_THEN "zz" (fun th -> MP_TAC(MP (SPEC `y0:real^3` th) (ASSUME `(y0:real^3) IN U`))) THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN U ==> (W:real^3->real^3) z = c % V z` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `G:real^3->real^3^3`; `z:real^3`;
                   `(W:real^3->real^3) z - c % V z`] LRG_METRIC_POS) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "zz" (fun th -> MP_TAC(MP (SPEC `z:real^3` th) (ASSUME `(z:real^3) IN U`))) THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c = &1 \/ c = --(&1)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 = &1` THEN CONV_TAC REAL_RING;
    DISJ1_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LID];
    DISJ2_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID]]);;

(* ------------------------------------------------------------------------- *)
(* Two unit parallel fields on an open set W agree up to one sign near every *)
(* point where R <> 0.  The chart_at representatives on a ball               *)
(* (P2BX1_PAR_SIGN_LOCAL), transported back by the chart Jacobian            *)
(* (PDG_VREP_INVERT).                                                        *)
(* ------------------------------------------------------------------------- *)

let P2BX1_PAR_SIGN = prove
 (`!top atlas (G:B->real^3^3) W X Y y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\ open_in top W /\
     y IN W /\ p2b_parallel_on atlas G W X /\ p2b_parallel_on atlas G W Y /\
     (!z. z IN W ==> X z dot (G z ** X z) = &1) /\
     (!z. z IN W ==> Y z dot (G z ** Y z) = &1) /\
     ~(mfd_scalar atlas G y = &0)
     ==> ?N. open_in top N /\ y IN N /\ N SUBSET W /\
             ((!z. z IN N ==> Y z = X z) \/ (!z. z IN N ==> Y z = --(X z)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "px") (CONJUNCTS_THEN2 (LABEL_TAC "py")
    (CONJUNCTS_THEN2 (LABEL_TAC "ux") (CONJUNCTS_THEN2 (LABEL_TAC "uy") ASSUME_TAC)))))))) THEN
  SUBGOAL_THEN `(W:B->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `y:B`] CHART_AT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `c = chart_at (atlas:((B->bool)#(B->real^3))->bool) (y:B)` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `c:(B->bool)#(B->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ci1") (LABEL_TAC "ci2")))) THEN
  ABBREV_TAC `O = IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER W)` THEN
  SUBGOAL_THEN `open (O:real^3->bool) /\ SND (c:(B->bool)#(B->real^3)) y IN O`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFDM_CHART_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`] THEN
      ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `SND (c:(B->bool)#(B->real^3)) y` o
              GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `B0 = ball(SND (c:(B->bool)#(B->real^3)) y,r)` THEN
  SUBGOAL_THEN `!u. u IN O ==> chart_inv (c:(B->bool)#(B->real^3)) u IN FST c INTER W`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:B` THEN
    STRIP_TAC THEN USE_THEN "ci1" (MP_TAC o SPEC `x:B`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the local sign lemma on the ball *)
  SUBGOAL_THEN `open (B0:real^3->bool) /\ connected B0 /\ SND (c:(B->bool)#(B->real^3)) y IN B0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B0" THEN ASM_REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; CENTRE_IN_BALL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`B0:real^3->bool`; `metric_local atlas (c:(B->bool)#(B->real^3)) (G:B->real^3^3)`;
                 `mfd_vrep atlas (X:B->real^3) (c:(B->bool)#(B->real^3))`;
                 `mfd_vrep atlas (Y:B->real^3) (c:(B->bool)#(B->real^3))`;
                 `SND (c:(B->bool)#(B->real^3)) y`] P2BX1_PAR_SIGN_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `riemannian_metric atlas (G:B->real^3^3)` THEN
        REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(B0:real^3->bool) SUBSET O` THEN EXPAND_TAC "O" THEN SET_TAC[]];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "O" THEN
      USE_THEN "px" (MP_TAC o SPEC `c:(B->bool)#(B->real^3)` o CONJUNCT1 o
                     GEN_REWRITE_RULE I [p2b_parallel_on]) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `O:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "O" THEN
      USE_THEN "py" (MP_TAC o SPEC `c:(B->bool)#(B->real^3)` o CONJUNCT1 o
                     GEN_REWRITE_RULE I [p2b_parallel_on]) THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "px" (MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [p2b_parallel_on]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(B0:real^3->bool) SUBSET O` THEN UNDISCH_TAC `(z:real^3) IN B0` THEN
      SET_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "py" (MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [p2b_parallel_on]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(B0:real^3->bool) SUBSET O` THEN UNDISCH_TAC `(z:real^3) IN B0` THEN
      SET_TAC[];
      X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(u:real^3) IN O` ASSUME_TAC THENL
       [UNDISCH_TAC `(B0:real^3->bool) SUBSET O` THEN UNDISCH_TAC `(u:real^3) IN B0` THEN
        SET_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(u:real^3) IN O`) o check (fun th ->
        can (term_match [] `!u. u IN O ==> chart_inv (c:(B->bool)#(B->real^3)) u IN FST c INTER W`)
            (concl th))) THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                     `X:B->real^3`; `c:(B->bool)#(B->real^3)`; `u:real^3`] P2BX0_VREP_DOT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(u:real^3) IN O` THEN EXPAND_TAC "O" THEN SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "ux" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(u:real^3) IN O` ASSUME_TAC THENL
       [UNDISCH_TAC `(B0:real^3->bool) SUBSET O` THEN UNDISCH_TAC `(u:real^3) IN B0` THEN
        SET_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(u:real^3) IN O`) o check (fun th ->
        can (term_match [] `!u. u IN O ==> chart_inv (c:(B->bool)#(B->real^3)) u IN FST c INTER W`)
            (concl th))) THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                     `Y:B->real^3`; `c:(B->bool)#(B->real^3)`; `u:real^3`] P2BX0_VREP_DOT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(u:real^3) IN O` THEN EXPAND_TAC "O" THEN SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "uy" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                     `c:(B->bool)#(B->real^3)`; `SND (c:(B->bool)#(B->real^3)) y`]
                    P2BX0_LSCALAR_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
                      DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "ci1" (MP_TAC o SPEC `y:B`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the neighbourhood: the preimage of the ball *)
  DISCH_TAC THEN
  EXISTS_TAC `{x | x IN FST (c:(B->bool)#(B->real^3)) /\ SND c x IN B0} INTER W` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFA_CHART_PREIMAGE_OPEN THEN
    EXISTS_TAC `atlas:((B->bool)#(B->real^3))->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "B0" THEN REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "B0" THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN {x | x IN FST (c:(B->bool)#(B->real^3)) /\ SND c x IN B0} INTER W
        ==> (X:B->real^3) z = chart_jac c (chart_at atlas z) z (mfd_vrep atlas X c (SND c z)) /\
            (Y:B->real^3) z = chart_jac c (chart_at atlas z) z (mfd_vrep atlas Y c (SND c z)) /\
            linear (chart_jac c (chart_at atlas z) z) /\ SND c z IN B0`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:B` THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:B) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDG_VREP_INVERT THEN
      EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC PDG_VREP_INVERT THEN
      EXISTS_TAC `top:B topology` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `z:B`] CHART_AT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM PAIR] THEN MATCH_MP_TAC CHART_JAC_LINEAR THEN
      EXISTS_TAC `top:B topology` THEN EXISTS_TAC `atlas:((B->bool)#(B->real^3))->bool` THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th))) THENL
   [DISJ1_TAC THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:B` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_jac")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    DISJ2_TAC THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:B` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "chart_jac")) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[LINEAR_NEG]]);;

(* ------------------------------------------------------------------------- *)
(* The line field at the zero-plane time.  SMP part (i) on the shifted flow  *)
(* gives local splitting of g(s0) (the slice is not flat); a system of local *)
(* unit parallel fields with their signs; a consistent choice of signs gives *)
(* a global field and the model.                                             *)
(* ------------------------------------------------------------------------- *)

let P2BX1_LOCALLY_SPLIT_AT = prove
 (`!kappa top atlas (g:real->B->real^3^3) b s0 x0 u v.
     p2b_ancflow0 kappa (top,atlas) g b /\ s0 < b /\ x0 IN topspace top /\
     ~collinear {vec 0,u,v} /\ mfd_sectional atlas (g s0) x0 u v = &0
     ==> p2b_locally_split (top,atlas) (g s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`; `s0:real`] P2BX1_SHIFT_CLASS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "upto") (LABEL_TAC "sec0"))) THEN
  MP_TAC(REWRITE_RULE[p2b_ancflow0] (ASSUME
    `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "rf") (CONJUNCTS_THEN2 (LABEL_TAC "cp")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "nf")
    (CONJUNCTS_THEN2 (LABEL_TAC "dr") (LABEL_TAC "kn")))))))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `\t. (g:real->B->real^3^3)(t + s0)`; `--(&1)`; `&0`; `x0:B`; `&0`]
         (REWRITE_RULE[P2B_REQ_RFA_SMP_SPLIT_PT_STATEMENT]
                      (ISPEC `UNIV:B->bool` RFA_P2B_REQ_SMP_SPLIT_PT))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `--(&1) < &0`; REAL_LE_REFL] THEN CONJ_TAC THENL
     [USE_THEN "upto" MATCH_MP_TAC THEN REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN USE_THEN "sec0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT1) THEN
  REWRITE_TAC[REAL_ADD_LID] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  REWRITE_TAC[REAL_ARITH `--(&1) < &0`; REAL_LE_REFL; REAL_ADD_LID] THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
  USE_THEN "nf" (MP_TAC o SPEC `s0:real`) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`atlas:((B->bool)#(B->real^3))->bool`; `(g:real->B->real^3^3) s0`; `y:B`]
                P2BX1_RM_NORM_ZERO) THEN
  ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The sign data of the line field and the case of a consistent choice of    *)
(* signs (a global unit parallel field).                                     *)
(* ------------------------------------------------------------------------- *)

let P2BX1_PARALLEL_ON_SUBSET = prove
 (`!(atlas:((B->bool)#(B->real^3))->bool) G W W' (X:B->real^3).
     p2b_parallel_on atlas G W X /\ W' SUBSET W ==> p2b_parallel_on atlas G W' X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_parallel_on] THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^3))) (FST c INTER W)` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* A consistent choice of signs eps relative to the reference field Xf x at  *)
(* each point x gives a global unit parallel field.                         *)

let P2BX1_GLOBAL_FIELD = prove
 (`!top atlas (G:B->real^3^3) (U:B->B->bool) (Xf:B->B->real^3) eps.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\
     (!i. open_in top (U i)) /\ (!x. x IN topspace top ==> x IN U x) /\
     (!i. p2b_parallel_on atlas G (U i) (Xf i)) /\
     (!i y. y IN U i ==> Xf i y dot (G y ** Xf i y) = &1) /\
     (!i x. x IN U i /\ x IN topspace top ==> Xf i x = Xf x x \/ Xf i x = --(Xf x x)) /\
     (!i. open_in top {x | x IN U i /\ (eps x <=> Xf i x = Xf x x)} /\
          open_in top {x | x IN U i /\ ~(eps x <=> Xf i x = Xf x x)})
     ==> p2b_parallel_on atlas G (topspace top)
                         (\y. if eps y then Xf y y else --(Xf y y)) /\
         !y. y IN topspace top
             ==> (if eps y then Xf y y else --(Xf y y)) dot
                 (G y ** (if eps y then Xf y y else --(Xf y y))) = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "op") (CONJUNCTS_THEN2 (LABEL_TAC "self")
    (CONJUNCTS_THEN2 (LABEL_TAC "par") (CONJUNCTS_THEN2 (LABEL_TAC "unit")
    (CONJUNCTS_THEN2 (LABEL_TAC "sgn") (LABEL_TAC "eps")))))))) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "self" (fun th -> ASSUME_TAC(MP (SPEC `y:B` th) (ASSUME `(y:B) IN topspace top`))) THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_LNEG; DOT_RNEG; REAL_NEG_NEG] THEN
    USE_THEN "unit" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC P2BPF_PARALLEL_ON_LOCAL THEN EXISTS_TAC `top:B topology` THEN
  ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  USE_THEN "self" (fun th -> ASSUME_TAC(MP (SPEC `x:B` th) (ASSUME `(x:B) IN topspace top`))) THEN
  SUBGOAL_THEN `(U:B->B->bool) x SUBSET topspace top` ASSUME_TAC THENL
   [USE_THEN "op" (fun th -> MATCH_ACCEPT_TAC (MATCH_MP OPEN_IN_SUBSET (SPEC `x:B` th)));
    ALL_TAC] THEN
  ASM_CASES_TAC `(eps:B->bool) x` THENL
   [EXISTS_TAC `{z | z IN (U:B->B->bool) x /\ (eps z <=> Xf x z = (Xf:B->B->real^3) z z)}` THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "eps" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `x:B` th)]);
      ASM_REWRITE_TAC[IN_ELIM_THM];
      UNDISCH_TAC `(U:B->B->bool) x SUBSET topspace top` THEN SET_TAC[];
      MATCH_MP_TAC P2BPF_PARALLEL_ON_EQ THEN
      EXISTS_TAC `top:B topology` THEN EXISTS_TAC `(Xf:B->B->real^3) x` THEN
      USE_THEN "eps" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `x:B` th)]) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `z:B` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(z:B) IN topspace top` ASSUME_TAC THENL
         [UNDISCH_TAC `(U:B->B->bool) x SUBSET topspace top` THEN
          UNDISCH_TAC `(z:B) IN (U:B->B->bool) x` THEN SET_TAC[];
          ALL_TAC] THEN
        USE_THEN "sgn" (fun th -> MP_TAC(MP (SPECL [`x:B`; `z:B`] th)
          (CONJ (ASSUME `(z:B) IN (U:B->B->bool) x`) (ASSUME `(z:B) IN topspace top`)))) THEN
        UNDISCH_TAC `(eps:B->bool) z <=> (Xf:B->B->real^3) x z = Xf z z` THEN
        ASM_CASES_TAC `(eps:B->bool) z` THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[];
        MATCH_MP_TAC P2BX1_PARALLEL_ON_SUBSET THEN EXISTS_TAC `(U:B->B->bool) x` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    EXISTS_TAC `{z | z IN (U:B->B->bool) x /\ ~(eps z <=> Xf x z = (Xf:B->B->real^3) z z)}` THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "eps" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `x:B` th)]);
      ASM_REWRITE_TAC[IN_ELIM_THM];
      UNDISCH_TAC `(U:B->B->bool) x SUBSET topspace top` THEN SET_TAC[];
      MATCH_MP_TAC P2BPF_PARALLEL_ON_EQ THEN
      EXISTS_TAC `top:B topology` THEN EXISTS_TAC `\y. --(&1) % (Xf:B->B->real^3) x y` THEN
      USE_THEN "eps" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `x:B` th)]) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_LNEG; VECTOR_MUL_LID] THEN
        X_GEN_TAC `z:B` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(z:B) IN topspace top` ASSUME_TAC THENL
         [UNDISCH_TAC `(U:B->B->bool) x SUBSET topspace top` THEN
          UNDISCH_TAC `(z:B) IN (U:B->B->bool) x` THEN SET_TAC[];
          ALL_TAC] THEN
        USE_THEN "sgn" (fun th -> MP_TAC(MP (SPECL [`x:B`; `z:B`] th)
          (CONJ (ASSUME `(z:B) IN (U:B->B->bool) x`) (ASSUME `(z:B) IN topspace top`)))) THEN
        UNDISCH_TAC `~((eps:B->bool) z <=> (Xf:B->B->real^3) x z = Xf z z)` THEN
        ASM_CASES_TAC `(eps:B->bool) z` THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[VECTOR_NEG_NEG];
        MATCH_MP_TAC P2BPF_PARALLEL_CMUL THEN EXISTS_TAC `top:B topology` THEN
        USE_THEN "eps" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `x:B` th)]) THEN
        ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC P2BX1_PARALLEL_ON_SUBSET THEN EXISTS_TAC `(U:B->B->bool) x` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]]]]);;

(* Unit vectors of a metric are nonzero; the empty set carries every field. *)

let P2BX1_UNIT_NZ = prove
 (`!(G:B->real^3^3) (X:B->real^3) y.
     X y dot (G y ** X y) = &1 ==> ~(X y = vec 0) /\ ~(X y = --(X y))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((X:B->real^3) y = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(X:B->real^3) y dot ((G:B->real^3^3) y ** X y) = &1` THEN
    ASM_REWRITE_TAC[DOT_LZERO] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `~((X:B->real^3) y = vec 0)` THEN
    REWRITE_TAC[] THEN UNDISCH_TAC `(X:B->real^3) y = --(X y)` THEN VECTOR_ARITH_TAC]);;

let P2BX1_PARALLEL_ON_EMPTY = prove
 (`!(atlas:((B->bool)#(B->real^3))->bool) G (X:B->real^3). p2b_parallel_on atlas G {} X`,
  REWRITE_TAC[p2b_parallel_on; INTER_EMPTY; IMAGE_CLAUSES; NOT_IN_EMPTY;
              P2CF_SMOOTH_MAP_ON_EMPTY]);;

(* The sign data: local unit parallel fields Xf i on U i (U i = {} off M),  *)
(* any two agree up to sign at common points, with open agreement and       *)
(* disagreement sets.                                                        *)

let P2BX1_SIGN_DATA = prove
 (`!top atlas (G:B->real^3^3).
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\
     p2b_locally_split (top,atlas) G /\
     (!x. x IN topspace top ==> ~(mfd_scalar atlas G x = &0))
     ==> ?U (Xf:B->B->real^3).
           (!i. open_in top (U i)) /\ (!x. x IN topspace top ==> x IN U x) /\
           (!i. p2b_parallel_on atlas G (U i) (Xf i)) /\
           (!i y. y IN U i ==> Xf i y dot (G y ** Xf i y) = &1) /\
           (!i j x. x IN U i /\ x IN U j ==> Xf i x = Xf j x \/ Xf i x = --(Xf j x)) /\
           (!i j. open_in top {x | x IN U i /\ x IN U j /\ Xf i x = Xf j x}) /\
           (!i j. open_in top {x | x IN U i /\ x IN U j /\ ~(Xf i x = Xf j x)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (MP_TAC o REWRITE_RULE[p2b_locally_split; RIGHT_IMP_EXISTS_THM; SKOLEM_THM])
                     (LABEL_TAC "rnz")))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Wf:B->B->bool` (X_CHOOSE_THEN `Xf:B->B->real^3` (LABEL_TAC "loc"))) THEN
  ABBREV_TAC `U = \i. if i IN topspace top then (Wf:B->B->bool) i else {}` THEN
  SUBGOAL_THEN
   `(!i. open_in top ((U:B->B->bool) i)) /\
    (!i. U i SUBSET topspace top) /\
    (!x. x IN topspace top ==> x IN U x) /\
    (!i. p2b_parallel_on atlas (G:B->real^3^3) (U i) ((Xf:B->B->real^3) i)) /\
    (!i y. y IN U i ==> Xf i y dot (G y ** Xf i y) = &1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:B` THEN BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[OPEN_IN_EMPTY] THEN
      USE_THEN "loc" (fun th -> REWRITE_TAC[MP (SPEC `i:B` th) (ASSUME `(i:B) IN topspace top`)]);
      X_GEN_TAC `i:B` THEN BETA_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[EMPTY_SUBSET] THEN
      MATCH_MP_TAC OPEN_IN_SUBSET THEN
      USE_THEN "loc" (fun th -> REWRITE_TAC[MP (SPEC `i:B` th) (ASSUME `(i:B) IN topspace top`)]);
      X_GEN_TAC `x:B` THEN DISCH_TAC THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "loc" (fun th -> REWRITE_TAC[MP (SPEC `x:B` th) (ASSUME `(x:B) IN topspace top`)]);
      X_GEN_TAC `i:B` THEN BETA_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[P2BX1_PARALLEL_ON_EMPTY] THEN
      USE_THEN "loc" (fun th -> REWRITE_TAC[MP (SPEC `i:B` th) (ASSUME `(i:B) IN topspace top`)]);
      MAP_EVERY X_GEN_TAC [`i:B`; `y:B`] THEN BETA_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[NOT_IN_EMPTY] THEN
      USE_THEN "loc" (fun th -> REWRITE_TAC[MP (SPEC `i:B` th) (ASSUME `(i:B) IN topspace top`)])];
    ALL_TAC] THEN
  (* the local sign agreement *)
  SUBGOAL_THEN
   `!i j x. x IN (U:B->B->bool) i /\ x IN U j
            ==> ?N. open_in top N /\ x IN N /\ N SUBSET U i INTER U j /\
                    ((!z. z IN N ==> (Xf:B->B->real^3) i z = Xf j z) \/
                     (!z. z IN N ==> Xf i z = --(Xf j z)))`
  (LABEL_TAC "loc2") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                   `(U:B->B->bool) i INTER U j`; `(Xf:B->B->real^3) j`; `(Xf:B->B->real^3) i`;
                   `x:B`] P2BX1_PAR_SIGN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC P2BX1_PARALLEL_ON_SUBSET THEN EXISTS_TAC `(U:B->B->bool) j` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC P2BX1_PARALLEL_ON_SUBSET THEN EXISTS_TAC `(U:B->B->bool) i` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        USE_THEN "rnz" MATCH_MP_TAC THEN
        MP_TAC(SPEC `i:B` (ASSUME `!i. (U:B->B->bool) i SUBSET topspace top`)) THEN
        UNDISCH_TAC `(x:B) IN (U:B->B->bool) i` THEN SET_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`U:B->B->bool`; `Xf:B->B->real^3`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "loc2" (fun th -> MP_TAC(MP (SPECL [`i:B`; `j:B`; `x:B`] th)
      (CONJ (ASSUME `(x:B) IN (U:B->B->bool) i`) (ASSUME `(x:B) IN (U:B->B->bool) j`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:B->bool` STRIP_ASSUME_TAC) THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`i:B`; `j:B`] THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    USE_THEN "loc2" (fun th -> MP_TAC(MP (SPECL [`i:B`; `j:B`; `x:B`] th)
      (CONJ (ASSUME `(x:B) IN (U:B->B->bool) i`) (ASSUME `(x:B) IN (U:B->B->bool) j`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:B->bool` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `N:B->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`G:B->real^3^3`; `(Xf:B->B->real^3) j`; `x:B`] P2BX1_UNIT_NZ) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `~((Xf:B->B->real^3) j x = --(Xf j x))` THEN
      UNDISCH_TAC `(Xf:B->B->real^3) i x = Xf j x` THEN ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`i:B`; `j:B`] THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    USE_THEN "loc2" (fun th -> MP_TAC(MP (SPECL [`i:B`; `j:B`; `x:B`] th)
      (CONJ (ASSUME `(x:B) IN (U:B->B->bool) i`) (ASSUME `(x:B) IN (U:B->B->bool) j`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:B->bool` STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC `~((Xf:B->B->real^3) i x = Xf j x)` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `N:B->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:B` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:B) IN (U:B->B->bool) i /\ z IN U j` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
      MP_TAC(ISPECL [`G:B->real^3^3`; `(Xf:B->B->real^3) j`; `z:B`] P2BX1_UNIT_NZ) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `~((Xf:B->B->real^3) j z = --(Xf j z))` THEN MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The section case and the route.  A consistent choice of signs gives a     *)
(* global unit parallel field and the model (P2BX1_GLOBAL_FIELD,             *)
(* P2BX1_ORIENTABLE_CASE); otherwise the double cover (P2BX1_COVER_CASE,     *)
(* below).                                                                   *)
(* ------------------------------------------------------------------------- *)

let P2BX1_SECTION_CASE = prove
 (`!w:B->bool.
     P2B_SPLIT_ROUND_STATEMENT w
     ==> !kappa top atlas (g:real->B->real^3^3) b s0 (U:B->B->bool) (Xf:B->B->real^3) eps.
           p2b_ancflow kappa (top,atlas) g b /\ s0 < b /\
           (!i. open_in top (U i)) /\ (!x. x IN topspace top ==> x IN U x) /\
           (!i. p2b_parallel_on atlas (g s0) (U i) (Xf i)) /\
           (!i y. y IN U i ==> Xf i y dot (g s0 y ** Xf i y) = &1) /\
           (!i j x. x IN U i /\ x IN U j ==> Xf i x = Xf j x \/ Xf i x = --(Xf j x)) /\
           (!i. open_in top {x | x IN U i /\ (eps x <=> Xf i x = Xf x x)} /\
                open_in top {x | x IN U i /\ ~(eps x <=> Xf i x = Xf x x)})
           ==> p2b_cyl_model (top,atlas) (\t. g(t + s0))`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "sr") THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`; `s0:real`; `U:B->B->bool`;
                       `Xf:B->B->real^3`; `eps:B->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) s0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `b:real`; `s0:real`] P2BX1_SHIFT_CLASS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[p2b_ancflow]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `--(&1)` o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[REAL_ARITH `--(&1) < &0`; rfs_flow_upto; ricci_flow_on; REAL_ADD_LID] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `U:B->B->bool`; `Xf:B->B->real^3`; `eps:B->bool`]
                P2BX1_GLOBAL_FIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    STRIP_TAC] THEN
  USE_THEN "sr" (MP_TAC o MATCH_MP P2BX1_ORIENTABLE_CASE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`kappa:real`; `b:real`;
                        `\y. if (eps:B->bool) y then (Xf:B->B->real^3) y y else --(Xf y y)`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The sign cocycle of the line field and the connectedness of its double    *)
(* cover (pc_smt_orient's smt_zcover) when no consistent choice of signs     *)
(* exists.                                                                   *)
(* ------------------------------------------------------------------------- *)

let P2BX1_ZCOCYCLE = prove
 (`!top (U:B->B->bool) (Xf:B->B->real^3) (G:B->real^3^3).
     (!i. open_in top (U i)) /\ (!x. x IN topspace top ==> x IN U x) /\
     (!i y. y IN U i ==> Xf i y dot (G y ** Xf i y) = &1) /\
     (!i j x. x IN U i /\ x IN U j ==> Xf i x = Xf j x \/ Xf i x = --(Xf j x)) /\
     (!i j. open_in top {x | x IN U i /\ x IN U j /\ Xf i x = Xf j x}) /\
     (!i j. open_in top {x | x IN U i /\ x IN U j /\ ~(Xf i x = Xf j x)})
     ==> smt_zcocycle top U (\i j x. Xf i x = Xf j x) (\x. x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "unit") (CONJUNCTS_THEN2 (LABEL_TAC "sgn")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
  REWRITE_TAC[smt_zcocycle] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:B`; `j:B`; `l:B`; `x:B`] THEN STRIP_TAC THEN
  USE_THEN "sgn" (fun th -> MP_TAC(MP (SPECL [`i:B`; `j:B`; `x:B`] th)
    (CONJ (ASSUME `(x:B) IN (U:B->B->bool) i`) (ASSUME `(x:B) IN (U:B->B->bool) j`)))) THEN
  USE_THEN "sgn" (fun th -> MP_TAC(MP (SPECL [`j:B`; `l:B`; `x:B`] th)
    (CONJ (ASSUME `(x:B) IN (U:B->B->bool) j`) (ASSUME `(x:B) IN (U:B->B->bool) l`)))) THEN
  USE_THEN "unit" (fun th -> MP_TAC(MATCH_MP P2BX1_UNIT_NZ
    (MP (SPECL [`l:B`; `x:B`] th) (ASSUME `(x:B) IN (U:B->B->bool) l`)))) THEN
  USE_THEN "unit" (fun th -> MP_TAC(MATCH_MP P2BX1_UNIT_NZ
    (MP (SPECL [`j:B`; `x:B`] th) (ASSUME `(x:B) IN (U:B->B->bool) j`)))) THEN
  MESON_TAC[VECTOR_NEG_NEG]);;

(* Preimages of open sets of the cover under the sheet sections are open. *)

let P2BX1_ZCOVER_SLICE_OPEN = prove
 (`!top (U:B->B->bool) P i e A.
     smt_zcocycle top U P (\x. x) /\ open_in (smt_zcover top U P (\x. x)) A
     ==> open_in top {y | y IN U i /\ (y,(P i y y <=> e)) IN A}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `U:B->B->bool`; `P:B->B->B->bool`; `\x:B. x`; `i:B`;
                 `e:bool`; `(U:B->B->bool) i`] SMT_ZCOVER_SHEET_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    UNDISCH_TAC `smt_zcocycle top (U:B->B->bool) P (\x:B. x)` THEN
    REWRITE_TAC[smt_zcocycle] THEN SIMP_TAC[];
    REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `{y | y IN (U:B->B->bool) i /\ (y,(P i y y <=> e)) IN A} =
                IMAGE FST (A INTER IMAGE (\y. y,((P:B->B->B->bool) i y y <=> e)) (U i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTER] THEN X_GEN_TAC `y:B` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `(y:B),((P:B->B->B->bool) i y y <=> e)` THEN
      ASM_REWRITE_TAC[FST] THEN EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `q:B#bool` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC)) THEN
      UNDISCH_TAC `(q:B#bool) IN A` THEN ASM_REWRITE_TAC[FST]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `U:B->B->bool`; `P:B->B->B->bool`; `\x:B. x`]
                SMT_ZCOVER_FST_OPEN_MAP) THEN
  ASM_REWRITE_TAC[open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[]);;

(* Without a consistent choice of signs the double cover is connected.      *)

let P2BX1_ZCOVER_CONNECTED = prove
 (`!top (U:B->B->bool) P.
     connected_space top /\ smt_zcocycle top U P (\x. x) /\
     ~(?eps. !i. open_in top {x | x IN U i /\ (eps x <=> P i x x)} /\
                 open_in top {x | x IN U i /\ ~(eps x <=> P i x x)})
     ==> connected_space (smt_zcover top U P (\x. x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "noeps"))) THEN
  REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN X_GEN_TAC `A:B#bool->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x b. (x,b) IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) <=>
                      x IN topspace top` (LABEL_TAC "tsp") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMT_ZCOVER_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. (U:B->B->bool) i SUBSET topspace top` (LABEL_TAC "usub") THENL
   [GEN_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_MESON_TAC[smt_zcocycle]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN topspace top ==> x IN (U:B->B->bool) x` (LABEL_TAC "self") THENL
   [ASM_MESON_TAC[smt_zcocycle]; ALL_TAC] THEN
  (* slices of A and of its complement are open *)
  SUBGOAL_THEN `!i e. open_in top {y | y IN (U:B->B->bool) i /\ (y,(P i y y <=> e)) IN A} /\
                      open_in top {y | y IN U i /\ ~((y,(P i y y <=> e)) IN A)}`
  (LABEL_TAC "sl") THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2BX1_ZCOVER_SLICE_OPEN THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `{y | y IN (U:B->B->bool) i /\ ~((y,(P i y y <=> e)) IN A)} =
                    {y | y IN U i /\ (y,(P i y y <=> e)) IN
                         topspace (smt_zcover top U P (\x. x)) DIFF A}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF] THEN X_GEN_TAC `y:B` THEN
        USE_THEN "tsp" (fun th -> REWRITE_TAC[th]) THEN
        USE_THEN "usub" (MP_TAC o SPEC `i:B`) THEN SET_TAC[];
        MATCH_MP_TAC P2BX1_ZCOVER_SLICE_OPEN THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[closed_in]]];
    ALL_TAC] THEN
  (* the fibre over y seen from the sheets of index i *)
  SUBGOAL_THEN
   `!i y. y IN (U:B->B->bool) i
          ==> (((y,T) IN A /\ (y,F) IN A) <=>
               (y,(P i y y <=> T)) IN A /\ (y,(P i y y <=> F)) IN A) /\
              ((~((y,T) IN A) /\ ~((y,F) IN A)) <=>
               ~((y,(P i y y <=> T)) IN A) /\ ~((y,(P i y y <=> F)) IN A)) /\
              (~((y,T) IN A <=> (y,F) IN A) <=>
               ~((y,(P i y y <=> T)) IN A <=> (y,(P i y y <=> F)) IN A))`
  (LABEL_TAC "fib") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `(P:B->B->B->bool) i y y` THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  ABBREV_TAC `Z2 = {y | y IN topspace top /\ (y,T) IN A /\ (y,F) IN (A:B#bool->bool)}` THEN
  ABBREV_TAC `Z0 = {y | y IN topspace top /\ ~((y,T) IN A) /\ ~((y,F) IN (A:B#bool->bool))}` THEN
  ABBREV_TAC `Z1 = {y | y IN topspace top /\ ~((y,T) IN A <=> (y,F) IN (A:B#bool->bool))}` THEN
  SUBGOAL_THEN `open_in top (Z2:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Z2" THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `y0:B` THEN STRIP_TAC THEN
    USE_THEN "self" (fun th -> ASSUME_TAC(MP (SPEC `y0:B` th) (ASSUME `(y0:B) IN topspace top`))) THEN
    EXISTS_TAC `{y | y IN (U:B->B->bool) y0 /\ (y,(P y0 y y <=> T)) IN A} INTER
                {y | y IN U y0 /\ (y,(P y0 y y <=> F)) IN A}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN USE_THEN "sl" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "fib" (fun th -> MP_TAC(CONJUNCT1(MP (SPECL [`y0:B`; `y0:B`] th)
                                     (ASSUME `(y0:B) IN (U:B->B->bool) y0`)))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [USE_THEN "usub" (MP_TAC o SPEC `y0:B`) THEN UNDISCH_TAC `(y:B) IN (U:B->B->bool) y0` THEN
        SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "fib" (fun th -> MP_TAC(CONJUNCT1(MP (SPECL [`y0:B`; `y:B`] th)
                                     (ASSUME `(y:B) IN (U:B->B->bool) y0`)))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (Z0:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Z0" THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `y0:B` THEN STRIP_TAC THEN
    USE_THEN "self" (fun th -> ASSUME_TAC(MP (SPEC `y0:B` th) (ASSUME `(y0:B) IN topspace top`))) THEN
    EXISTS_TAC `{y | y IN (U:B->B->bool) y0 /\ ~((y,(P y0 y y <=> T)) IN A)} INTER
                {y | y IN U y0 /\ ~((y,(P y0 y y <=> F)) IN A)}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN USE_THEN "sl" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "fib" (fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(MP (SPECL [`y0:B`; `y0:B`] th)
                                     (ASSUME `(y0:B) IN (U:B->B->bool) y0`))))) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [USE_THEN "usub" (MP_TAC o SPEC `y0:B`) THEN UNDISCH_TAC `(y:B) IN (U:B->B->bool) y0` THEN
        SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "fib" (fun th -> MP_TAC(CONJUNCT1(CONJUNCT2(MP (SPECL [`y0:B`; `y:B`] th)
                                     (ASSUME `(y:B) IN (U:B->B->bool) y0`))))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (Z1:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Z1" THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `y0:B` THEN STRIP_TAC THEN
    USE_THEN "self" (fun th -> ASSUME_TAC(MP (SPEC `y0:B` th) (ASSUME `(y0:B) IN topspace top`))) THEN
    EXISTS_TAC `({y | y IN (U:B->B->bool) y0 /\ (y,(P y0 y y <=> T)) IN A} INTER
                 {y | y IN U y0 /\ ~((y,(P y0 y y <=> F)) IN A)}) UNION
                ({y | y IN U y0 /\ ~((y,(P y0 y y <=> T)) IN A)} INTER
                 {y | y IN U y0 /\ (y,(P y0 y y <=> F)) IN A})` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC OPEN_IN_INTER THEN USE_THEN "sl" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[IN_UNION; IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "fib" (fun th -> MP_TAC(CONJUNCT2(CONJUNCT2(MP (SPECL [`y0:B`; `y0:B`] th)
                                     (ASSUME `(y0:B) IN (U:B->B->bool) y0`))))) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
      REWRITE_TAC[SUBSET; IN_UNION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `y:B` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(y:B) IN (U:B->B->bool) y0` ASSUME_TAC THENL
       [POP_ASSUM MP_TAC THEN CONV_TAC TAUT; ALL_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "usub" (MP_TAC o SPEC `y0:B`) THEN UNDISCH_TAC `(y:B) IN (U:B->B->bool) y0` THEN
        SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "fib" (fun th -> MP_TAC(CONJUNCT2(CONJUNCT2(MP (SPECL [`y0:B`; `y:B`] th)
                                     (ASSUME `(y:B) IN (U:B->B->bool) y0`))))) THEN
      DISCH_THEN SUBST1_TAC THEN POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN
      CONV_TAC TAUT];
    ALL_TAC] THEN
  (* the partition of M *)
  SUBGOAL_THEN `(Z1:B->bool) = {} \/ Z1 = topspace top` MP_TAC THENL
   [UNDISCH_TAC `connected_space (top:B topology)` THEN REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Z1"] THEN SET_TAC[];
      SUBGOAL_THEN `topspace top DIFF (Z1:B->bool) = Z0 UNION Z2` SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["Z0"; "Z1"; "Z2"] THEN SET_TAC[];
        MATCH_MP_TAC OPEN_IN_UNION THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [ALL_TAC;
    USE_THEN "noeps" (MP_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `\y:B. (y,T) IN (A:B#bool->bool)`) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN X_GEN_TAC `i:B` THEN
    SUBGOAL_THEN `!y. y IN (U:B->B->bool) i
                      ==> (((y,T) IN A <=> P i y y) <=> (y,(P i y y <=> T)) IN A)`
    (LABEL_TAC "pt") THENL
     [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:B) IN Z1` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "usub" (MP_TAC o SPEC `i:B`) THEN
        UNDISCH_TAC `(y:B) IN (U:B->B->bool) i` THEN SET_TAC[];
        EXPAND_TAC "Z1" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_CASES_TAC `(P:B->B->B->bool) i y y` THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{x | x IN (U:B->B->bool) i /\ ((x,T) IN A <=> P i x x)} =
      {y | y IN U i /\ (y,(P i y y <=> T)) IN A} /\
      {x | x IN U i /\ ~((x,T) IN A <=> P i x x)} =
      {y | y IN U i /\ ~((y,(P i y y <=> T)) IN A)}`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONJ_TAC THEN X_GEN_TAC `y:B` THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "pt" (fun th -> MP_TAC(MP (SPEC `y:B` th) (ASSUME `(y:B) IN (U:B->B->bool) i`))) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "sl" (fun th -> REWRITE_TAC[th])]] THEN
  (* Z1 empty: Z0 and Z2 split M *)
  SUBGOAL_THEN `(Z0:B->bool) = {} \/ Z0 = topspace top` MP_TAC THENL
   [UNDISCH_TAC `connected_space (top:B topology)` THEN REWRITE_TAC[CONNECTED_SPACE_CLOPEN_IN] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Z0"] THEN SET_TAC[];
      SUBGOAL_THEN `topspace top DIFF (Z0:B->bool) = Z2` SUBST1_TAC THENL
       [UNDISCH_TAC `(Z1:B->bool) = {}` THEN MAP_EVERY EXPAND_TAC ["Z0"; "Z1"; "Z2"] THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; NOT_IN_EMPTY] THEN MESON_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:B#bool->bool) SUBSET topspace (smt_zcover top U P (\x. x))` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ2_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC [`y:B`; `b:bool`] THEN
    USE_THEN "tsp" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:B) IN Z2` MP_TAC THENL
     [SUBGOAL_THEN `~((y:B) IN Z0) /\ ~(y IN Z1)` MP_TAC THENL
       [ASM_REWRITE_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["Z0"; "Z1"; "Z2"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      EXPAND_TAC "Z2" THEN REWRITE_TAC[IN_ELIM_THM] THEN BOOL_CASES_TAC `b:bool` THEN
      SIMP_TAC[]];
    DISJ1_TAC THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:B`; `b:bool`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:B) IN topspace top` ASSUME_TAC THENL
     [USE_THEN "tsp" (fun th -> REWRITE_TAC[GSYM th]) THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:B) IN Z0` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Z0" THEN REWRITE_TAC[IN_ELIM_THM] THEN BOOL_CASES_TAC `b:bool` THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The double cover inside B.  B is infinite (a nonempty 3-manifold contains *)
(* a copy of an open set of real^3), so there is an injection j : B#bool ->  *)
(* B with a left inverse (card.ml); the topology of smt_zcover is            *)
(* transported along j (MTR_TOPOLOGY) and the projection is pi = FST o j'.   *)
(* ------------------------------------------------------------------------- *)

let P2BX1_MANIFOLD_INFINITE = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool).
     smooth_manifold_atlas top atlas /\ ~(topspace top = {}) ==> INFINITE(:B)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:B` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `x:B`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `INFINITE (IMAGE (SND (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)))
                                (FST (chart_at atlas x)))` MP_TAC THENL
   [MP_TAC(ISPEC `IMAGE (SND (chart_at (atlas:((B->bool)#(B->real^3))->bool) (x:B)))
                        (FST (chart_at atlas x))` OPEN_IMP_INFINITE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(:B)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV]);;

let P2BX1_PAIR_INJECTION = prove
 (`INFINITE(:B) ==> ?j:B#bool->B j'. !p. j'(j p) = p`,
  DISCH_TAC THEN
  MP_TAC(ISPECL [`(:bool)`; `(:B)`] CARD_MUL_ABSORB_LE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_LE_FINITE_INFINITE THEN
    ASM_REWRITE_TAC[FINITE_BOOL];
    ALL_TAC] THEN
  REWRITE_TAC[le_c; mul_c; IN_UNIV; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:bool#B->B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!p q. (f:bool#B->B) (SND p,FST p) = f (SND q,FST q) ==> (p:B#bool) = q`
  MP_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p2:bool,p1:B`; `p2':bool,p1':B`]) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    ANTS_TAC THENL [MESON_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[INJECTIVE_LEFT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `h:B->B#bool`) THEN
  MAP_EVERY EXISTS_TAC [`\p:B#bool. (f:bool#B->B) (SND p,FST p)`; `h:B->B#bool`] THEN
  ASM_REWRITE_TAC[]);;

(* A homeomorphism followed by a covering map is a covering map. *)

let P2BX1_COVERING_MAP_HOMEO = prove
 (`!X Y Z (h:C->A) (p:A->B).
     homeomorphic_map (Z,X) h /\ covering_map (X,Y) p ==> covering_map (Z,Y) (p o h)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[covering_map] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  SUBGOAL_THEN `continuous_map (Z,X) (h:C->A) /\ IMAGE h (topspace Z) = topspace X /\
                (!x y. x IN topspace Z /\ y IN topspace Z ==> (h x = h y <=> x = y))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP; HOMEOMORPHIC_IMP_SURJECTIVE_MAP;
                  homeomorphic_map];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `X:A topology` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_o];
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MP (SPEC `y:B` th) (ASSUME `(y:B) IN topspace Y`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `V:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `vs:(A->bool)->bool` STRIP_ASSUME_TAC)))) THEN
    EXISTS_TAC `V:B->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `IMAGE (\U. {z | z IN topspace Z /\ (h:C->A) z IN U}) (vs:(A->bool)->bool)` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_IMAGE; o_THM] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:C` THEN
      ASM_CASES_TAC `(z:C) IN topspace Z` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(h:C->A) z IN topspace X` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `UNIONS vs = {x | x IN topspace X /\ (p:A->B) x IN V}` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `(h:C->A) z`) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `U:A->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `X:A topology` THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[PAIRWISE_IMAGE] THEN
      UNDISCH_TAC `pairwise DISJOINT (vs:(A->bool)->bool)` THEN
      REWRITE_TAC[pairwise] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`U1:A->bool`; `U2:A->bool`] THEN STRIP_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`U1:A->bool`; `U2:A->bool`] o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `U:A->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN EXISTS_TAC `subtopology X (U:A->bool)` THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (h:C->A) (topspace Z) = topspace X` THEN SET_TAC[]]]);;

(* The double cover of a Hausdorff space is Hausdorff. *)

let P2BX1_ZCOVER_HAUSDORFF = prove
 (`!top (U:B->B->bool) P.
     hausdorff_space top /\ smt_zcocycle top U P (\x. x)
     ==> hausdorff_space (smt_zcover top U P (\x. x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x b. (x,b) IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) <=>
                      x IN topspace top` (LABEL_TAC "tsp") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMT_ZCOVER_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(!i. open_in top ((U:B->B->bool) i)) /\
                (!x. x IN topspace top ==> x IN U x) /\
                (!i x. x IN U i ==> (P:B->B->B->bool) i i x)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `smt_zcocycle top (U:B->B->bool) P (\x:B. x)` THEN
    REWRITE_TAC[smt_zcocycle] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[hausdorff_space; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `b:bool`; `y:B`; `c:bool`] THEN
  USE_THEN "tsp" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:B = y` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(b:bool = c)` ASSUME_TAC THENL
     [UNDISCH_TAC `~((y:B),(b:bool) = y,c)` THEN REWRITE_TAC[PAIR_EQ]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (\z. z,((P:B->B->B->bool) y z z <=> b)) ((U:B->B->bool) y)`;
      `IMAGE (\z. z,((P:B->B->B->bool) y z z <=> c)) ((U:B->B->bool) y)`] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `U:B->B->bool`; `P:B->B->B->bool`; `\x:B. x`; `y:B`;
                     `b:bool`; `(U:B->B->bool) y`] SMT_ZCOVER_SHEET_OPEN) THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      MP_TAC(ISPECL [`top:B topology`; `U:B->B->bool`; `P:B->B->B->bool`; `\x:B. x`; `y:B`;
                     `c:bool`; `(U:B->B->bool) y`] SMT_ZCOVER_SHEET_OPEN) THEN
      ASM_REWRITE_TAC[SUBSET_REFL];
      REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN EXISTS_TAC `y:B` THEN ASM_SIMP_TAC[];
      REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN EXISTS_TAC `y:B` THEN ASM_SIMP_TAC[];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; FORALL_PAIR_THM;
                  SMT_ZCOVER_IN_GRAPH] THEN
      MAP_EVERY X_GEN_TAC [`z:B`; `d:bool`] THEN
      ASM_CASES_TAC `(P:B->B->B->bool) y z z` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(b:bool = c)` THEN CONV_TAC TAUT];
    MP_TAC(SPECL [`x:B`; `y:B`] (REWRITE_RULE[hausdorff_space]
      (ASSUME `hausdorff_space (top:B topology)`))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `Ux:B->bool` (X_CHOOSE_THEN `Uy:B->bool` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`{q | q IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) /\ FST q IN Ux}`;
      `{q | q IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) /\ FST q IN Uy}`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `top:B topology` THEN
      ASM_SIMP_TAC[SMT_ZCOVER_FST_CONTINUOUS];
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `top:B topology` THEN
      ASM_SIMP_TAC[SMT_ZCOVER_FST_CONTINUOUS];
      REWRITE_TAC[IN_ELIM_THM] THEN USE_THEN "tsp" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN USE_THEN "tsp" (fun th -> REWRITE_TAC[th]) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `DISJOINT (Ux:B->bool) Uy` THEN SET_TAC[]]]);;

(* The double cover transported into B along j. *)

let P2BX1_TRANSPORT_COVER = prove
 (`!top (U:B->B->bool) P (j:B#bool->B) j'.
     hausdorff_space top /\ connected_space (smt_zcover top U P (\x. x)) /\
     smt_zcocycle top U P (\x. x) /\ (!p. j'(j p) = p)
     ==> ?topc. (!W. open_in topc W <=>
                     ?V. open_in (smt_zcover top U P (\x. x)) V /\ W = IMAGE j V) /\
                topspace topc = IMAGE j (topspace (smt_zcover top U P (\x. x))) /\
                homeomorphic_maps (smt_zcover top U P (\x. x),topc) (j,j') /\
                hausdorff_space topc /\ connected_space topc /\
                covering_map (topc,top) (FST o j')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`smt_zcover top (U:B->B->bool) P (\x:B. x)`; `j:B#bool->B`; `j':B->B#bool`]
                MTR_TOPOLOGY) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `topc:B topology` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `smt_zcover top (U:B->B->bool) P (\x:B. x) homeomorphic_space (topc:B topology)`
  ASSUME_TAC THENL [REWRITE_TAC[homeomorphic_space] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_HAUSDORFF_SPACE; P2BX1_ZCOVER_HAUSDORFF];
    ASM_MESON_TAC[HOMEOMORPHIC_CONNECTED_SPACE];
    MATCH_MP_TAC P2BX1_COVERING_MAP_HOMEO THEN
    EXISTS_TAC `smt_zcover top (U:B->B->bool) P (\x:B. x)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_MAPS_IMP_MAP THEN EXISTS_TAC `j:B#bool->B` THEN
      ASM_MESON_TAC[HOMEOMORPHIC_MAPS_SYM];
      MATCH_MP_TAC SMT_ZCOVER_COVERING_MAP THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Sheets of the transported cover and its smooth atlas.  A sheet over an    *)
(* open V inside U i is IMAGE j (IMAGE (\y. y,(P i y y <=> e)) V); pi = FST  *)
(* o j' maps it homeomorphically onto V.  The lifted charts are (sheet over  *)
(* U i INTER FST c, SND c o pi), with the transition maps of the atlas of M. *)
(* ------------------------------------------------------------------------- *)

let P2BX1_SHEET_FACTS = prove
 (`!top (U:B->B->bool) P (j:B#bool->B) j' topc i e V.
     smt_zcocycle top U P (\x. x) /\ (!p. j'(j p) = p) /\
     (!W. open_in topc W <=> ?V. open_in (smt_zcover top U P (\x. x)) V /\ W = IMAGE j V) /\
     topspace topc = IMAGE j (topspace (smt_zcover top U P (\x. x))) /\
     homeomorphic_maps (smt_zcover top U P (\x. x),topc) (j,j') /\
     open_in top V /\ V SUBSET U i
     ==> open_in topc (IMAGE j (IMAGE (\y. y,(P i y y <=> e)) V)) /\
         IMAGE (FST o j') (IMAGE j (IMAGE (\y. y,(P i y y <=> e)) V)) = V /\
         (!w. w IN IMAGE j (IMAGE (\y. y,(P i y y <=> e)) V)
              ==> FST(j' w) IN V /\ j(FST(j' w),(P i (FST(j' w)) (FST(j' w)) <=> e)) = w) /\
         (!w1 w2. w1 IN IMAGE j (IMAGE (\y. y,(P i y y <=> e)) V) /\
                  w2 IN IMAGE j (IMAGE (\y. y,(P i y y <=> e)) V) /\
                  FST(j' w1) = FST(j' w2) ==> w1 = w2) /\
         homeomorphic_map (subtopology topc (IMAGE j (IMAGE (\y. y,(P i y y <=> e)) V)),
                           subtopology top V) (FST o j')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `U:B->B->bool`; `P:B->B->B->bool`; `\x:B. x`; `i:B`;
                 `e:bool`; `V:B->bool`] SMT_ZCOVER_SHEET_OPEN) THEN
  MP_TAC(ISPECL [`top:B topology`; `U:B->B->bool`; `P:B->B->B->bool`; `\x:B. x`; `i:B`;
                 `e:bool`; `V:B->bool`] SMT_ZCOVER_SHEET_HOMEOMORPHIC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `IMAGE (\y. y,((P:B->B->B->bool) i y y <=> e)) V` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID] THEN
    REWRITE_TAC[ETA_AX; IMAGE_ID];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y1:B` THEN DISCH_TAC THEN X_GEN_TAC `y2:B` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REWRITE_TAC[o_DEF] THEN
    SUBGOAL_THEN `(\x. FST((j':B->B#bool) x)) = FST o j'` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology (smt_zcover top (U:B->B->bool) P (\x. x))
                            (IMAGE (\y. y,((P:B->B->B->bool) i y y <=> e)) V)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_MAPS_IMP_MAP THEN EXISTS_TAC `j:B#bool->B` THEN
      ASM_MESON_TAC[HOMEOMORPHIC_MAPS_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (\y. y,((P:B->B->B->bool) i y y <=> e)) V SUBSET
                  topspace (smt_zcover top U P (\x. x))` ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (\y. y,((P:B->B->B->bool) i y y <=> e)) V SUBSET
                 topspace (smt_zcover top U P (\x. x))` THEN
    UNDISCH_TAC `!p. (j':B->B#bool) ((j:B#bool->B) p) = p` THEN
    SPEC_TAC(`IMAGE (\y. y,((P:B->B->B->bool) i y y <=> e)) V`,`S:B#bool->bool`) THEN
    SPEC_TAC(`topspace (smt_zcover top (U:B->B->bool) P (\x. x))`,`Tz:B#bool->bool`) THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The transported double cover is proper (the preimage of a compact set is  *)
(* compact), and the deck involution tau(j(x,b)) = j(x,~b) is a              *)
(* fixed-point-free homeomorphism over M.                                    *)
(* ------------------------------------------------------------------------- *)

let P2BX1_ZCOVER_PROPER = prove
 (`!top (U:B->B->bool) P K.
     smt_zcocycle top U P (\x. x) /\ compact_in top K
     ==> compact_in (smt_zcover top U P (\x. x))
                    {p | p IN topspace (smt_zcover top U P (\x. x)) /\ FST p IN K}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x b. (x,b) IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) <=>
                      x IN topspace top` (LABEL_TAC "tsp") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMT_ZCOVER_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(!x. x IN topspace top ==> x IN (U:B->B->bool) x) /\
                (!i x. x IN U i ==> (P:B->B->B->bool) i i x)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `smt_zcocycle top (U:B->B->bool) P (\x:B. x)` THEN
    REWRITE_TAC[smt_zcocycle] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K:B->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[compact_in]; ALL_TAC] THEN
  REWRITE_TAC[compact_in] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `UU:(B#bool->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN {p | p IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) /\
                              FST p IN K}
                    ==> ?O. O IN UU /\ (p:B#bool) IN O` MP_TAC THENL
   [UNDISCH_TAC `{p | p IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) /\ FST p IN K}
                 SUBSET UNIONS UU` THEN REWRITE_TAC[SUBSET; IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `OO:B#bool->B#bool->bool` o
             REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  SUBGOAL_THEN
   `!x:B. x IN (K:B->bool)
          ==> (OO:B#bool->B#bool->bool)(x,T) IN (UU:(B#bool->bool)->bool) /\
              OO(x,F) IN UU /\ (x,T) IN OO(x,T) /\ (x,F) IN OO(x,F)`
  (LABEL_TAC "oo") THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `(x:B),T` th) THEN MP_TAC(SPEC `(x:B),F` th)) THEN
    REWRITE_TAC[IN_ELIM_THM; FST] THEN USE_THEN "tsp" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(x:B) IN topspace top` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `VV = \x:B. {y | y IN (U:B->B->bool) x /\
                     (y,((P:B->B->B->bool) x y y <=> T)) IN (OO:B#bool->B#bool->bool)(x,T)} INTER
               {y | y IN U x /\ (y,(P x y y <=> F)) IN OO(x,F)}` THEN
  SUBGOAL_THEN `!x. x IN (K:B->bool) ==> open_in top ((VV:B->B->bool) x) /\ x IN VV x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN EXPAND_TAC "VV" THEN
    USE_THEN "oo" (fun th -> MP_TAC(MP (SPEC `x:B` th) (ASSUME `(x:B) IN K`))) THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THEN
      MATCH_MP_TAC P2BX1_ZCOVER_SLICE_OPEN THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN `(x:B) IN (U:B->B->bool) x` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(P:B->B->B->bool) x x x` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]];
    ALL_TAC] THEN
  UNDISCH_TAC `compact_in top (K:B->bool)` THEN REWRITE_TAC[compact_in] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (VV:B->B->bool) K` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `VF:(B->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`VV:B->B->bool`; `K:B->bool`; `VF:(B->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:B->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (\x:B. OO(x,T):B#bool->bool) F0 UNION IMAGE (\x. OO(x,F)) F0` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE];
    REWRITE_TAC[UNION_SUBSET; SUBSET; FORALL_IN_IMAGE] THEN
    CONJ_TAC THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    USE_THEN "oo" (MP_TAC o SPEC `x:B`) THEN ANTS_TAC THEN SIMP_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; FST] THEN
    MAP_EVERY X_GEN_TAC [`y:B`; `b:bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?x:B. x IN F0 /\ (y:B) IN (VV:B->B->bool) x` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(K:B->bool) SUBSET UNIONS VF` THEN
      UNDISCH_TAC `(VF:(B->bool)->bool) = IMAGE VV (F0:B->bool)` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(y:B) IN (VV:B->B->bool) x` THEN EXPAND_TAC "VV" THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_UNION; IN_IMAGE] THEN
    ASM_CASES_TAC `(b:bool) = (P:B->B->B->bool) x y y` THENL
     [EXISTS_TAC `(OO:B#bool->B#bool->bool)((x:B),T)` THEN CONJ_TAC THENL
       [DISJ1_TAC THEN EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `((y:B),(P:B->B->B->bool) x y y) IN
                     (OO:B#bool->B#bool->bool)((x:B),T)` THEN
        ASM_REWRITE_TAC[]];
      EXISTS_TAC `(OO:B#bool->B#bool->bool)((x:B),F)` THEN CONJ_TAC THENL
       [DISJ2_TAC THEN EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `((y:B),~((P:B->B->B->bool) x y y)) IN
                     (OO:B#bool->B#bool->bool)((x:B),F)` THEN
        SUBGOAL_THEN `(b:bool) = ~((P:B->B->B->bool) x y y)` SUBST1_TAC THENL
         [UNDISCH_TAC `~((b:bool) = (P:B->B->B->bool) x y y)` THEN CONV_TAC TAUT;
          REWRITE_TAC[]]]]]);;

(* The transported cover is proper. *)

let P2BX1_COVER_PROPER = prove
 (`!top (U:B->B->bool) P (j:B#bool->B) j' topc K.
     smt_zcocycle top U P (\x. x) /\ (!p. j'(j p) = p) /\
     topspace topc = IMAGE j (topspace (smt_zcover top U P (\x. x))) /\
     homeomorphic_maps (smt_zcover top U P (\x. x),topc) (j,j') /\ compact_in top K
     ==> compact_in topc {w | w IN topspace topc /\ (FST o j') w IN K}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{w | w IN topspace topc /\ (FST o (j':B->B#bool)) w IN K} =
                IMAGE (j:B#bool->B)
                  {p | p IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) /\ FST p IN K}`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[o_THM; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `w:B` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:B#bool` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `p:B#bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `p:B#bool` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `p:B#bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `smt_zcover top (U:B->B->bool) P (\x. x)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX1_ZCOVER_PROPER THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[HOMEOMORPHIC_MAPS_MAP; HOMEOMORPHIC_IMP_CONTINUOUS_MAP]]);;

(* The exchange of the sheets of the double cover is a homeomorphism. *)

let P2BX1_ZCOVER_SWAP = prove
 (`!top (U:B->B->bool) P.
     smt_zcocycle top U P (\x. x)
     ==> homeomorphic_maps (smt_zcover top U P (\x. x),smt_zcover top U P (\x. x))
                           ((\p. FST p,~SND p),(\p. FST p,~SND p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_MAPS_INVOLUTION THEN
  SUBGOAL_THEN `!x b. (x,b) IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) <=>
                      x IN topspace top` (LABEL_TAC "tsp") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMT_ZCOVER_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[FORALL_PAIR_THM; FST; SND]] THEN
  REWRITE_TAC[continuous_map] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN USE_THEN "tsp" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  X_GEN_TAC `O:B#bool->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{p | p IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) /\ (FST p,~SND p) IN O} =
    IMAGE (\p:B#bool. FST p,~SND p) O`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`smt_zcover top (U:B->B->bool) P (\x. x)`; `O:B#bool->bool`]
                  OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_ELIM_THM; IN_IMAGE; FORALL_PAIR_THM; EXISTS_PAIR_THM;
                PAIR_EQ; FST; SND] THEN
    USE_THEN "tsp" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:B`; `b:bool`] THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`x:B`; `~b`] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `x':B` (X_CHOOSE_THEN `b':bool` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `open_in (smt_zcover top (U:B->B->bool) P (\x. x)) O` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SMT_ZCOVER_OPEN_IN th]) THEN
  REWRITE_TAC[UNION_OF; ARBITRARY] THEN
  DISCH_THEN(X_CHOOSE_THEN `uu:(B#bool->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (IMAGE (\p:B#bool. FST p,~SND p)) uu` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `s:B#bool->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:B#bool->bool`) THEN ASM_REWRITE_TAC[smt_zcover_basic] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:B` (X_CHOOSE_THEN `e:bool` (X_CHOOSE_THEN `V:B->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))) THEN
    MAP_EVERY EXISTS_TAC [`i:B`; `~e`; `V:B->bool`] THEN ASM_REWRITE_TAC[GSYM IMAGE_o] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; FST; SND; PAIR_EQ] THEN
    GEN_TAC THEN CONV_TAC TAUT;
    ASM_REWRITE_TAC[GSYM IMAGE_UNIONS]]);;

(* ------------------------------------------------------------------------- *)
(* The class of the route passes to a proper Hausdorff connected covering    *)
(* space with the lifted atlas and the pullback flow (pc_mfd_lift): Ricci    *)
(* flow chartwise, completeness, curvature, dR/ds, kappa-noncollapsing       *)
(* (balls map onto balls, volumes do not decrease), and orientability of     *)
(* relatively compact open sets.                                             *)
(* ------------------------------------------------------------------------- *)

let P2BX1_LIFT_RICCI_FLOW = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) (g:real->B->real^N^N) topc (f:A->B) a b.
     ricci_flow_on (top,atlas) a b g /\ local_homeomorphism_map (topc,top) f
     ==> ricci_flow_on (topc,mfd_lift_atlas topc top f atlas) a b
           (\t. mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f (g t))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas top (atlas:((B->bool)#(B->real^N))->bool) /\ a < b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ricci_flow_on]; ALL_TAC] THEN
  MATCH_MP_TAC P2CA_RICCI_FLOW_ON_CHARTS THEN ASM_SIMP_TAC[MFDL_ATLAS] THEN
  X_GEN_TAC `cc:(A->bool)#(A->real^N)` THEN REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))))) THEN
  REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_LIFT_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC RFA_LRICCI_FLOW_EQ THEN
  EXISTS_TAC `\t. metric_local atlas (c:(B->bool)#(B->real^N)) ((g:real->B->real^N^N) t)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RFA_LRICCI_FLOW_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N))) (FST c)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_RICCI_FLOW_ON_CHART THEN EXISTS_TAC `top:B topology` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC MFDL_METRIC_LOCAL_ON THEN ASM_REWRITE_TAC[]]);;

(* kappa-noncollapsing lifts. *)

let P2BX1_LIFT_KNC = prove
 (`!kappa top (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) b topc (f:A->B) r0.
     smooth_manifold_atlas top atlas /\ (!s. s < b ==> riemannian_metric atlas (g s)) /\
     covering_map (topc,top) f /\ hausdorff_space topc /\
     (!s. s < b ==> mfd_complete (topc,mfd_lift_atlas topc top f atlas)
                      (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f (g s))) /\
     rfs_kappa_noncollapsed (rfs_flow_view (top,atlas) {s | s < b} g) kappa r0
     ==> rfs_kappa_noncollapsed
           (rfs_flow_view (topc,mfd_lift_atlas topc top f atlas) {s | s < b}
              (\t. mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f (g t)))
           kappa r0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "riem")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cpl") MP_TAC))))) THEN
  SUBGOAL_THEN `local_homeomorphism_map (topc,top) (f:A->B) /\ continuous_map (topc,top) f`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COVERING_MAP_LOCAL_HOMEOMORPHISM; covering_map]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS]; ALL_TAC] THEN
  REWRITE_TAC[rfs_kappa_noncollapsed; rfs_flow_view; rfs_parabolic_exists; rfs_persists;
              rfs_vball; IN_ELIM_THM] THEN
  DISCH_THEN(LABEL_TAC "knc") THEN MAP_EVERY X_GEN_TAC [`t:real`; `x:A`; `r:real`] THEN
  ASM_CASES_TAC `t < b` THEN ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "curv"))))) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) t)` ASSUME_TAC THENL
   [USE_THEN "riem" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) x IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`]
                  CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:A) IN topspace topc` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_ball (top,atlas) ((g:real->B->real^3^3) t) ((f:A->B) x) r =
    IMAGE f (mfd_ball (topc,mfd_lift_atlas topc top f atlas)
               (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f (g t)) x r)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MFDL_BALL_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "knc" (MP_TAC o SPECL [`t:real`; `(f:A->B) x`; `r:real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `s < b` (fun th -> REWRITE_TAC[th]) THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `IMAGE (f:A->B) (mfd_ball (topc,mfd_lift_atlas topc top f atlas)
          (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f
                               ((g:real->B->real^3^3) t)) x r) =
        mfd_ball (top,atlas) (g t) (f x) r` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real`; `y:B`] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `z:A` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)))) THEN
      SUBGOAL_THEN `(z:A) IN topspace topc` ASSUME_TAC THENL
       [UNDISCH_TAC `(z:A) IN mfd_ball (topc,mfd_lift_atlas topc top f atlas)
                       (mfd_pullback_metric (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)) atlas f
                                            ((g:real->B->real^3^3) t)) x r` THEN
        REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN MESON_TAC[MFD_JOINABLE_IN_TOPSPACE];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `f:A->B`; `(g:real->B->real^3^3) s`; `z:A`] MFDL_RM_NORM) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "riem" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      USE_THEN "curv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `riemannian_metric (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool))
      (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f
                           ((g:real->B->real^3^3) t)) /\
    mfd_complete (topc,mfd_lift_atlas topc top f atlas)
      (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f (g t))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDL_RIEMANNIAN THEN ASM_REWRITE_TAC[];
      USE_THEN "cpl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)`;
                 `mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B)
                                      ((g:real->B->real^3^3) t)`; `x:A`; `r:real`]
                MFD_HAS_VOLUME_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  EXISTS_TAC
   `mfd_volume (topc,mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool))
      (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f ((g:real->B->real^3^3) t))
      (mfd_ball (topc,mfd_lift_atlas topc top f atlas)
         (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f (g t)) x r)` THEN
  ASM_REWRITE_TAC[] THEN TRANS_TAC REAL_LE_TRANS `v:real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL
   [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `f:A->B`;
    `(g:real->B->real^3^3) t`;
    `mfd_cball (topc,mfd_lift_atlas topc top f atlas)
       (mfd_pullback_metric (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)) atlas f
                            ((g:real->B->real^3^3) t)) x r`;
    `mfd_ball (topc,mfd_lift_atlas topc top f atlas)
       (mfd_pullback_metric (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)) atlas f
                            ((g:real->B->real^3^3) t)) x r`] MFDL_VOLUME_GE) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `mfd_complete (topc,mfd_lift_atlas topc top f atlas)
                   (mfd_pullback_metric (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)) atlas f
                                        ((g:real->B->real^3^3) t))` THEN
    REWRITE_TAC[mfd_complete] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]]);;

(* The class of the route lifts to a proper connected Hausdorff cover. *)

let P2BX1_LIFT_CLASS = prove
 (`!kappa top (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) b topc (f:A->B).
     p2b_ancflow0 kappa (top,atlas) g b /\
     covering_map (topc,top) f /\ hausdorff_space topc /\ connected_space topc /\
     (!K. compact_in top K ==> compact_in topc {w | w IN topspace topc /\ f w IN K})
     ==> p2b_ancflow0 kappa (topc,mfd_lift_atlas topc top f atlas)
           (\t. mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f (g t)) b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN MP_TAC th) STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX0_ANC_BASIC) THEN
  SUBGOAL_THEN `local_homeomorphism_map (topc,top) (f:A->B) /\
                IMAGE f (topspace topc) = topspace top`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COVERING_MAP_LOCAL_HOMEOMORPHISM; covering_map]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN topspace topc ==> (f:A->B) w IN topspace top` (LABEL_TAC "ft") THENL
   [UNDISCH_TAC `IMAGE (f:A->B) (topspace topc) = topspace top` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s < b ==> mfd_complete (topc,mfd_lift_atlas topc top f atlas)
                    (mfd_pullback_metric (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)) atlas f
                                         ((g:real->B->real^3^3) s))`
  (LABEL_TAC "cpl~") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MFDL_COMPLETE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2b_ancflow0] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "flow") (CONJUNCTS_THEN2 (LABEL_TAC "cpl")
    (CONJUNCTS_THEN2 (LABEL_TAC "sec") (CONJUNCTS_THEN2 (LABEL_TAC "nf")
    (CONJUNCTS_THEN2 (LABEL_TAC "dr") (LABEL_TAC "knc")))))))))) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `IMAGE (f:A->B) (topspace topc) = topspace top` THEN
    UNDISCH_TAC `~(topspace top:B->bool = {})` THEN SET_TAC[];
    X_GEN_TAC `a:real` THEN DISCH_TAC THEN MATCH_MP_TAC P2BX1_LIFT_RICCI_FLOW THEN
    ASM_SIMP_TAC[];
    USE_THEN "cpl~" ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`s:real`; `w:A`; `u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `f:A->B`; `(g:real->B->real^3^3) s`; `w:A`] MFDL_SECTIONAL_NONNEG) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN USE_THEN "sec" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "nf" (MP_TAC o C MATCH_MP (ASSUME `s < b`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?w. w IN topspace topc /\ (f:A->B) w = y` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (f:A->B) (topspace topc) = topspace top` THEN
      UNDISCH_TAC `(y:B) IN topspace top` THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `w:A` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `f:A->B`; `(g:real->B->real^3^3) s`; `w:A`] MFDL_RM_NORM) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real`; `w:A`; `dR:real`] THEN STRIP_TAC THEN
    USE_THEN "dr" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:real`; `(f:A->B) w`] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC `\t. mfd_scalar (mfd_lift_atlas topc top f atlas)
                      (mfd_pullback_metric (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)) atlas f
                                           ((g:real->B->real^3^3) t)) w` THEN
    EXISTS_TAC `b - s` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC MFDL_SCALAR THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `r0:real` THEN MATCH_MP_TAC P2BX1_LIFT_KNC THEN ASM_SIMP_TAC[] THEN
    USE_THEN "cpl~" ACCEPT_TAC]);;

(* Orientability of relatively compact open sets lifts. *)

let P2BX1_LIFT_LORIENT = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) topc (f:A->B).
     smooth_manifold_atlas top atlas /\ hausdorff_space top /\ p2b_lorient top atlas /\
     covering_map (topc,top) f
     ==> p2b_lorient topc (mfd_lift_atlas topc top f atlas)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_lorient] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "lor") ASSUME_TAC))) THEN
  SUBGOAL_THEN `local_homeomorphism_map (topc,top) (f:A->B) /\ continuous_map (topc,top) f /\
                open_map (topc,top) f`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COVERING_MAP_LOCAL_HOMEOMORPHISM; covering_map; COVERING_MAP_OPEN_MAP];
    ALL_TAC] THEN
  X_GEN_TAC `W:A->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC MFDL_ORIENTABLE THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "lor" MATCH_MP_TAC THEN
  SUBGOAL_THEN `open_in top (IMAGE (f:A->B) W)` ASSUME_TAC THENL
   [ASM_MESON_TAC[open_map]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `IMAGE (f:A->B) (topc closure_of W)` THEN
  REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `topc:A topology` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
      ASM_MESON_TAC[OPEN_IN_SUBSET];
      MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC IMAGE_COMPACT_IN THEN EXISTS_TAC `topc:A topology` THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The tautological field of the double cover.  A parallel field on the      *)
(* image of a sheet lifts to a parallel field on the sheet                   *)
(* (P2BX1_LIFT_PARALLEL).  On the transported double cover the vectors       *)
(* V(j(x,b)) = (if b then Xf x x else -Xf x x) lift to a global unit         *)
(* parallel field of the pullback of g(s0) (P2BX1_TAUT_FIELD).               *)
(* ------------------------------------------------------------------------- *)

(* The chart facts used for one lifted chart (S1,c) and the sheet S. *)

let P2BX1_LIFT_PARALLEL_CHART = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) topc (f:A->B) (G:B->real^N^N) S
    (Y:B->real^N) (V:A->real^N) S1 c.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
     (!w. w IN S ==> V w = Y(f w)) /\
     open_in topc S1 /\ open_in top (IMAGE f S1) /\
     homeomorphic_map (subtopology topc S1,subtopology top (IMAGE f S1)) f /\ c IN atlas
     ==> open (IMAGE (SND c o f) ((S1 INTER {w | f w IN FST c}) INTER S)) /\
         IMAGE (SND c o f) ((S1 INTER {w | f w IN FST c}) INTER S) SUBSET
         IMAGE (SND c) (FST c INTER IMAGE f S) /\
         open (IMAGE (SND c o f) (S1 INTER {w | f w IN FST c})) /\
         IMAGE (SND c o f) ((S1 INTER {w | f w IN FST c}) INTER S) SUBSET
         IMAGE (SND c o f) (S1 INTER {w | f w IN FST c}) /\
         (!z. z IN IMAGE (SND c o f) ((S1 INTER {w | f w IN FST c}) INTER S)
              ==> mfd_vrep (mfd_lift_atlas topc top f atlas) (mfd_lift_vec topc top f atlas V)
                           (S1 INTER {w | f w IN FST c},SND c o f) z =
                  mfd_vrep atlas Y c z) /\
         (!z. z IN IMAGE (SND c o f) (S1 INTER {w | f w IN FST c})
              ==> metric_local (mfd_lift_atlas topc top f atlas)
                    (S1 INTER {w | f w IN FST c},SND c o f)
                    (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f G) z =
                  metric_local atlas c G z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) /\
                (S1 INTER {w | f w IN FST (c:(B->bool)#(B->real^N))},SND c o f) IN
                mfd_lift_atlas topc top f atlas`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS]; ALL_TAC] THEN
    REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
    MAP_EVERY EXISTS_TAC [`S1:A->bool`; `c:(B->bool)#(B->real^N)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S1:A->bool`; `c:(B->bool)#(B->real^N)`] MFDL_LIFT_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                   `(S1 INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))},SND c o f)`;
                   `(S1 INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))}) INTER S`]
                  MFDM_CHART_IMAGE_OPEN) THEN
    ASM_REWRITE_TAC[FST; SND; INTER_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MFDL_VREP_EQ THEN
    EXISTS_TAC `(S1 INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))}) INTER S` THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN ASM SET_TAC[];
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MFDL_METRIC_LOCAL_ON THEN
    ASM_REWRITE_TAC[]]);;

let P2BX1_LIFT_PARALLEL = prove
 (`!top (atlas:((B->bool)#(B->real^N))->bool) topc (f:A->B) (G:B->real^N^N) S
    (Y:B->real^N) (V:A->real^N).
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f /\
     p2b_parallel_on atlas G (IMAGE f S) Y /\ (!w. w IN S ==> V w = Y(f w))
     ==> p2b_parallel_on (mfd_lift_atlas topc top f atlas)
           (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f G) S
           (mfd_lift_vec topc top f atlas V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `p2b_parallel_on atlas (G:B->real^N^N) (IMAGE (f:A->B) S) Y` THEN
  REWRITE_TAC[p2b_parallel_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sm") (LABEL_TAC "cov")) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `cc:(A->bool)#(A->real^N)` THEN REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
    DISCH_THEN(X_CHOOSE_THEN `S1:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))))) THEN
    REWRITE_TAC[FST; SND] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `topc:A topology`;
                   `f:A->B`; `G:B->real^N^N`; `S:A->bool`; `Y:B->real^N`; `V:A->real^N`;
                   `S1:A->bool`; `c:(B->bool)#(B->real^N)`] P2BX1_LIFT_PARALLEL_CHART) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `mfd_vrep atlas (Y:B->real^N) c` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N))) (FST c INTER IMAGE (f:A->B) S)` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`cc:(A->bool)#(A->real^N)`; `y:real^N`; `z:real^N`] THEN
  REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `S1:A->bool` (X_CHOOSE_THEN `c:(B->bool)#(B->real^N)`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[FST; SND]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `topc:A topology`;
                 `f:A->B`; `G:B->real^N^N`; `S:A->bool`; `Y:B->real^N`; `V:A->real^N`;
                 `S1:A->bool`; `c:(B->bool)#(B->real^N)`] P2BX1_LIFT_PARALLEL_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `frechet_derivative (mfd_vrep (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool))
                         (mfd_lift_vec topc top f atlas (V:A->real^N))
                         (S1 INTER {w | f w IN FST (c:(B->bool)#(B->real^N))},SND c o f)) (at y) =
    frechet_derivative (mfd_vrep atlas (Y:B->real^N) c) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N)) o (f:A->B))
                      ((S1 INTER {w | f w IN FST c}) INTER S)` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `christoffel (metric_local (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool))
                  (S1 INTER {w | f w IN FST (c:(B->bool)#(B->real^N))},SND c o f)
                  (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f
                                       (G:B->real^N^N))) y z =
    christoffel (metric_local atlas c G) y z`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `u:real^N` THEN
    MATCH_MP_TAC CHRISTOFFEL_LOCAL THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N)) o (f:A->B)) (S1 INTER {w | f w IN FST c})` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_vrep (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) (mfd_lift_vec topc top f atlas (V:A->real^N))
             (S1 INTER {w | f w IN FST (c:(B->bool)#(B->real^N))},SND c o f) y =
    mfd_vrep atlas (Y:B->real^N) c y`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "cov" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* On the sheet through (x,b) the tautological vectors are those of +-Xf x. *)

let P2BX1_TAUT_SIGN = prove
 (`!(Xf:B->B->real^3) x y b.
     (Xf x y = Xf y y \/ Xf x y = --(Xf y y)) /\ ~(Xf y y = --(Xf y y))
     ==> (if (Xf x y = Xf y y <=> b) then Xf y y else --(Xf y y)) =
         (if b then Xf x y else --(Xf x y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC) THENL
   [ASM_REWRITE_TAC[] THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[];
    SUBGOAL_THEN `~(--((Xf:B->B->real^3) y y) = Xf y y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[VECTOR_NEG_NEG]]);;

(* The tautological field of the transported double cover. *)

let P2BX1_TAUT_FIELD = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (G:B->real^3^3) (U:B->B->bool)
    (Xf:B->B->real^3) (j:B#bool->B) j' topc.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\
     (!i. open_in top (U i)) /\ (!x. x IN topspace top ==> x IN U x) /\
     (!i. p2b_parallel_on atlas G (U i) (Xf i)) /\
     (!i y. y IN U i ==> Xf i y dot (G y ** Xf i y) = &1) /\
     (!i j x. x IN U i /\ x IN U j ==> Xf i x = Xf j x \/ Xf i x = --(Xf j x)) /\
     smt_zcocycle top U (\i j x. Xf i x = Xf j x) (\x. x) /\ (!p. j'(j p) = p) /\
     (!W. open_in topc W <=>
          ?V. open_in (smt_zcover top U (\i j x. Xf i x = Xf j x) (\x. x)) V /\
              W = IMAGE j V) /\
     topspace topc = IMAGE j (topspace (smt_zcover top U (\i j x. Xf i x = Xf j x) (\x. x))) /\
     homeomorphic_maps (smt_zcover top U (\i j x. Xf i x = Xf j x) (\x. x),topc) (j,j') /\
     covering_map (topc,top) (FST o j')
     ==> p2b_parallel_on (mfd_lift_atlas topc top (FST o j') atlas)
           (mfd_pullback_metric (mfd_lift_atlas topc top (FST o j') atlas) atlas (FST o j') G)
           (topspace topc)
           (mfd_lift_vec topc top (FST o j') atlas
              (\w. if SND(j' w) then Xf (FST(j' w)) (FST(j' w))
                   else --(Xf (FST(j' w)) (FST(j' w))))) /\
         !w. w IN topspace topc
             ==> mfd_lift_vec topc top (FST o j') atlas
                   (\w. if SND(j' w) then Xf (FST(j' w)) (FST(j' w))
                        else --(Xf (FST(j' w)) (FST(j' w)))) w dot
                 (mfd_pullback_metric (mfd_lift_atlas topc top (FST o j') atlas) atlas
                                      (FST o j') G w **
                  mfd_lift_vec topc top (FST o j') atlas
                   (\w. if SND(j' w) then Xf (FST(j' w)) (FST(j' w))
                        else --(Xf (FST(j' w)) (FST(j' w)))) w) = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "self" (el 3 (CONJUNCTS th)) THEN
                       LABEL_TAC "unit" (el 5 (CONJUNCTS th)) THEN
                       LABEL_TAC "sgn" (el 6 (CONJUNCTS th))) THEN
  SUBGOAL_THEN `local_homeomorphism_map (topc,top) (FST o (j':B->B#bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[COVERING_MAP_LOCAL_HOMEOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN topspace topc ==> FST((j':B->B#bool) w) IN topspace top`
  (LABEL_TAC "ft") THENL
   [X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    UNDISCH_TAC `covering_map (topc,top) (FST o (j':B->B#bool))` THEN
    REWRITE_TAC[covering_map] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[o_DEF] THEN UNDISCH_TAC `(w:B) IN topspace topc` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topc:B topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST o (j':B->B#bool)`; `G:B->real^3^3`;
                   `\w. if SND((j':B->B#bool) w) then (Xf:B->B->real^3) (FST(j' w)) (FST(j' w))
                        else --(Xf (FST(j' w)) (FST(j' w)))`;
                   `\w. if SND((j':B->B#bool) w) then (Xf:B->B->real^3) (FST(j' w)) (FST(j' w))
                        else --(Xf (FST(j' w)) (FST(j' w)))`; `w:B`] MFDL_LIFT_VEC_DOT) THEN
    ASM_REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "ft" (fun th -> ASSUME_TAC(MP (SPEC `w:B` th) (ASSUME `(w:B) IN topspace topc`))) THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; DOT_LNEG; DOT_RNEG; REAL_NEG_NEG] THEN
    USE_THEN "unit" MATCH_MP_TAC THEN USE_THEN "self" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC P2BPF_PARALLEL_ON_LOCAL THEN EXISTS_TAC `topc:B topology` THEN
  REWRITE_TAC[OPEN_IN_TOPSPACE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MFDL_ATLAS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `w:B` THEN DISCH_TAC THEN
  USE_THEN "ft" (fun th -> ASSUME_TAC(MP (SPEC `w:B` th) (ASSUME `(w:B) IN topspace topc`))) THEN
  SUBGOAL_THEN `(j:B#bool->B) ((j':B->B#bool) w) = w` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphic_maps (smt_zcover top (U:B->B->bool)
                   (\i j x. (Xf:B->B->real^3) i x = Xf j x) (\x. x),topc)
                   ((j:B#bool->B),(j':B->B#bool))` THEN
    REWRITE_TAC[homeomorphic_maps] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = FST((j':B->B#bool) w)` THEN ABBREV_TAC `b = SND((j':B->B#bool) w)` THEN
  SUBGOAL_THEN `(j':B->B#bool) w = (x:B),(b:bool)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "b"] THEN REWRITE_TAC[PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:B) IN (U:B->B->bool) x` ASSUME_TAC THENL
   [USE_THEN "self" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `U:B->B->bool`; `\i j x. (Xf:B->B->real^3) i x = Xf j x`;
                 `j:B#bool->B`; `j':B->B#bool`; `topc:B topology`; `x:B`; `b:bool`;
                 `(U:B->B->bool) x`] P2BX1_SHEET_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inv") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) o BETA_RULE) THEN
  EXISTS_TAC `IMAGE (j:B#bool->B) (IMAGE (\y. y,((Xf:B->B->real^3) x y = Xf y y <=> b))
                                         ((U:B->B->bool) x))` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(x:B),(b:bool)` THEN CONJ_TAC THENL
     [UNDISCH_TAC `(j:B#bool->B) ((j':B->B#bool) w) = w` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]);
      EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[PAIR_EQ]];
    MATCH_MP_TAC OPEN_IN_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC P2BX1_LIFT_PARALLEL THEN
    EXISTS_TAC `\y. if b then (Xf:B->B->real^3) x y else --(Xf x y)` THEN
    SUBGOAL_THEN
     `IMAGE (FST o (j':B->B#bool))
        (IMAGE (j:B#bool->B) (IMAGE (\y. y,((Xf:B->B->real^3) x y = Xf y y <=> b))
                                    ((U:B->B->bool) x))) = U x`
    SUBST1_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `G:B->real^3^3`;
                     `(U:B->B->bool) x`; `(Xf:B->B->real^3) x`; `--(&1)`] P2BPF_PARALLEL_CMUL) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID];
      ALL_TAC] THEN
    X_GEN_TAC `w':B` THEN DISCH_TAC THEN
    USE_THEN "inv" (fun th -> MP_TAC(MP (SPEC `w':B` th)
      (ASSUME `(w':B) IN IMAGE (j:B#bool->B)
                 (IMAGE (\y. y,((Xf:B->B->real^3) x y = Xf y y <=> b)) ((U:B->B->bool) x))`))) THEN
    ABBREV_TAC `y = FST((j':B->B#bool) w')` THEN STRIP_TAC THEN
    REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `SND((j':B->B#bool) w') = ((Xf:B->B->real^3) x y = Xf y y <=> b)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THEN
      ASM_REWRITE_TAC[SND];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:B) IN (U:B->B->bool) y` ASSUME_TAC THENL
     [USE_THEN "self" MATCH_MP_TAC THEN
      SUBGOAL_THEN `(U:B->B->bool) x SUBSET topspace top` MP_TAC THENL
       [MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(y:B) IN (U:B->B->bool) x` THEN SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BX1_TAUT_SIGN THEN CONJ_TAC THENL
     [USE_THEN "sgn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`G:B->real^3^3`; `(Xf:B->B->real^3) y`; `y:B`] P2BX1_UNIT_NZ) THEN
      ANTS_TAC THENL [USE_THEN "unit" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* The double cover is the round cylinder model.  The class and p2b_lorient  *)
(* lift; the tautological field is a global unit parallel field of the       *)
(* lifted g(s0); P2BX1_ORIENTABLE_CASE0.                                     *)
(* ------------------------------------------------------------------------- *)

let P2BX1_COVER_MODEL = prove
 (`!w:B->bool.
     P2B_SPLIT_ROUND_STATEMENT w
     ==> !kappa top atlas (g:real->B->real^3^3) b s0 (U:B->B->bool) (Xf:B->B->real^3)
          (j:B#bool->B) j' topc.
           p2b_ancflow kappa (top,atlas) g b /\ s0 < b /\
           (!i. open_in top (U i)) /\ (!x. x IN topspace top ==> x IN U x) /\
           (!i. p2b_parallel_on atlas (g s0) (U i) (Xf i)) /\
           (!i y. y IN U i ==> Xf i y dot (g s0 y ** Xf i y) = &1) /\
           (!i j x. x IN U i /\ x IN U j ==> Xf i x = Xf j x \/ Xf i x = --(Xf j x)) /\
           smt_zcocycle top U (\i j x. Xf i x = Xf j x) (\x. x) /\ (!p. j'(j p) = p) /\
           (!W. open_in topc W <=>
                ?V. open_in (smt_zcover top U (\i j x. Xf i x = Xf j x) (\x. x)) V /\
                    W = IMAGE j V) /\
           topspace topc =
           IMAGE j (topspace (smt_zcover top U (\i j x. Xf i x = Xf j x) (\x. x))) /\
           homeomorphic_maps (smt_zcover top U (\i j x. Xf i x = Xf j x) (\x. x),topc) (j,j') /\
           hausdorff_space topc /\ connected_space topc /\ covering_map (topc,top) (FST o j')
           ==> p2b_cyl_model (topc,mfd_lift_atlas topc top (FST o j') atlas)
                 (\t. mfd_pullback_metric (mfd_lift_atlas topc top (FST o j') atlas) atlas
                                          (FST o j') (g(t + s0)))`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP P2BX1_ORIENTABLE_CASE0) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[p2b_ancflow; p2b_ksep] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX0_ANC_BASIC) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "riemannian_metric")) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `U:B->B->bool`; `Xf:B->B->real^3`;
                 `j:B#bool->B`; `j':B->B#bool`; `topc:B topology`] P2BX1_TAUT_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`kappa:real`; `topc:B topology`;
    `mfd_lift_atlas topc top (FST o (j':B->B#bool)) (atlas:((B->bool)#(B->real^3))->bool)`;
    `\t. mfd_pullback_metric (mfd_lift_atlas topc top (FST o (j':B->B#bool))
                                (atlas:((B->bool)#(B->real^3))->bool))
                             atlas (FST o j') ((g:real->B->real^3^3) t)`;
    `b:real`; `s0:real`;
    `mfd_lift_vec topc top (FST o (j':B->B#bool)) (atlas:((B->bool)#(B->real^3))->bool)
       (\w. if SND(j' w) then (Xf:B->B->real^3) (FST(j' w)) (FST(j' w))
            else --(Xf (FST(j' w)) (FST(j' w))))`] o
   check (fun th -> can (find_term (fun t -> is_const t && fst(dest_const t) = "p2b_cyl_model"))
                        (concl th))) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX1_LIFT_CLASS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `K:B->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `U:B->B->bool`; `\i j x. (Xf:B->B->real^3) i x = Xf j x`;
                   `j:B#bool->B`; `j':B->B#bool`; `topc:B topology`; `K:B->bool`]
                  P2BX1_COVER_PROPER) THEN
    ASM_REWRITE_TAC[o_THM];
    MATCH_MP_TAC P2BX1_LIFT_LORIENT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The deck involution of the transported cover, deck maps and sheets as     *)
(* diffeomorphisms of the lifted atlas, the pullback of a lifted metric by a *)
(* parametrization (P2BX1_RFS_PULLBACK_LIFT), and parametrizations with a    *)
(* given pullback as local isometries.                                       *)
(* ------------------------------------------------------------------------- *)

let P2BX1_DECK = prove
 (`!top (U:B->B->bool) P (j:B#bool->B) j' topc (tau:B->B).
     smt_zcocycle top U P (\x. x) /\ (!p. j'(j p) = p) /\
     topspace topc = IMAGE j (topspace (smt_zcover top U P (\x. x))) /\
     homeomorphic_maps (smt_zcover top U P (\x. x),topc) (j,j') /\
     (!w. tau w = j(FST(j' w),~SND(j' w)))
     ==> (!w. w IN topspace topc
              ==> tau w IN topspace topc /\ tau(tau w) = w /\ ~(tau w = w) /\
                  FST(j'(tau w)) = FST(j' w) /\ SND(j'(tau w)) = ~SND(j' w)) /\
         (!w1 w2. w1 IN topspace topc /\ w2 IN topspace topc
                  ==> (FST(j' w1) = FST(j' w2) <=> w2 = w1 \/ w2 = tau w1)) /\
         homeomorphic_maps (topc,topc) (tau,tau)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "tspc") (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  SUBGOAL_THEN `!x b. (x,b) IN topspace (smt_zcover top (U:B->B->bool) P (\x. x)) <=>
                      x IN topspace top` (LABEL_TAC "tsp") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SMT_ZCOVER_IN_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN topspace topc
        ==> ?x b. x IN topspace top /\ w = (j:B#bool->B)(x,b)`
  (LABEL_TAC "rep") THENL
   [X_GEN_TAC `w:B` THEN USE_THEN "tspc" SUBST1_TAC THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN
    USE_THEN "tsp" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x b. x IN topspace top ==> (j:B#bool->B)(x,b) IN topspace topc`
  (LABEL_TAC "jin") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "tspc" SUBST1_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    USE_THEN "tsp" (fun th -> ASM_REWRITE_TAC[th]);
    ALL_TAC] THEN
  REMOVE_THEN "tspc" (K ALL_TAC) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    USE_THEN "rep" (fun th -> MP_TAC(MP (SPEC `w:B` th) (ASSUME `(w:B) IN topspace topc`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:B` (X_CHOOSE_THEN `b:bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "jin" (fun th -> ASM_SIMP_TAC[th]) THEN
    DISCH_THEN(MP_TAC o AP_TERM `j':B->B#bool`) THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`w1:B`; `w2:B`] THEN STRIP_TAC THEN
    USE_THEN "rep" (fun th -> MP_TAC(MP (SPEC `w1:B` th) (ASSUME `(w1:B) IN topspace topc`))) THEN
    USE_THEN "rep" (fun th -> MP_TAC(MP (SPEC `w2:B` th) (ASSUME `(w2:B) IN topspace topc`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x2:B` (X_CHOOSE_THEN `b2:bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:B` (X_CHOOSE_THEN `b1:bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
    ASM_REWRITE_TAC[] THEN EQ_TAC THENL
     [DISCH_THEN SUBST1_TAC THEN ASM_CASES_TAC `(b2:bool) = b1` THEN ASM_REWRITE_TAC[] THEN
      DISJ2_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
      UNDISCH_TAC `~((b2:bool) = b1)` THEN CONV_TAC TAUT;
      DISCH_THEN(DISJ_CASES_THEN (MP_TAC o AP_TERM `j':B->B#bool`)) THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN SIMP_TAC[]];
    SUBGOAL_THEN `(tau:B->B) = (j:B#bool->B) o (\p. FST p,~SND p) o (j':B->B#bool)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [o_ASSOC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAPS_COMPOSE THEN
    EXISTS_TAC `smt_zcover top (U:B->B->bool) P (\x. x)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_MAPS_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HOMEOMORPHIC_MAPS_COMPOSE THEN
      EXISTS_TAC `smt_zcover top (U:B->B->bool) P (\x. x)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC P2BX1_ZCOVER_SWAP THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]]]);;

(* A homeomorphism over f is a diffeomorphism of the lifted atlas. *)

let P2BX1_DECK_DIFFEO = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (tau:A->A).
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     homeomorphic_maps (topc,topc) (tau,tau) /\
     (!w. w IN topspace topc ==> f(tau w) = f w)
     ==> mfd_diffeo topc (mfd_lift_atlas topc top f atlas) (topspace topc)
                    topc (mfd_lift_atlas topc top f atlas) (topspace topc) tau tau`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_diffeo; OPEN_IN_TOPSPACE; SUBTOPOLOGY_TOPSPACE] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w. w IN topspace topc ==> (tau:A->A) w IN topspace topc` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphic_maps (topc,topc) ((tau:A->A),tau)` THEN
    REWRITE_TAC[homeomorphic_maps; continuous_map] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC [`cc:(A->bool)#(A->real^N)`; `cc':(A->bool)#(A->real^N)`] THEN
  REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `S1:A->bool` (X_CHOOSE_THEN `c1:(B->bool)#(B->real^N)`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))))
    (X_CHOOSE_THEN `S2:A->bool` (X_CHOOSE_THEN `c2:(B->bool)#(B->real^N)`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))))) THEN
  REWRITE_TAC[FST; SND] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `chart_trans (c1:(B->bool)#(B->real^N)) c2` THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    X_GEN_TAC `w:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `f:A->B`; `S1:A->bool`; `c1:(B->bool)#(B->real^N)`] MFDL_CHART_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:A` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                   `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                   `FST (c2:(B->bool)#(B->real^N))`; `SND (c2:(B->bool)#(B->real^N))`;
                   `(f:A->B) w`] CHART_TRANS_AT) THEN
    ASM_REWRITE_TAC[PAIR];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c1:(B->bool)#(B->real^N))) (FST c1 INTER FST (c2:(B->bool)#(B->real^N)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `w:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(f:A->B)((tau:A->A) w) IN FST (c2:(B->bool)#(B->real^N))` THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                     `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`;
                     `FST (c2:(B->bool)#(B->real^N))`; `SND (c2:(B->bool)#(B->real^N))`]
                    CHART_TRANS_SMOOTH) THEN
      ASM_REWRITE_TAC[PAIR]]]);;

(* ------------------------------------------------------------------------- *)
(* Sheets as diffeomorphisms, the pullback of a lifted metric by a           *)
(* parametrization of the cover is the pullback of the base metric by its    *)
(* projection (P2BX1_RFS_PULLBACK_LIFT), and local parametrizations with     *)
(* pullback Gm are local isometries out of an open set of real^3             *)
(* (P2BX1_PARAM_LISOM).                                                      *)
(* ------------------------------------------------------------------------- *)

let P2BX1_SHEET_DIFFEO = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) S.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     open_in topc S /\ open_in top (IMAGE f S) /\
     homeomorphic_map (subtopology topc S,subtopology top (IMAGE f S)) f
     ==> ?sig. mfd_diffeo topc (mfd_lift_atlas topc top f atlas) S top atlas (IMAGE f S) f sig`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `sig:B->A` o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
  EXISTS_TAC `sig:B->A` THEN ASM_REWRITE_TAC[mfd_diffeo] THEN
  SUBGOAL_THEN `(S:A->bool) SUBSET topspace topc /\ IMAGE (f:A->B) S SUBSET topspace top`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN IMAGE (f:A->B) S ==> (sig:B->A) y IN S /\ f(sig y) = y`
  (LABEL_TAC "inv") THENL
   [UNDISCH_TAC `homeomorphic_maps (subtopology topc S,subtopology top (IMAGE (f:A->B) S))
                                   (f,(sig:B->A))` THEN
    REWRITE_TAC[homeomorphic_maps; continuous_map; TOPSPACE_SUBTOPOLOGY] THEN
    UNDISCH_TAC `IMAGE (f:A->B) S SUBSET topspace top` THEN
    UNDISCH_TAC `(S:A->bool) SUBSET topspace topc` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MFD_SMOOTH_MAP_SUBSET THEN EXISTS_TAC `topspace topc:A->bool` THEN
    ASM_SIMP_TAC[MFDL_SMOOTH_MAP];
    ALL_TAC] THEN
  REWRITE_TAC[mfd_smooth_map] THEN
  MAP_EVERY X_GEN_TAC [`c:(B->bool)#(B->real^N)`; `cc:(A->bool)#(A->real^N)`] THEN
  REWRITE_TAC[IN_MFD_LIFT_ATLAS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `S1:A->bool` (X_CHOOSE_THEN `c1:(B->bool)#(B->real^N)`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))))))) THEN
  REWRITE_TAC[FST; SND] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `c:(B->bool)#(B->real^N)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `chart_trans (c:(B->bool)#(B->real^N)) c1` THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_INTER; o_THM] THEN
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    USE_THEN "inv" (fun th -> MP_TAC(MP (SPEC `x:B` th) (ASSUME `(x:B) IN IMAGE (f:A->B) S`))) THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[chart_trans] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (c:(B->bool)#(B->real^N))) (FST c INTER FST (c1:(B->bool)#(B->real^N)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `x:B` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "inv" (fun th -> MP_TAC(MP (SPEC `x:B` th) (ASSUME `(x:B) IN IMAGE (f:A->B) S`))) THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                     `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`;
                     `FST (c1:(B->bool)#(B->real^N))`; `SND (c1:(B->bool)#(B->real^N))`]
                    CHART_TRANS_SMOOTH) THEN
      ASM_REWRITE_TAC[PAIR]]]);;

(* The pullback of the lifted metric by a parametrization of the cover. *)

let P2BX1_RFS_PULLBACK_LIFT = prove
 (`!topc top (atlas:((B->bool)#(B->real^N))->bool) (f:A->B) (g:B->real^N^N) s
    (e:real^N->A) y.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     mfd_param topc (mfd_lift_atlas topc top f atlas) s e /\ y IN s
     ==> rfs_pullback (mfd_lift_atlas topc top f atlas) e
           (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) y =
         rfs_pullback atlas (f o e) g y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) /\
                continuous_map (topc,top) f`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS; MFDL_LH_CONTINUOUS]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^N->A) y IN topspace topc` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (e:real^N->A) s SUBSET topspace topc` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `(e:real^N->A) y`]
                MFDL_LH_SHEET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open {z | z IN s /\ (e:real^N->A) z IN S}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
    EXISTS_TAC `s:real^N->bool` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{z | z IN s /\ (e:real^N->A) z IN S} =
                    {z | z IN topspace (subtopology euclidean s) /\ e z IN S}` SUBST1_TAC THENL
       [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `topc:A topology` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM OPEN_IN] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN {z | z IN s /\ (e:real^N->A) z IN S} /\
                {z | z IN s /\ (e:real^N->A) z IN S} SUBSET s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN CONJ_TAC THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)) {z | z IN s /\ (e:real^N->A) z IN S} (e:real^N->A)`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFD_PARAM_RESTRICT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `f:A->B`; `S:A->bool`] P2BX1_SHEET_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `sig:B->A`) THEN
  SUBGOAL_THEN `mfd_param top atlas {z | z IN s /\ (e:real^N->A) z IN S} ((f:A->B) o (e:real^N->A))` ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                          `S:A->bool`; `IMAGE (f:A->B) S`; `sig:B->A`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) ((e:real^N->A) y) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`]
                  CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:real^N->A) y IN topspace topc` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`;
                 `(f:A->B) ((e:real^N->A) y)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = chart_at (atlas:((B->bool)#(B->real^N))->bool) ((f:A->B) ((e:real^N->A) y))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^N))->bool`; `g:B->real^N^N`;
                 `{z | z IN s /\ (e:real^N->A) z IN S}`; `(f:A->B) o (e:real^N->A)`;
                 `FST (c:(B->bool)#(B->real^N))`; `SND (c:(B->bool)#(B->real^N))`; `y:real^N`]
                APX_RFS_PULLBACK_CHART) THEN
  ASM_REWRITE_TAC[PAIR; o_THM] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^N))->bool)`;
                 `mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B) (g:B->real^N^N)`;
                 `{z | z IN s /\ (e:real^N->A) z IN S}`; `e:real^N->A`;
                 `S INTER {w | (f:A->B) w IN FST (c:(B->bool)#(B->real^N))}`;
                 `SND (c:(B->bool)#(B->real^N)) o (f:A->B)`; `y:real^N`]
                APX_RFS_PULLBACK_CHART) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_MFD_LIFT_ATLAS] THEN
    MAP_EVERY EXISTS_TAC [`S:A->bool`; `c:(B->bool)#(B->real^N)`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN REWRITE_TAC[mpullback] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[o_THM] THEN MATCH_MP_TAC MFDL_METRIC_LOCAL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A map e from an open set R of real^3 that is locally a parametrization,   *)
(* with rfs_pullback equal to Gm, is a local isometry from (R,open_set_atlas *)
(* R,Gm) (P2BX1_PARAM_LISOM).                                                *)
(* ------------------------------------------------------------------------- *)

let P2BX1_PARAM_SMOOTH = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) R (e:real^3->A).
     smooth_manifold_atlas top atlas /\ open R /\
     (!y. y IN R ==> ?s. open s /\ y IN s /\ s SUBSET R /\ mfd_param top atlas s e)
     ==> continuous_map (subtopology euclidean R,top) e /\
         mfd_smooth_map (open_set_atlas R) atlas R e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  SUBGOAL_THEN `continuous_map (subtopology euclidean R,top) (e:real^3->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN R`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[GSYM OPEN_IN];
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      SUBGOAL_THEN `(R:real^3->bool) INTER s = s` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[mfd_smooth_map; RFB_OPEN_SET_ATLAS_CASES] THEN
  MAP_EVERY X_GEN_TAC [`c0:(real^3->bool)#(real^3->real^3)`; `c:(A->bool)#(A->real^3)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_IDEMPOT] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN
  EXISTS_TAC `\z. SND (c:(A->bool)#(A->real^3)) ((e:real^3->A) z)` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN SIMP_TAC[MFDM_CHART_INV_ID]; ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
    EXISTS_TAC `R:real^3->bool` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{x | x IN R /\ (e:real^3->A) x IN FST (c:(A->bool)#(A->real^3))} =
                    {x | x IN topspace (subtopology euclidean R) /\ e x IN FST c}`
      SUBST1_TAC THENL [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `top:A topology` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MFDM_CHART];
      REWRITE_TAC[GSYM OPEN_IN] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  USE_THEN "loc" (fun th -> MP_TAC(MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN R`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{z | z IN s /\ (e:real^3->A) z IN FST (c:(A->bool)#(A->real^3))}` THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `e:real^3->A`; `c:(A->bool)#(A->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]);;

let P2BX1_PARAM_LISOM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) R (Gm:real^3->real^3^3)
    (e:real^3->A).
     smooth_manifold_atlas top atlas /\ open R /\
     (!y. y IN R ==> ?s. open s /\ y IN s /\ s SUBSET R /\ mfd_param top atlas s e) /\
     (!y. y IN R ==> rfs_pullback atlas e G y = Gm y)
     ==> mfd_local_isometry (subtopology euclidean R,open_set_atlas R) Gm (top,atlas) G R e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    LABEL_TAC "loc" (el 2 (CONJUNCTS th)) THEN LABEL_TAC "pb" (el 3 (CONJUNCTS th))) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `R:real^3->bool`;
                 `e:real^3->A`] P2BX1_PARAM_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_local_isometry] THEN
  ASM_REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV;
                  SUBTOPOLOGY_SUBTOPOLOGY; INTER_IDEMPOT] THEN
  REWRITE_TAC[RFB_OPEN_SET_ATLAS_CASES; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[FST; SND; IMAGE_ID; INTER_IDEMPOT; IN_ELIM_THM] THEN
  X_GEN_TAC `c:(A->bool)#(A->real^3)` THEN DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL] THEN
  TRANS_TAC EQ_TRANS
   `mpullback (SND (c:(A->bool)#(A->real^3)) o (e:real^3->A)) (metric_local atlas c G) y` THEN
  CONJ_TAC THENL
   [USE_THEN "pb" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN R`))]) THEN
    USE_THEN "loc" (fun th -> MP_TAC(MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN R`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                   `s:real^3->bool`; `e:real^3->A`; `FST (c:(A->bool)#(A->real^3))`;
                   `SND (c:(A->bool)#(A->real^3))`; `y:real^3`] APX_RFS_PULLBACK_CHART) THEN
    ASM_REWRITE_TAC[PAIR];
    REWRITE_TAC[mpullback] THEN
    SUBGOAL_THEN
     `frechet_derivative (SND (c:(A->bool)#(A->real^3)) o (e:real^3->A) o
                          chart_inv (R,(\x:real^3. x))) (at y) =
      frechet_derivative (SND c o e) (at y)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `R:real^3->bool` THEN
      ASM_SIMP_TAC[o_THM; MFDM_CHART_INV_ID];
      ASM_SIMP_TAC[o_THM; MFDM_CHART_INV_ID]]]);;

(* ------------------------------------------------------------------------- *)
(* A unit parallel field seen through a local isometric parametrization by   *)
(* the round cylinder lam cyl(0).  Its 1-form p2bkg_pform (pc_p2b_kglob) at  *)
(* y is (mu / |y|^2) y with mu^2 = 2 lam: a parallel field kills the Ricci   *)
(* form, and the kernel of the Ricci form of the cylinder is the radial line *)
(* (LRICCI_ROUND_CYLINDER).                                                  *)
(* ------------------------------------------------------------------------- *)

let P2BX1_PFORM_MATRIX = prove
 (`!(atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (X:A->real^3) (psi:real^3->A) y.
     transp(g(psi y)) = g(psi y) /\
     linear(frechet_derivative (\z. SND(chart_at atlas (psi y)) (psi z)) (at y))
     ==> p2bkg_pform atlas g X psi y =
         transp(matrix(frechet_derivative (\z. SND(chart_at atlas (psi y)) (psi z)) (at y))) **
         (g(psi y) ** X(psi y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[p2bkg_pform; CART_EQ; LAMBDA_BETA] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
  ABBREV_TAC `D = frechet_derivative (\z. SND(chart_at (atlas:((A->bool)#(A->real^3))->bool)
                                                 ((psi:real^3->A) y)) (psi z)) (at y)` THEN
  SUBGOAL_THEN
   `(transp(matrix(D:real^3->real^3)) ** (g:A->real^3^3) ((psi:real^3->A) y) **
     (X:A->real^3) (psi y))$i =
    basis i dot (transp(matrix D) ** g (psi y) ** X (psi y))` SUBST1_TAC THENL
   [ASM_SIMP_TAC[DOT_BASIS]; ALL_TAC] THEN
  REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL] THEN ASM_SIMP_TAC[MATRIX_WORKS] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM DOT_MATRIX_TRANSP_LMUL] THEN ASM_REWRITE_TAC[DOT_SYM]);;

(* A parametrization read in a chart is a diffeomorphism of open sets. *)

let P2BX1_PARAM_CHART_DIFFEO = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) s (e:real^3->A) e' cc.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\
     mfd_diffeo euclidean (open_set_atlas (:real^3)) s top atlas (IMAGE e s) e e' /\
     (!x. x IN s ==> e'(e x) = x) /\ (!y. y IN IMAGE e s ==> e(e' y) = y) /\ cc IN atlas
     ==> diffeomorphism_on {z | z IN s /\ e z IN FST cc}
                           (IMAGE (SND cc) (FST cc INTER IMAGE e s))
                           (\z. SND cc (e z)) (\u. e'(chart_inv cc u))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `e:real^3->A`; `cc:(A->bool)#(A->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`; `cc:(A->bool)#(A->real^3)`]
                P2BKG_INV_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open (s:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_PARAM_MAPS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `cc:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `u:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(e:real^3->A) z` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `w:A` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(w:A) IN FST (cc:(A->bool)#(A->real^3))` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:real^3` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `w:A` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC)) THEN
      ASM_SIMP_TAC[] THEN UNDISCH_TAC `(w:A) IN FST (cc:(A->bool)#(A->real^3))` THEN
      ASM_SIMP_TAC[];
      STRIP_TAC THEN EXISTS_TAC `SND (cc:(A->bool)#(A->real^3)) ((e:real^3->A) z)` THEN
      ASM_SIMP_TAC[] THEN EXISTS_TAC `(e:real^3->A) z` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `u:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `w:A` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `(w:A) IN FST (cc:(A->bool)#(A->real^3))` THEN
    ASM_SIMP_TAC[]]);;

(* The field at a model point: the 1-form is radial with mu^2 = 2 lam. *)

let P2BX1_MODEL_FIELD = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (X:A->real^3) (e:real^3->A)
    lam s y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\ &0 < lam /\
     p2b_parallel_on atlas G (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (G x ** X x) = &1) /\
     mfd_param top atlas s e /\ s SUBSET {y | ~(y = vec 0)} /\
     (!z. z IN s ==> rfs_pullback atlas e G z = lam %% cylinder_flow (&0) z) /\ y IN s
     ==> ?mu. mu pow 2 = &2 * lam /\ p2bkg_pform atlas G X e y = (mu / norm y pow 2) % y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (e:real^3->A) s SUBSET topspace top` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(e:real^3->A) y`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `cc = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `cc:(A->bool)#(A->real^3)`] MFDM_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`; `cc:(A->bool)#(A->real^3)`]
                P2BX1_PARAM_CHART_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `U' = {z | z IN s /\ (e:real^3->A) z IN FST (cc:(A->bool)#(A->real^3))}` THEN
  ABBREV_TAC `h = \z. SND (cc:(A->bool)#(A->real^3)) ((e:real^3->A) z)` THEN
  ABBREV_TAC `h' = \u. (e':A->real^3) (chart_inv (cc:(A->bool)#(A->real^3)) u)` THEN
  ABBREV_TAC `U = IMAGE (SND (cc:(A->bool)#(A->real^3))) (FST cc INTER IMAGE (e:real^3->A) s)` THEN
  SUBGOAL_THEN `(y:real^3) IN U'` ASSUME_TAC THENL
   [EXPAND_TAC "U'" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND (cc:(A->bool)#(A->real^3))) (FST cc))
                             (metric_local atlas cc (G:A->real^3^3))` ASSUME_TAC THENL
   [ASM_MESON_TAC[riemannian_metric]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^3->bool) SUBSET IMAGE (SND (cc:(A->bool)#(A->real^3))) (FST cc)`
  ASSUME_TAC THENL [EXPAND_TAC "U" THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U (metric_local atlas (cc:(A->bool)#(A->real^3)) (G:A->real^3^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
    EXISTS_TAC `IMAGE (SND (cc:(A->bool)#(A->real^3))) (FST cc)` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  (* the pullback identity on U' *)
  SUBGOAL_THEN
   `!z. z IN U' ==> mpullback (h:real^3->real^3) (metric_local atlas cc (G:A->real^3^3)) z =
                    lam %% cylinder_flow (&0) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN EXPAND_TAC "U'" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM(MP (SPEC `z:real^3` th)
      (ASSUME `(z:real^3) IN s`))]) o check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "rfs_pullback")) (concl th))) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                   `s:real^3->bool`; `e:real^3->A`; `FST (cc:(A->bool)#(A->real^3))`;
                   `SND (cc:(A->bool)#(A->real^3))`; `z:real^3`] APX_RFS_PULLBACK_CHART) THEN
    ASM_REWRITE_TAC[PAIR] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  (* the parallel field in the chart cc *)
  SUBGOAL_THEN `IMAGE (SND (cc:(A->bool)#(A->real^3))) (FST cc INTER topspace top) =
                IMAGE (SND cc) (FST cc)` ASSUME_TAC THENL
   [AP_TERM_TAC THEN MP_TAC(ISPECL [`top:A topology`; `FST (cc:(A->bool)#(A->real^3))`]
      OPEN_IN_SUBSET) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `p2b_parallel_on atlas (G:A->real^3^3) (topspace top) X` THEN
  REWRITE_TAC[p2b_parallel_on] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `cc:(A->bool)#(A->real^3)`)
    (MP_TAC o SPEC `cc:(A->bool)#(A->real^3)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!u v. lriemann (metric_local atlas cc (G:A->real^3^3)) (h(y:real^3)) u v
                        (mfd_vrep atlas (X:A->real^3) cc (h y)) = vec 0`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2BX0_LRIEMANN_PARALLEL THEN
    EXISTS_TAC `IMAGE (SND (cc:(A->bool)#(A->real^3))) (FST cc)` THEN
    REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `mfd_vrep atlas (X:A->real^3) (cc:(A->bool)#(A->real^3)) (h(y:real^3)) =
                X((e:real^3->A) y)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[mfd_vrep] THEN ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `FST (cc:(A->bool)#(A->real^3))`; `SND (cc:(A->bool)#(A->real^3))`;
                   `(e:real^3->A) y`] CHART_JAC_SELF) THEN
    ASM_REWRITE_TAC[PAIR] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the vector Y at y *)
  ABBREV_TAC `Y = frechet_derivative (h':real^3->real^3) (at (h(y:real^3))) (X((e:real^3->A) y))` THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `U':real^3->bool`; `h:real^3->real^3`; `h':real^3->real^3`;
                 `y:real^3`] LRG_DIFFEO_DERIV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `frechet_derivative (h:real^3->real^3) (at y) Y = X((e:real^3->A) y)` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the 1-form and the unit length *)
  SUBGOAL_THEN `transp((G:A->real^3^3) ((e:real^3->A) y)) = G (e y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RIEMANNIAN_METRIC_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `frechet_derivative (\z. SND(chart_at atlas ((e:real^3->A) y)) (e z)) (at y) =
                frechet_derivative (h:real^3->real^3) (at y)` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2bkg_pform atlas (G:A->real^3^3) (X:A->real^3) (e:real^3->A) y =
    (lam %% cylinder_flow (&0) y) ** (Y:real^3)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`; `X:A->real^3`;
                   `e:real^3->A`; `y:real^3`] P2BX1_PFORM_MATRIX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM(MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN U'`))]) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mpullback")) (concl th))) THEN
    REWRITE_TAC[mpullback; GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                   `(e:real^3->A) y`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXPAND_TAC "h" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^3) dot ((lam %% cylinder_flow (&0) y) ** Y) = &1` ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM(MP (SPEC `y:real^3` th) (ASSUME `(y:real^3) IN U'`))]) o
      check (fun th -> is_forall (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "mpullback")) (concl th))) THEN
    REWRITE_TAC[mpullback; GSYM MATRIX_VECTOR_MUL_ASSOC; DOT_MATRIX_TRANSP_RMUL] THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                   `(e:real^3->A) y`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXPAND_TAC "h" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* Ric(.,Y) = 0 for the cylinder *)
  SUBGOAL_THEN `!u. lricci (\z:real^3. lam %% cylinder_flow (&0) z) y u Y = &0` ASSUME_TAC THENL
   [X_GEN_TAC `u:real^3` THEN
    TRANS_TAC EQ_TRANS `lricci (mpullback (h:real^3->real^3)
                                 (metric_local atlas (cc:(A->bool)#(A->real^3)) (G:A->real^3^3)))
                               y u Y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRICCI_LOCAL THEN EXISTS_TAC `U':real^3->bool` THEN
      ASM_SIMP_TAC[] THEN ASM_MESON_TAC[diffeomorphism_on];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `U':real^3->bool`; `h:real^3->real^3`; `h':real^3->real^3`;
                   `metric_local atlas (cc:(A->bool)#(A->real^3)) (G:A->real^3^3)`; `y:real^3`;
                   `u:real^3`; `Y:real^3`] LRICCI_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[lricci] THEN MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    UNDISCH_TAC `!u v. lriemann (metric_local atlas cc (G:A->real^3^3)) (h(y:real^3)) u v
                         (mfd_vrep atlas (X:A->real^3) (cc:(A->bool)#(A->real^3)) (h y)) = vec 0` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th; VEC_COMPONENT]);
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u dot Y - (u dot y) * (Y dot (y:real^3)) / norm y pow 2 = &0` ASSUME_TAC THENL
   [X_GEN_TAC `u:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^3` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "lricci")) (concl th))) THEN
    REWRITE_TAC[LRG_CYL0_EQ] THEN
    MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `\z:real^3. (&2 / norm z pow 2) %% (mat 1:real^3^3)`; `lam:real`;
                   `y:real^3`; `u:real^3`; `Y:real^3`] LRICCI_SCALE) THEN
    ASM_REWRITE_TAC[LRG_CYL_METRIC; IN_DELETE; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[LRICCI_ROUND_CYLINDER] THEN
    ASM_SIMP_TAC[REAL_DIV_EQ_0; REAL_POW_EQ_0; NORM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^3) = ((Y dot y) / norm (y:real^3) pow 2) % y` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC[GSYM DOT_EQ_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Y - ((Y dot y) / norm (y:real^3) pow 2) % y`) THEN
    REWRITE_TAC[DOT_LSUB; DOT_LMUL; DOT_RSUB; DOT_RMUL] THEN
    REWRITE_TAC[NORM_POW_2] THEN
    SUBGOAL_THEN `~((y:real^3) dot y = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `kap = (Y dot y) / norm (y:real^3) pow 2` THEN
  SUBGOAL_THEN `~((y:real^3) dot y = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. (lam %% cylinder_flow (&0) y) ** v =
                           (&2 * lam / norm (y:real^3) pow 2) % v` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[LRG_CYL0_EQ; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID;
                             VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * lam * kap * kap = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:real^3) dot ((lam %% cylinder_flow (&0) y) ** Y) = &1` THEN
    ASM_REWRITE_TAC[DOT_LMUL; DOT_RMUL; NORM_POW_2] THEN
    UNDISCH_TAC `~((y:real^3) dot y = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  EXISTS_TAC `&2 * lam * kap` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&2 * lam * kap * kap = &1` THEN CONV_TAC REAL_RING;
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The 1-form of the field on the whole model is (mu / |y|^2) y with one     *)
(* constant mu (continuity, P2BKG_PFORM_CLOSED, and connectedness of real^3  *)
(* minus the origin); its transformation under maps with a common 1-jet; the *)
(* 1-form of a lifted field in base terms, and its sign change under the     *)
(* deck map.                                                                 *)
(* ------------------------------------------------------------------------- *)

let P2BX1_MODEL_MU_CONST = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (X:A->real^3) (e:real^3->A) lam.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\ &0 < lam /\
     p2b_parallel_on atlas G (topspace top) X /\
     (!x. x IN topspace top ==> X x dot (G x ** X x) = &1) /\
     (!y. ~(y = vec 0)
          ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\ mfd_param top atlas s e) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas e G y = lam %% cylinder_flow (&0) y)
     ==> ?mu. mu pow 2 = &2 * lam /\
              !y. ~(y = vec 0) ==> p2bkg_pform atlas G X e y = (mu / norm y pow 2) % y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    LABEL_TAC "loc" (el 5 (CONJUNCTS th)) THEN LABEL_TAC "pb" (el 6 (CONJUNCTS th))) THEN
  SUBGOAL_THEN
   `!y. ~(y = vec 0)
        ==> ?mu. mu pow 2 = &2 * lam /\
                 p2bkg_pform atlas (G:A->real^3^3) (X:A->real^3) (e:real^3->A) y =
                 (mu / norm y pow 2) % y`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MP (SPEC `y:real^3` th) (ASSUME `~(y:real^3 = vec 0)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC P2BX1_MODEL_FIELD THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `s:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN USE_THEN "pb" MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `m = \y. p2bkg_pform atlas (G:A->real^3^3) (X:A->real^3) (e:real^3->A) y dot y` THEN
  SUBGOAL_THEN `!y. ~(y = vec 0)
                    ==> (m:real^3->real) y pow 2 = &2 * lam /\
                        p2bkg_pform atlas (G:A->real^3^3) (X:A->real^3) (e:real^3->A) y =
                        (m y / norm y pow 2) % y`
  (LABEL_TAC "mm") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "pt" (fun th -> MP_TAC(MP (SPEC `y:real^3` th) (ASSUME `~(y:real^3 = vec 0)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `mu:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(m:real^3->real) y = mu` (fun th -> ASM_REWRITE_TAC[th]) THEN
    EXPAND_TAC "m" THEN ASM_REWRITE_TAC[DOT_LMUL; NORM_POW_2] THEN
    SUBGOAL_THEN `~((y:real^3) dot y = &0)` MP_TAC THENL
     [ASM_REWRITE_TAC[DOT_EQ_0]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  (* continuity of m *)
  SUBGOAL_THEN `(\y. lift((m:real^3->real) y)) continuous_on ((:real^3) DIFF {vec 0})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (fun th -> MP_TAC(MP (SPEC `y:real^3` th) (ASSUME `~(y:real^3 = vec 0)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                   `X:A->real^3`; `topspace top:A->bool`; `s:real^3->bool`; `e:real^3->A`]
                  P2BKG_PFORM_CLOSED) THEN
    ASM_REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN MESON_TAC[OPEN_IN_SUBSET];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[smooth_map_on] THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[continuously_differentiable] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\y. lift((m:real^3->real) y)) continuous_on s` MP_TAC THENL
     [EXPAND_TAC "m" THEN REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
      REWRITE_TAC[ETA_AX] THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID];
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. lift((m:real^3->real) y)`; `(:real^3) DIFF {vec 0}`]
                CONTINUOUS_DISCRETE_RANGE_CONSTANT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONNECTED_PUNCTURED_UNIVERSE; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ABBREV_TAC `r = sqrt(&2 * lam)` THEN
    SUBGOAL_THEN `&0 < r /\ r pow 2 = &2 * lam` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[LIFT_EQ; GSYM LIFT_SUB; NORM_LIFT] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs((m:real^3->real) y) = r /\ abs(m z) = r` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `abs((m:real^3->real) y) = abs r /\ abs(m z) = abs r` MP_TAC THENL
       [ALL_TAC; ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`]] THEN
      REWRITE_TAC[REAL_EQ_SQUARE_ABS] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "mm" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `y:real^3` th)
        (ASSUME `~(y:real^3 = vec 0)`))]) THEN
      USE_THEN "mm" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `z:real^3` th)
        (ASSUME `~(z:real^3 = vec 0)`))]);
      ALL_TAC] THEN
    UNDISCH_TAC `~((m:real^3->real) z = m y)` THEN
    UNDISCH_TAC `abs((m:real^3->real) y) = r` THEN UNDISCH_TAC `abs((m:real^3->real) z) = r` THEN
    UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^1` (LABEL_TAC "const")) THEN
  SUBGOAL_THEN `~(basis 1:real^3 = vec 0)` ASSUME_TAC THENL
   [SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  EXISTS_TAC `drop a` THEN CONJ_TAC THENL
   [USE_THEN "const" (MP_TAC o SPEC `basis 1:real^3`) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING; ASSUME `~(basis 1:real^3 = vec 0)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LIFT_DROP] THEN
    USE_THEN "mm" (fun th -> ACCEPT_TAC(CONJUNCT1(MP (SPEC `basis 1:real^3` th)
      (ASSUME `~(basis 1:real^3 = vec 0)`))));
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "const" (MP_TAC o SPEC `y:real^3`) THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_SING; ASSUME `~(y:real^3 = vec 0)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[LIFT_DROP] THEN
    USE_THEN "mm" (fun th -> ACCEPT_TAC(CONJUNCT2(MP (SPEC `y:real^3` th)
      (ASSUME `~(y:real^3 = vec 0)`))))]);;

(* The 1-forms of two maps with a common point and related differentials. *)

let P2BX1_PFORM_JET = prove
 (`!(atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (X:A->real^3) (e1:real^3->A) e2
    y1 y2 (M:real^3->real^3).
     e1 y1 = e2 y2 /\ transp(g(e2 y2)) = g(e2 y2) /\ linear M /\
     linear(frechet_derivative (\z. SND(chart_at atlas (e2 y2)) (e2 z)) (at y2)) /\
     frechet_derivative (\z. SND(chart_at atlas (e2 y2)) (e1 z)) (at y1) =
     frechet_derivative (\z. SND(chart_at atlas (e2 y2)) (e2 z)) (at y2) o M
     ==> p2bkg_pform atlas g X e1 y1 = transp(matrix M) ** p2bkg_pform atlas g X e2 y2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `X:A->real^3`;
                 `e2:real^3->A`; `y2:real^3`] P2BX1_PFORM_MATRIX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`; `X:A->real^3`;
                 `e1:real^3->A`; `y1:real^3`] P2BX1_PFORM_MATRIX) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; MATRIX_TRANSP_MUL; GSYM MATRIX_VECTOR_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The 1-form of a lifted vector family in base terms (P2BX1_PFORM_LIFT) and *)
(* its sign change under a deck map that reverses the family                 *)
(* (P2BX1_PFORM_DECK).                                                       *)
(* ------------------------------------------------------------------------- *)

let P2BX1_PFORM_LIFT = prove
 (`!topc top (atlas:((B->bool)#(B->real^3))->bool) (f:A->B) (g:B->real^3^3) (V:A->real^3)
    s (e:real^3->A) y.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\
     mfd_param topc (mfd_lift_atlas topc top f atlas) s e /\ y IN s
     ==> p2bkg_pform (mfd_lift_atlas topc top f atlas)
           (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g)
           (mfd_lift_vec topc top f atlas V) e y =
         transp(matrix(frechet_derivative (\z. SND(chart_at atlas (f(e y))) (f(e z))) (at y))) **
         (g(f(e y)) ** V(e y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)) /\
                continuous_map (topc,top) f /\
                riemannian_metric (mfd_lift_atlas topc top f atlas)
                  (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f
                                       (g:B->real^3^3))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MFDL_ATLAS; MFDL_LH_CONTINUOUS; MFDL_RIEMANNIAN]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace topc` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (e:real^3->A) s SUBSET topspace topc` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:A->B) ((e:real^3->A) y) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`]
                  CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(e:real^3->A) y IN topspace topc` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the base map f o e is a parametrization near y *)
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `(e:real^3->A) y`]
                MFDL_LH_SHEET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open {z | z IN s /\ (e:real^3->A) z IN S}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
    EXISTS_TAC `s:real^3->bool` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{z | z IN s /\ (e:real^3->A) z IN S} =
                    {z | z IN topspace (subtopology euclidean s) /\ e z IN S}` SUBST1_TAC THENL
       [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `topc:A topology` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM OPEN_IN] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `f:A->B`; `S:A->bool`] P2BX1_SHEET_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `sig:B->A`) THEN
  SUBGOAL_THEN `mfd_param top atlas {z | z IN s /\ (e:real^3->A) z IN S} ((f:A->B) o e)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`topc:A topology`; `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)`;
                          `S:A->bool`; `IMAGE (f:A->B) S`; `sig:B->A`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `s:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  (* the charts *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(f:A->B) ((e:real^3->A) y)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c0 = chart_at (atlas:((B->bool)#(B->real^3))->bool) ((f:A->B) ((e:real^3->A) y))` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `f:A->B`; `(e:real^3->A) y`] MFDL_LIFT_BASE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c1 = mfd_lift_base topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)
                                 ((e:real^3->A) y)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `S1:A->bool` STRIP_ASSUME_TAC))) THEN
  (* the derivative D0 of the base representative *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `{z | z IN s /\ (e:real^3->A) z IN S}`; `(f:A->B) o (e:real^3->A)`;
                 `c0:(B->bool)#(B->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `N0 = {z | z IN {z | z IN s /\ (e:real^3->A) z IN S} /\
                        (f:A->B) (e z) IN FST (c0:(B->bool)#(B->real^3))}` THEN
  SUBGOAL_THEN `(y:real^3) IN N0` ASSUME_TAC THENL
   [EXPAND_TAC "N0" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. SND (c0:(B->bool)#(B->real^3)) ((f:A->B) ((e:real^3->A) z))) differentiable at y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`N0:real^3->bool`;
                   `\z. SND (c0:(B->bool)#(B->real^3)) ((f:A->B) ((e:real^3->A) z))`;
                   `y:real^3`; `vec 0:real^3`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D0 = frechet_derivative
                     (\z. SND (c0:(B->bool)#(B->real^3)) ((f:A->B) ((e:real^3->A) z))) (at y)` THEN
  SUBGOAL_THEN `linear (D0:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "D0" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `x = (f:A->B) ((e:real^3->A) y)` THEN
  ABBREV_TAC `K = chart_jac (c0:(B->bool)#(B->real^3)) c1 (x:B)` THEN
  SUBGOAL_THEN `linear (K:real^3->real^3) /\ linear (chart_jac (c1:(B->bool)#(B->real^3)) c0 (x:B)) /\
                (!v. chart_jac c1 c0 x (K v) = v)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `FST (c0:(B->bool)#(B->real^3))`; `SND (c0:(B->bool)#(B->real^3))`;
                     `FST (c1:(B->bool)#(B->real^3))`; `SND (c1:(B->bool)#(B->real^3))`;
                     `x:B`] CHART_JAC_LINEAR) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `FST (c1:(B->bool)#(B->real^3))`; `SND (c1:(B->bool)#(B->real^3))`;
                     `FST (c0:(B->bool)#(B->real^3))`; `SND (c0:(B->bool)#(B->real^3))`;
                     `x:B`] CHART_JAC_LINEAR) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER];
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `FST (c0:(B->bool)#(B->real^3))`; `SND (c0:(B->bool)#(B->real^3))`;
                     `FST (c1:(B->bool)#(B->real^3))`; `SND (c1:(B->bool)#(B->real^3))`;
                     `x:B`] CHART_JAC_INVERSE) THEN
      ASM_REWRITE_TAC[PAIR; IN_INTER; FUN_EQ_THM; o_THM]];
    ALL_TAC] THEN
  (* D1 = K o D0 *)
  SUBGOAL_THEN
   `frechet_derivative (\z. SND (chart_at (mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)) ((e:real^3->A) y))
                               (e z)) (at y) = (K:real^3->real^3) o (D0:real^3->real^3)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SND; o_THM] THEN
    TRANS_TAC EQ_TRANS
     `frechet_derivative
        (\z. chart_trans (c0:(B->bool)#(B->real^3)) c1
               (SND c0 ((f:A->B) ((e:real^3->A) z)))) (at y)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `N0:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN EXPAND_TAC "N0" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                     `FST (c0:(B->bool)#(B->real^3))`; `SND (c0:(B->bool)#(B->real^3))`;
                     `FST (c1:(B->bool)#(B->real^3))`; `SND (c1:(B->bool)#(B->real^3))`;
                     `(f:A->B) ((e:real^3->A) z)`] CHART_TRANS_AT) THEN
      ASM_REWRITE_TAC[PAIR];
      ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `u:real^3` THEN
    MP_TAC(ISPECL [`\z. SND (c0:(B->bool)#(B->real^3)) ((f:A->B) ((e:real^3->A) z))`;
                   `chart_trans (c0:(B->bool)#(B->real^3)) c1`; `y:real^3`; `u:real^3`]
                  LRG_FRECHET_DERIVATIVE_CHAIN) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST (c0:(B->bool)#(B->real^3))`; `SND (c0:(B->bool)#(B->real^3))`;
                   `FST (c1:(B->bool)#(B->real^3))`; `SND (c1:(B->bool)#(B->real^3))`;
                   `x:B`] CHART_TRANS_HAS_DERIVATIVE) THEN
    ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_TAC THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[differentiable];
      ALL_TAC] THEN
    BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the metric and the vector at e y *)
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `f:A->B`; `g:B->real^3^3`; `S1:A->bool`; `c1:(B->bool)#(B->real^3)`;
                 `(e:real^3->A) y`] MFDL_PULLBACK_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `FST (c1:(B->bool)#(B->real^3))`; `SND (c1:(B->bool)#(B->real^3))`;
                 `FST (c0:(B->bool)#(B->real^3))`; `SND (c0:(B->bool)#(B->real^3))`;
                 `g:B->real^3^3`; `x:B`] METRIC_LOCAL_JAC) THEN
  ASM_REWRITE_TAC[PAIR; IN_INTER] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`;
                 `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)`;
                 `mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B)
                                      (g:B->real^3^3)`; `(e:real^3->A) y`]
                RIEMANNIAN_METRIC_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)`;
                 `mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas (f:A->B)
                                      (g:B->real^3^3)`;
                 `mfd_lift_vec topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool) V`;
                 `e:real^3->A`; `y:real^3`] P2BX1_PFORM_MATRIX) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[mfd_lift_vec] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; MATRIX_TRANSP_MUL; GSYM MATRIX_VECTOR_MUL_ASSOC; MATRIX_WORKS] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `!v:real^3. transp(matrix(K:real^3->real^3)) **
                           transp(matrix(chart_jac (c1:(B->bool)#(B->real^3)) c0 (x:B))) ** v = v`
  (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM MATRIX_TRANSP_MUL] THEN
  ASM_SIMP_TAC[GSYM MATRIX_COMPOSE] THEN
  SUBGOAL_THEN `chart_jac (c1:(B->bool)#(B->real^3)) c0 (x:B) o (K:real^3->real^3) = (\v. v)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REWRITE_TAC[MATRIX_ID; TRANSP_MAT; MATRIX_VECTOR_MUL_LID]);;


(* A deck map reversing the vectors reverses the 1-form. *)

let P2BX1_PFORM_DECK = prove
 (`!topc top (atlas:((B->bool)#(B->real^3))->bool) (f:A->B) (g:B->real^3^3) (V:A->real^3)
    (tau:A->A) s (e:real^3->A) y.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     riemannian_metric atlas g /\
     homeomorphic_maps (topc,topc) (tau,tau) /\ (!w. w IN topspace topc ==> f(tau w) = f w) /\
     (!w. w IN topspace topc ==> V(tau w) = --(V w)) /\
     mfd_param topc (mfd_lift_atlas topc top f atlas) s e /\ y IN s
     ==> p2bkg_pform (mfd_lift_atlas topc top f atlas)
           (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g)
           (mfd_lift_vec topc top f atlas V) (tau o e) y =
         --(p2bkg_pform (mfd_lift_atlas topc top f atlas)
              (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g)
              (mfd_lift_vec topc top f atlas V) e y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B)
                                              (atlas:((B->bool)#(B->real^3))->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `IMAGE (e:real^3->A) s SUBSET topspace topc` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_param topc (mfd_lift_atlas topc top (f:A->B)
                                  (atlas:((B->bool)#(B->real^3))->bool)) s ((tau:A->A) o e)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`topc:A topology`;
                          `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)`;
                          `topspace topc:A->bool`; `topspace topc:A->bool`; `tau:A->A`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX1_DECK_DIFFEO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `f:A->B`; `g:B->real^3^3`; `V:A->real^3`; `s:real^3->bool`;
                 `(tau:A->A) o (e:real^3->A)`; `y:real^3`] P2BX1_PFORM_LIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `f:A->B`; `g:B->real^3^3`; `V:A->real^3`; `s:real^3->bool`;
                 `e:real^3->A`; `y:real^3`] P2BX1_PFORM_LIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace topc` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. SND(chart_at atlas ((f:A->B) ((e:real^3->A) y)))
                             (f((tau:A->A) (e z)))) (at y) =
    frechet_derivative (\z. SND(chart_at (atlas:((B->bool)#(B->real^3))->bool) (f(e y)))
                             (f(e z))) (at y)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:real^3->A) z IN topspace topc` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG]]);;

(* ------------------------------------------------------------------------- *)
(* The twisted model carries no unit parallel field.  If e(twist y) = e(y)   *)
(* then the radial 1-form (mu/|y|^2) y of the field equals its own pullback  *)
(* by twist, which is its negative.                                          *)
(* ------------------------------------------------------------------------- *)

let P2BX1_PFORM_LOCAL = prove
 (`!(atlas:((A->bool)#(A->real^3))->bool) (g:A->real^3^3) (X:A->real^3) (e1:real^3->A) e2 S y.
     open S /\ y IN S /\ (!z. z IN S ==> e1 z = e2 z)
     ==> p2bkg_pform atlas g X e1 y = p2bkg_pform atlas g X e2 y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bkg_pform] THEN
  SUBGOAL_THEN `(e1:real^3->A) y = e2 y` SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frechet_derivative (\z. SND(chart_at atlas ((e2:real^3->A) y)) ((e1:real^3->A) z)) (at y) =
    frechet_derivative (\z. SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) (e2 y)) (e2 z))
                       (at y)`
  (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC LRG_FRECHET_DERIVATIVE_EQ_OPEN THEN EXISTS_TAC `S:real^3->bool` THEN
  ASM_SIMP_TAC[]);;

(* The derivative of the twist and its transpose on the radial vector. *)

let P2BX1_TWIST_HAS_DERIVATIVE = prove
 (`!y:real^3.
     ~(y = vec 0)
     ==> (rfs_twist has_derivative
          (\h. --(inv(norm y pow 2) % h - (&2 * (y dot h) / (norm y pow 2) pow 2) % y))) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `rfs_twist = (\z:real^3. --(inv(norm z pow 2) % z))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; rfs_twist]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_NEG THEN ASM_SIMP_TAC[RFB_INVERSION_HAS_DERIVATIVE]);;

let P2BX1_TWIST_TRANSP_RADIAL = prove
 (`!y:real^3.
     ~(y = vec 0)
     ==> transp(matrix(frechet_derivative rfs_twist (at y))) ** y = inv(norm y pow 2) % y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2BX1_TWIST_HAS_DERIVATIVE) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  SUBGOAL_THEN
   `linear (\h:real^3. --(inv(norm y pow 2) % h - (&2 * (y dot h) / (norm y pow 2) pow 2) % y))`
  ASSUME_TAC THENL [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_EQ_LDOT] THEN X_GEN_TAC `h:real^3` THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[DOT_MATRIX_TRANSP_LMUL] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  REWRITE_TAC[DOT_RNEG; DOT_RSUB; DOT_RMUL; DOT_LMUL; NORM_POW_2] THEN
  SUBGOAL_THEN `~((y:real^3) dot y = &0)` MP_TAC THENL [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_FIELD);;

(* The twisted model is excluded. *)

let P2BX1_TWIST_EXCLUDED = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (X:A->real^3) (e:real^3->A)
    lam mu.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\ &0 < lam /\
     mu pow 2 = &2 * lam /\
     (!y. ~(y = vec 0)
          ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\ mfd_param top atlas s e) /\
     (!y. ~(y = vec 0) ==> p2bkg_pform atlas G X e y = (mu / norm y pow 2) % y) /\
     (!y. ~(y = vec 0) ==> e(rfs_twist y) = e y)
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "loc" (el 4 (CONJUNCTS th)) THEN
    LABEL_TAC "om" (el 5 (CONJUNCTS th)) THEN LABEL_TAC "tw" (el 6 (CONJUNCTS th))) THEN
  ABBREV_TAC `y:real^3 = basis 1` THEN
  SUBGOAL_THEN `~(y:real^3 = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `~(rfs_twist y = vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_twist; VECTOR_NEG_EQ_0; VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_POW_EQ_0;
                NORM_EQ_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the parametrization near twist y *)
  USE_THEN "loc" (fun th -> MP_TAC(MP (SPEC `rfs_twist y` th) (ASSUME `~(rfs_twist y = vec 0)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `e:real^3->A`; `chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) (rfs_twist y))`]
                P2BKG_PARAM_CHART_SMOOTH) THEN
  SUBGOAL_THEN `(e:real^3->A) (rfs_twist y) IN topspace top` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `IMAGE (e:real^3->A) s SUBSET topspace top` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `(e:real^3->A) (rfs_twist y)`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. SND (chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) (rfs_twist y))) (e z))
    differentiable at (rfs_twist y)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`{z | z IN s /\ (e:real^3->A) z IN
                          FST (chart_at (atlas:((A->bool)#(A->real^3))->bool) (e (rfs_twist y)))}`;
                   `\z. SND (chart_at (atlas:((A->bool)#(A->real^3))->bool)
                                      ((e:real^3->A) (rfs_twist y))) (e z)`;
                   `rfs_twist y`; `vec 0:real^3`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_twist differentiable at (y:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[P2BX1_TWIST_HAS_DERIVATIVE]; ALL_TAC] THEN
  (* omega(y) = omega_{e o twist}(y) = transp(D twist) omega(twist y) *)
  SUBGOAL_THEN
   `p2bkg_pform atlas (G:A->real^3^3) (X:A->real^3) (e:real^3->A) y =
    transp(matrix(frechet_derivative rfs_twist (at y))) **
    p2bkg_pform atlas G X e (rfs_twist y)`
  MP_TAC THENL
   [TRANS_TAC EQ_TRANS `p2bkg_pform atlas (G:A->real^3^3) (X:A->real^3)
                          ((e:real^3->A) o rfs_twist) y` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2BX1_PFORM_LOCAL THEN
      EXISTS_TAC `{z:real^3 | ~(z = vec 0)}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; o_THM] THEN
      REWRITE_TAC[SET_RULE `{z:real^3 | ~(z = vec 0)} = (:real^3) DELETE vec 0`] THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC P2BX1_PFORM_JET THEN REWRITE_TAC[o_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[RIEMANNIAN_METRIC_POS]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[has_derivative; P2BX1_TWIST_HAS_DERIVATIVE; FRECHET_DERIVATIVE_AT];
                    ALL_TAC] THEN
    CONJ_TAC THENL [MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN X_GEN_TAC `u:real^3` THEN
    MP_TAC(ISPECL [`rfs_twist`;
                   `\z. SND (chart_at (atlas:((A->bool)#(A->real^3))->bool)
                                      ((e:real^3->A) (rfs_twist y))) (e z)`;
                   `y:real^3`; `u:real^3`] LRG_FRECHET_DERIVATIVE_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "om" (fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th) (ASSUME `~(y:real^3 = vec 0)`)]) THEN
  USE_THEN "om" (fun th -> REWRITE_TAC[MP (SPEC `rfs_twist y` th) (ASSUME `~(rfs_twist y = vec 0)`)]) THEN
  SUBGOAL_THEN `(mu / norm(rfs_twist y) pow 2) % rfs_twist y = --(mu % (y:real^3))` SUBST1_TAC THENL
   [REWRITE_TAC[rfs_twist; NORM_NEG; NORM_MUL; VECTOR_MUL_RNEG; VECTOR_MUL_ASSOC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    SUBGOAL_THEN `~(norm(y:real^3) = &0)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RNEG; MATRIX_VECTOR_MUL_RMUL] THEN
  ASM_SIMP_TAC[P2BX1_TWIST_TRANSP_RADIAL] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; real_div; GSYM VECTOR_NEG_MINUS1] THEN
  DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v dot y`) THEN BETA_TAC THEN
  REWRITE_TAC[DOT_LMUL; DOT_LNEG] THEN
  SUBGOAL_THEN `~((y:real^3) dot y = &0) /\ ~(norm(y:real^3) = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0; NORM_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `mu pow 2 = &2 * lam` THEN UNDISCH_TAC `&0 < lam` THEN
  REWRITE_TAC[NORM_POW_2] THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Linear algebra for the deck map in the model.  Conformal linear maps; the *)
(* reflection in the plane orthogonal to y0 and the derivative of the        *)
(* inversion; the maps c A inv (A orthogonal) are isometries of lam cyl 0    *)
(* and diffeomorphisms of real^3 minus the origin; an involution without     *)
(* fixed vectors is -id.                                                     *)
(* ------------------------------------------------------------------------- *)

(* A linear map stretching all lengths by k with transp(M) z = -k^2 y maps y *)
(* to -z.                                                                    *)

let P2BX1_CONFORMAL_DOT = prove
 (`!(M:real^3->real^3) k.
     linear M /\ (!u. norm(M u) = k * norm u)
     ==> !u v. M u dot M v = k pow 2 * (u dot v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^3. (M:real^3->real^3) w dot M w = k pow 2 * (w dot w)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM NORM_POW_2] THEN ASM_REWRITE_TAC[REAL_POW_MUL];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `u + v:real^3`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `u:real^3`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `v:real^3`) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th]) THEN
  REWRITE_TAC[DOT_LADD; DOT_RADD] THEN REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING);;

let P2BX1_CONFORMAL_IMAGE = prove
 (`!(M:real^3->real^3) k (y:real^3) z.
     linear M /\ &0 < k /\ (!u. norm(M u) = k * norm u) /\
     transp(matrix M) ** z = --(k pow 2 % y)
     ==> M y = --z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "nm") (LABEL_TAC "tr")))) THEN
  MP_TAC(ISPECL [`M:real^3->real^3`; `k:real`] P2BX1_CONFORMAL_DOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "dot") THEN
  SUBGOAL_THEN `!v:real^3. (M:real^3->real^3) v dot (M (y:real^3) + (z:real^3)) = &0`
  (LABEL_TAC "orth") THENL
   [GEN_TAC THEN REWRITE_TAC[DOT_RADD] THEN USE_THEN "dot" (fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `(M:real^3->real^3) v dot z = v dot (transp(matrix M) ** z)` SUBST1_TAC THENL
     [SUBGOAL_THEN `(M:real^3->real^3) v = matrix M ** v` SUBST1_TAC THENL
       [ASM_SIMP_TAC[MATRIX_WORKS]; REWRITE_TAC[DOT_MATRIX_TRANSP_RMUL]];
      USE_THEN "tr" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[DOT_RNEG; DOT_RMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `M:real^3->real^3` LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN REWRITE_TAC[GSYM NORM_EQ_0] THEN
    USE_THEN "nm" (MP_TAC o SPEC `a - b:real^3`) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th]) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(M:real^3->real^3) y + z`) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^3` (LABEL_TAC "vv")) THEN
  USE_THEN "orth" (MP_TAC o SPEC `v:real^3`) THEN
  USE_THEN "vv" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[DOT_EQ_0] THEN
  VECTOR_ARITH_TAC);;

(* The reflection in the plane orthogonal to y0 and the inversion. *)

let P2BX1_REFL_FACTS = prove
 (`!y0:real^3.
     ~(y0 = vec 0)
     ==> linear (\v. v - (&2 * (y0 dot v) / (y0 dot y0)) % y0) /\
         (!v. (v - (&2 * (y0 dot v) / (y0 dot y0)) % y0) -
              (&2 * (y0 dot (v - (&2 * (y0 dot v) / (y0 dot y0)) % y0)) / (y0 dot y0)) % y0 = v) /\
         (!v. norm(v - (&2 * (y0 dot v) / (y0 dot y0)) % y0) = norm v) /\
         y0 - (&2 * (y0 dot y0) / (y0 dot y0)) % y0 = --y0 /\
         (!h. inv(norm y0 pow 2) % h - (&2 * (y0 dot h) / (norm y0 pow 2) pow 2) % y0 =
              inv(norm y0 pow 2) % (h - (&2 * (y0 dot h) / (y0 dot y0)) % y0))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((y0:real^3) dot y0 = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; DOT_RADD; DOT_RMUL] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `((x:real^3) + y) - a % (z:real^3) = (x - b % z) + (y - c % z) <=>
                              (b + c - a) % z = vec 0`;
                VECTOR_ARITH `c % (x:real^3) - a % (z:real^3) = c % (x - b % z) <=>
                              (c * b - a) % z = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~((y0:real^3) dot y0 = &0)` THEN CONV_TAC REAL_FIELD;
    GEN_TAC THEN REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN
    REWRITE_TAC[VECTOR_ARITH `((v:real^3) - a % (y:real^3)) - b % y = v <=> (a + b) % y = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~((y0:real^3) dot y0 = &0)` THEN CONV_TAC REAL_FIELD;
    GEN_TAC THEN REWRITE_TAC[NORM_EQ; DOT_LSUB; DOT_RSUB; DOT_LMUL; DOT_RMUL] THEN
    REWRITE_TAC[DOT_SYM] THEN
    UNDISCH_TAC `~((y0:real^3) dot y0 = &0)` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[VECTOR_ARITH `(y:real^3) - a % y = --y <=> (a - &2) % y = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~((y0:real^3) dot y0 = &0)` THEN CONV_TAC REAL_FIELD;
    GEN_TAC THEN REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC; NORM_POW_2] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~((y0:real^3) dot y0 = &0)` THEN CONV_TAC REAL_FIELD]);;

(* Pullbacks of scalar multiples and by matrices. *)

let P2BX1_MPULLBACK_CMUL = prove
 (`!(h:real^N->real^N) (G:real^N->real^N^N) c y.
     mpullback h (\w. c %% G w) y = c %% mpullback h G y`,
  REWRITE_TAC[mpullback; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL]);;

let P2BX1_MPULLBACK_MATRIX = prove
 (`!(Q:real^N^N) (G:real^N->real^N^N) y.
     mpullback (\x. Q ** x) G y = transp Q ** G (Q ** y) ** Q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mpullback] THEN
  SUBGOAL_THEN `frechet_derivative (\x:real^N. (Q:real^N^N) ** x) (at (y:real^N)) = (\x. Q ** x)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR];
    REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL]]);;

(* Invertible matrices are diffeomorphisms of real^3 minus the origin. *)

let P2BX1_LINEAR_DIFFEO_PUNCT = prove
 (`!(Q:real^3^3) Q'.
     (!v. Q' ** (Q ** v) = v) /\ (!v. Q ** (Q' ** v) = v)
     ==> diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
                           (\v. Q ** v) (\v. Q' ** v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN
  SIMP_TAC[OPEN_DELETE; OPEN_UNIV; CMPW_LINEAR_SMOOTH] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_UNIV] THEN CONJ_TAC THEN
  X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MATRIX_VECTOR_MUL_RZERO];
    DISCH_TAC THEN EXISTS_TAC `(Q':real^3^3) ** z` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MATRIX_VECTOR_MUL_RZERO];
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MATRIX_VECTOR_MUL_RZERO];
    DISCH_TAC THEN EXISTS_TAC `(Q:real^3^3) ** z` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MATRIX_VECTOR_MUL_RZERO]]);;

(* The matrix c A of a dilated orthogonal map and its inverse. *)

let P2BX1_ORTHO_CMUL = prove
 (`!(A:real^3->real^3) c.
     orthogonal_transformation A /\ &0 < c
     ==> (!v. (c %% matrix A) ** v = c % A v) /\
         (!v. (inv c %% transp(matrix A)) ** ((c %% matrix A) ** v) = v) /\
         (!v. (c %% matrix A) ** ((inv c %% transp(matrix A)) ** v) = v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear (A:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  SUBGOAL_THEN `transp(matrix(A:real^3->real^3)) ** matrix A = mat 1 /\
                matrix A ** transp(matrix A) = mat 1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX; orthogonal_matrix]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN GEN_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_LMUL; MATRIX_WORKS];
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID; MATRIX_VECTOR_MUL_LID];
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; MATRIX_CMUL_LID; MATRIX_VECTOR_MUL_LID]]);;

(* A dilated orthogonal map is an isometry of lam cyl 0. *)

let P2BX1_CYL0_CONFORMAL = prove
 (`!(A:real^3->real^3) c lam z.
     orthogonal_transformation A /\ &0 < c /\ ~(z = vec 0)
     ==> mpullback (\x. (c %% matrix A) ** x) (\w. lam %% cylinder_flow (&0) w) z =
         lam %% cylinder_flow (&0) z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear (A:real^3->real^3) /\ (!v. norm(A v) = norm v)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  SUBGOAL_THEN `transp(matrix(A:real^3->real^3)) ** matrix A = mat 1` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX; orthogonal_matrix]; ALL_TAC] THEN
  REWRITE_TAC[P2BX1_MPULLBACK_MATRIX; LRG_CYL0_EQ] THEN
  SUBGOAL_THEN `norm((c %% matrix(A:real^3->real^3)) ** z) = c * norm z` SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATRIX_VECTOR_LMUL; MATRIX_WORKS; NORM_MUL;
                 REAL_ARITH `&0 < c ==> abs c = c`];
    ALL_TAC] THEN
  REWRITE_TAC[TRANSP_MATRIX_CMUL; MATRIX_MUL_LMUL; MATRIX_MUL_RMUL; MATRIX_CMUL_ASSOC;
              MATRIX_MUL_LID] THEN
  ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(norm(z:real^3) = &0)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD);;

(* The maps y |-> c A(y / |y|^2), A orthogonal, c > 0. *)

let P2BX1_INV_ORTHO = prove
 (`!(A:real^3->real^3) c lam.
     orthogonal_transformation A /\ &0 < c
     ==> diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0)
           (\y. c % A(inv(norm y pow 2) % y))
           ((\y. inv(norm y pow 2) % y) o (\v. (inv c %% transp(matrix A)) ** v)) /\
         (!y. ~(y = vec 0)
              ==> mpullback (\y. c % A(inv(norm y pow 2) % y))
                            (\z. lam %% cylinder_flow (&0) z) y =
                  lam %% cylinder_flow (&0) y) /\
         (!y. ~(y = vec 0)
              ==> ((\y. c % A(inv(norm y pow 2) % y)) has_derivative
                   (\h. c % A(inv(norm y pow 2) % h -
                              (&2 * (y dot h) / (norm y pow 2) pow 2) % y)))
                  (at y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^3->real^3`; `c:real`] P2BX1_ORTHO_CMUL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^3. c % A(inv(norm y pow 2) % y)) =
                (\v. (c %% matrix(A:real^3->real^3)) ** v) o (\y. inv(norm y pow 2) % y)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `(:real^3) DELETE vec 0` THEN REWRITE_TAC[STEX_DIFFEOMORPHISM_INVERSION] THEN
    MATCH_MP_TAC P2BX1_LINEAR_DIFFEO_PUNCT THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(inv(norm y pow 2) % y:real^3 = vec 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; REAL_POW_EQ_0; NORM_EQ_0]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\y:real^3. inv(norm y pow 2) % y`;
                   `\v:real^3. (c %% matrix(A:real^3->real^3)) ** v`;
                   `\z:real^3. lam %% cylinder_flow (&0) z`; `y:real^3`]
                  APX_MPULLBACK_CHAIN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[differentiable] THENL
       [ASM_MESON_TAC[RFB_INVERSION_HAS_DERIVATIVE];
        EXISTS_TAC `\v:real^3. (c %% matrix(A:real^3->real^3)) ** v` THEN
        MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    TRANS_TAC EQ_TRANS
     `mpullback (\y:real^3. inv(norm y pow 2) % y) (\z. lam %% cylinder_flow (&0) z) y` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2A_MPULLBACK_PT THEN BETA_TAC THEN
      MATCH_MP_TAC P2BX1_CYL0_CONFORMAL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[P2BX1_MPULLBACK_CMUL] THEN AP_TERM_TAC THEN
      REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC APX_INVERSION_CYL0 THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(\h:real^3. c % A(inv(norm y pow 2) % h -
                                    (&2 * (y dot h) / (norm y pow 2) pow 2) % y)) =
                  (\v. (c %% matrix(A:real^3->real^3)) ** v) o
                  (\h. inv(norm y pow 2) % h - (&2 * (y dot h) / (norm y pow 2) pow 2) % y)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[RFB_INVERSION_HAS_DERIVATIVE];
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR]]]);;

(* An involution without nonzero fixed vectors is -id. *)

let P2BX1_INVOL_NOFIX = prove
 (`!(A:real^3->real^3).
     linear A /\ (!v. A(A v) = v) /\ (!v. A v = v ==> v = vec 0)
     ==> !v. A v = --v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(A:real^3->real^3)(v + A v) = v + A v` MP_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th]) THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The deck map in the one-to-one cover model.  At y0 and z0 with tau(e y0)  *)
(* = e z0 the derivatives differ by a conformal map M with M y0 = -z0        *)
(* (metric and 1-form); an explicit isometry T y = c A(y/|y|^2) of lam cyl 0 *)
(* has the same 1-jet; rigidity gives tau o e = e o T; then A = -id          *)
(* (involution, no fixed point), so T is c times the twist                   *)
(* (P2BX1_DECK_FORM).                                                        *)
(* ------------------------------------------------------------------------- *)

(* The metric pullbacks of two maps with a common point and related          *)
(* differentials (metric analogue of P2BX1_PFORM_JET).                       *)

let P2BX1_RFS_PULLBACK_JET = prove
 (`!(atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (e1:real^3->A) e2 y1 y2
    (M:real^3->real^3).
     e1 y1 = e2 y2 /\ linear M /\
     linear(frechet_derivative (\z. SND(chart_at atlas (e2 y2)) (e2 z)) (at y2)) /\
     frechet_derivative (\z. SND(chart_at atlas (e2 y2)) (e1 z)) (at y1) =
     frechet_derivative (\z. SND(chart_at atlas (e2 y2)) (e2 z)) (at y2) o M
     ==> rfs_pullback atlas e1 G y1 =
         transp(matrix M) ** rfs_pullback atlas e2 G y2 ** matrix M`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rfs_pullback; mpullback; o_DEF] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MATRIX_COMPOSE; MATRIX_TRANSP_MUL] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC]);;

(* A congruence of lam cyl 0 at two points is conformal. *)

let P2BX1_CYL0_CONGRUENT = prove
 (`!(M:real^3->real^3) lam (y0:real^3) (z0:real^3).
     linear M /\ &0 < lam /\ ~(y0 = vec 0) /\ ~(z0 = vec 0) /\
     lam %% cylinder_flow (&0) y0 =
     transp(matrix M) ** (lam %% cylinder_flow (&0) z0) ** matrix M
     ==> !u. norm(M u) = (norm z0 / norm y0) * norm u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:real^3` THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\B:real^3^3. (u:real^3) dot (B ** u)`) THEN
  REWRITE_TAC[LRG_CYL0_EQ; MATRIX_CMUL_ASSOC; GSYM MATRIX_VECTOR_MUL_ASSOC;
              DOT_MATRIX_TRANSP_RMUL; MATRIX_VECTOR_LMUL; MATRIX_VECTOR_MUL_LID] THEN
  ASM_SIMP_TAC[MATRIX_WORKS; DOT_RMUL] THEN
  REWRITE_TAC[NORM_POW_2] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
  SIMP_TAC[NORM_POS_LE; REAL_LE_MUL; REAL_LE_DIV; ARITH_EQ] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_DIV; NORM_POW_2] THEN
  SUBGOAL_THEN `~((y0:real^3) dot y0 = &0) /\ ~((z0:real^3) dot z0 = &0) /\ ~(lam = &0)`
  MP_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD);;

let P2BX1_SCALE_SOLVE = prove
 (`!a b (y:real^3) (w:real^3). ~(b = &0) /\ --(a % y) = b % w ==> w = --((a / b) % y)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\v:real^3. inv b % v`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_MUL_RNEG; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let P2BX1_MU_NZ = prove
 (`!lam mu. &0 < lam /\ mu pow 2 = &2 * lam ==> ~(mu = &0)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `mu pow 2 = &2 * lam` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

(* Chart representatives of parametrizations. *)

let P2BX1_PARAM_CHART_DIFFERENTIABLE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) s (e:real^3->A) cc y.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\ cc IN atlas /\
     y IN s /\ e y IN FST cc
     ==> (\z. SND cc (e z)) differentiable at y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (s:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MFD_PARAM_MAPS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `e:real^3->A`; `cc:(A->bool)#(A->real^3)`] P2BKG_PARAM_CHART_SMOOTH) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{z | z IN s /\ (e:real^3->A) z IN FST (cc:(A->bool)#(A->real^3))}`;
                 `\z. SND (cc:(A->bool)#(A->real^3)) ((e:real^3->A) z)`;
                 `y:real^3`; `vec 0:real^3`] LRG_SMOOTH_FRECHET_DIFFERENTIABLE) THEN
  ASM_SIMP_TAC[IN_ELIM_THM]);;

let P2BX1_PARAM_CHART_INVERTIBLE = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) s (e:real^3->A) y.
     smooth_manifold_atlas top atlas /\ mfd_param top atlas s e /\ y IN s
     ==> (\z. SND (chart_at atlas (e y)) (e z)) differentiable at y /\
         linear (frechet_derivative (\z. SND (chart_at atlas (e y)) (e z)) (at y)) /\
         ?D'. linear D' /\
              (!v. D'(frechet_derivative (\z. SND (chart_at atlas (e y)) (e z)) (at y) v) = v) /\
              (!w. frechet_derivative (\z. SND (chart_at atlas (e y)) (e z)) (at y) (D' w) = w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^3->A) y IN topspace top` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (e:real^3->A) s SUBSET topspace top` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(e:real^3->A) y`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `cc = chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) y)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s:real^3->bool`;
                 `e:real^3->A`; `e':A->real^3`; `cc:(A->bool)#(A->real^3)`]
                P2BX1_PARAM_CHART_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (SND (cc:(A->bool)#(A->real^3))) (FST cc INTER IMAGE (e:real^3->A) s)`;
                 `{z | z IN s /\ (e:real^3->A) z IN FST (cc:(A->bool)#(A->real^3))}`;
                 `\z. SND (cc:(A->bool)#(A->real^3)) ((e:real^3->A) z)`;
                 `\u. (e':A->real^3) (chart_inv (cc:(A->bool)#(A->real^3)) u)`;
                 `y:real^3`] LRG_DIFFEO_DERIV) THEN
  MP_TAC(ISPECL [`IMAGE (SND (cc:(A->bool)#(A->real^3))) (FST cc INTER IMAGE (e:real^3->A) s)`;
                 `{z | z IN s /\ (e:real^3->A) z IN FST (cc:(A->bool)#(A->real^3))}`;
                 `\z. SND (cc:(A->bool)#(A->real^3)) ((e:real^3->A) z)`;
                 `\u. (e':A->real^3) (chart_inv (cc:(A->bool)#(A->real^3)) u)`;
                 `y:real^3`] LRG_DIFFEO_INV_LINEAR) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    EXISTS_TAC `frechet_derivative (\u. (e':A->real^3) (chart_inv (cc:(A->bool)#(A->real^3)) u))
                  (at (SND cc ((e:real^3->A) y)))` THEN
    ASM_REWRITE_TAC[]]);;

(* The orthogonal map with the prescribed 1-jet. *)

let P2BX1_REFL = prove
 (`!y0:real^3.
     ~(y0 = vec 0)
     ==> ?R0. linear R0 /\ (!v. R0(R0 v) = v) /\ (!v. norm(R0 v) = norm v) /\ R0 y0 = --y0 /\
              (!h. inv(norm y0 pow 2) % h - (&2 * (y0 dot h) / (norm y0 pow 2) pow 2) % y0 =
                   inv(norm y0 pow 2) % R0 h)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\v:real^3. v - (&2 * (y0 dot v) / (y0 dot y0)) % y0` THEN
  ASM_SIMP_TAC[P2BX1_REFL_FACTS]);;

let P2BX1_DECK_ISOM = prove
 (`!(M:real^3->real^3) (y0:real^3) (z0:real^3).
     linear M /\ (!u. norm(M u) = (norm z0 / norm y0) * norm u) /\ M y0 = --z0 /\
     ~(y0 = vec 0) /\ ~(z0 = vec 0)
     ==> ?A c. orthogonal_transformation A /\ &0 < c /\
               c % A(inv(norm y0 pow 2) % y0) = z0 /\
               (!h. c % A(inv(norm y0 pow 2) % h -
                          (&2 * (y0 dot h) / (norm y0 pow 2) pow 2) % y0) = M h)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `y0:real^3` P2BX1_REFL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R0:real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(y0:real^3) /\ &0 < norm(z0:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  EXISTS_TAC `\u:real^3. (norm(y0:real^3) / norm(z0:real^3)) % (M:real^3->real^3) (R0 u)` THEN
  EXISTS_TAC `norm(y0:real^3) * norm(z0:real^3)` THEN
  ASM_SIMP_TAC[REAL_LT_MUL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
      SUBGOAL_THEN `(\u:real^3. (M:real^3->real^3) (R0 u)) = M o R0` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[]];
      GEN_TAC THEN ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      UNDISCH_TAC `&0 < norm(y0:real^3)` THEN UNDISCH_TAC `&0 < norm(z0:real^3)` THEN
      CONV_TAC REAL_FIELD];
    REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME `linear (R0:real^3->real^3)`)] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_MUL_RNEG] THEN
    REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME `linear (M:real^3->real^3)`);
                MATCH_MP LINEAR_NEG (ASSUME `linear (M:real^3->real^3)`)] THEN
    ASM_REWRITE_TAC[VECTOR_NEG_NEG; VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[VECTOR_MUL_RNEG; VECTOR_NEG_NEG; VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < norm(y0:real^3)` THEN UNDISCH_TAC `&0 < norm(z0:real^3)` THEN
    CONV_TAC REAL_FIELD;
    GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME `linear (R0:real^3->real^3)`)] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MATCH_MP LINEAR_CMUL (ASSUME `linear (M:real^3->real^3)`)] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < norm(y0:real^3)` THEN UNDISCH_TAC `&0 < norm(z0:real^3)` THEN
    CONV_TAC REAL_FIELD]);;

(* Precomposition of a local isometric parametrization with a diffeomorphism *)
(* of real^3 minus the origin.                                               *)

let P2BX1_PRECOMP_PARAMS = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (e:real^3->A) Tm Tm'
    (Gm:real^3->real^3^3).
     smooth_manifold_atlas top atlas /\
     diffeomorphism_on ((:real^3) DELETE vec 0) ((:real^3) DELETE vec 0) Tm Tm' /\
     (!y. ~(y = vec 0)
          ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\ mfd_param top atlas s e) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas e G y = Gm y)
     ==> (!y. ~(y = vec 0)
              ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\
                      mfd_param top atlas s (e o Tm)) /\
         (!y. ~(y = vec 0) ==> rfs_pullback atlas (e o Tm) G y = mpullback Tm Gm y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "loc") (LABEL_TAC "pb")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN
   `!y. ~(y = vec 0)
        ==> ?s. open s /\ s SUBSET {y | ~(y = vec 0)} /\
                mfd_param top atlas s (e:real^3->A) /\
                diffeomorphism_on (IMAGE Tm' s) s (Tm:real^3->real^3) Tm' /\
                y IN IMAGE Tm' s /\ IMAGE Tm' s SUBSET {y | ~(y = vec 0)}`
  (LABEL_TAC "loc2") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((Tm:real^3->real^3) y = vec 0)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `~((Tm:real^3->real^3) y = vec 0)`) o
                    SPEC `(Tm:real^3->real^3) y`) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(:real^3) DELETE vec 0`; `(:real^3) DELETE vec 0`; `Tm:real^3->real^3`;
                     `Tm':real^3->real^3`; `s:real^3->bool`] P2B9S_DIFFEO_ON_RESTRICT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  USE_THEN "loc2" (MP_TAC o C MP (ASSUME `~(y:real^3 = vec 0)`) o SPEC `y:real^3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `IMAGE (Tm':real^3->real^3) s` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[diffeomorphism_on];
      MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
      MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `s:real^3->bool`; `Tm':real^3->real^3`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL]];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                   `s:real^3->bool`; `e:real^3->A`; `IMAGE (Tm':real^3->real^3) s`;
                   `Tm:real^3->real^3`; `Tm':real^3->real^3`; `y:real^3`]
                  P2BX2_RFS_PULLBACK_PRECOMP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC P2A_MPULLBACK_PT THEN USE_THEN "pb" MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* Rigidity for two local isometric parametrizations of the model. *)

let P2BX1_MODEL_RIGID = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (Gm:real^3->real^3^3)
    (e1:real^3->A) e2 y0 w0.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\
     metric_field ((:real^3) DELETE vec 0) Gm /\
     (!y. ~(y = vec 0)
          ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\ mfd_param top atlas s e1) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas e1 G y = Gm y) /\
     (!y. ~(y = vec 0)
          ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\ mfd_param top atlas s e2) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas e2 G y = Gm y) /\
     ~(y0 = vec 0) /\ e1 y0 = w0 /\ e2 y0 = w0 /\
     frechet_derivative (\z. SND(chart_at atlas w0) (e1 z)) (at y0) =
     frechet_derivative (\z. SND(chart_at atlas w0) (e2 z)) (at y0)
     ==> !y. ~(y = vec 0) ==> e1 y = e2 y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open ((:real^3) DELETE vec 0)` ASSUME_TAC THENL
   [SIMP_TAC[OPEN_DELETE; OPEN_UNIV]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SET_RULE `{y:real^3 | ~(y = vec 0)} = (:real^3) DELETE vec 0`]) THEN
  SUBGOAL_THEN
   `!e:real^3->A.
      (!y. ~(y = vec 0)
           ==> ?s. open s /\ y IN s /\ s SUBSET (:real^3) DELETE vec 0 /\ mfd_param top atlas s e) /\
      (!y. ~(y = vec 0) ==> rfs_pullback atlas e G y = Gm y)
      ==> mfd_local_isometry (subtopology euclidean ((:real^3) DELETE vec 0),
                              open_set_atlas ((:real^3) DELETE vec 0)) Gm
                             (top,atlas) G ((:real^3) DELETE vec 0) e`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC P2BX1_PARAM_LISOM THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected ((:real^3) DELETE vec 0)` ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `(:real^3) DELETE vec 0 = (:real^3) DIFF {vec 0}`] THEN
    SIMP_TAC[CONNECTED_PUNCTURED_UNIVERSE; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_differential (open_set_atlas ((:real^3) DELETE vec 0))
                     (atlas:((A->bool)#(A->real^3))->bool) (e1:real^3->A) y0 =
    mfd_differential (open_set_atlas ((:real^3) DELETE vec 0)) atlas (e2:real^3->A) y0`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CMPW_PM_DIFF; IN_DELETE; IN_UNIV]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`subtopology euclidean ((:real^3) DELETE vec 0)`; `open_set_atlas ((:real^3) DELETE vec 0)`;
    `Gm:real^3->real^3^3`; `top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
    `G:A->real^3^3`; `(:real^3) DELETE vec 0`; `e1:real^3->A`; `e2:real^3->A`; `y0:real^3`]
   MFD_LOCAL_ISOMETRY_RIGID) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN; OPEN_SET_ATLAS;
                 RFB_OPEN_SET_RIEMANNIAN; CONNECTED_IN_SUBTOPOLOGY_EUCLIDEAN; SUBSET_REFL;
                 IN_DELETE; IN_UNIV];
    REWRITE_TAC[IN_DELETE; IN_UNIV] THEN MESON_TAC[]]);;

(* The algebra: an orthogonal A with tau o e = e o (c A inv), tau an         *)
(* involution without fixed points and e injective, is -id.                  *)

let P2BX1_DECK_ALGEBRA = prove
 (`!(e:real^3->A) (tau:A->A) (A:real^3->real^3) c.
     orthogonal_transformation A /\ &0 < c /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (e y = e z <=> z = y)) /\
     (!y. ~(y = vec 0) ==> tau(e y) = e(c % A(inv(norm y pow 2) % y))) /\
     (!y. ~(y = vec 0) ==> tau(tau(e y)) = e y /\ ~(tau(e y) = e y))
     ==> !y. ~(y = vec 0) ==> c % A(inv(norm y pow 2) % y) = c % rfs_twist y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "deck") (LABEL_TAC "inv"))))) THEN
  SUBGOAL_THEN `linear (A:real^3->real^3) /\ (!v. norm(A v) = norm v)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. c % (A:real^3->real^3)(inv(norm y pow 2) % y) =
                           (c * inv(norm y pow 2)) % A y`
  (LABEL_TAC "Tform") THENL
   [GEN_TAC THEN FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. ~(y = vec 0) ==> ~(c % (A:real^3->real^3)(inv(norm y pow 2) % y) = vec 0)`
  (LABEL_TAC "Tnz") THENL
   [SUBGOAL_THEN `!v:real^3. (A:real^3->real^3) v = vec 0 <=> v = vec 0` ASSUME_TAC THENL
     [GEN_TAC THEN ONCE_REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN USE_THEN "Tform" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_ENTIRE; REAL_INV_EQ_0; REAL_POW_EQ_0;
                    NORM_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. ~(y = vec 0)
               ==> c % (A:real^3->real^3)(inv(norm(c % A(inv(norm y pow 2) % y)) pow 2) %
                         (c % A(inv(norm y pow 2) % y))) = A(A y)`
  (LABEL_TAC "TT") THENL
   [GEN_TAC THEN DISCH_TAC THEN USE_THEN "Tform" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
    SUBGOAL_THEN `~(norm(y:real^3) = &0)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
    UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  (* A is an involution *)
  SUBGOAL_THEN `!v:real^3. A(A v) = v` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN ASM_CASES_TAC `v:real^3 = vec 0` THENL
     [ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
    USE_THEN "TT" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `v:real^3` th)
      (ASSUME `~(v:real^3 = vec 0)`))]) THEN
    ABBREV_TAC `w = c % (A:real^3->real^3) (inv(norm v pow 2) % v)` THEN
    SUBGOAL_THEN `~(w:real^3 = vec 0)` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN USE_THEN "Tnz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(c % (A:real^3->real^3) (inv(norm w pow 2) % w) = vec 0)` ASSUME_TAC THENL
     [USE_THEN "Tnz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^3->A) v = e(c % (A:real^3->real^3) (inv(norm w pow 2) % w))`
    MP_TAC THENL
     [USE_THEN "deck" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `w:real^3` th)
        (ASSUME `~(w:real^3 = vec 0)`))]) THEN
      EXPAND_TAC "w" THEN
      USE_THEN "deck" (fun th -> REWRITE_TAC[GSYM(MP (SPEC `v:real^3` th)
        (ASSUME `~(v:real^3 = vec 0)`))]) THEN
      USE_THEN "inv" (fun th -> REWRITE_TAC[CONJUNCT1(MP (SPEC `v:real^3` th)
        (ASSUME `~(v:real^3 = vec 0)`))]);
      ALL_TAC] THEN
    USE_THEN "inj" (fun th -> REWRITE_TAC[MP (SPECL [`v:real^3`;
      `c % (A:real^3->real^3) (inv(norm w pow 2) % w)`] th)
      (CONJ (ASSUME `~(v:real^3 = vec 0)`)
            (ASSUME `~(c % (A:real^3->real^3) (inv(norm w pow 2) % w) = vec 0)`))]);
    ALL_TAC] THEN
  (* A has no fixed vector *)
  SUBGOAL_THEN `!v:real^3. A v = v ==> v = vec 0` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `v:real^3 = vec 0` THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `y = (sqrt c / norm v) % (v:real^3)` THEN
    SUBGOAL_THEN `&0 < sqrt c /\ &0 < norm(v:real^3)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT; NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `~(y:real^3 = vec 0) /\ (A:real^3->real^3) y = y /\ norm y pow 2 = c`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_DIV_EQ_0] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LT_IMP_NZ] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `c % (A:real^3->real^3) (inv(norm y pow 2) % y) = y` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID];
      ALL_TAC] THEN
    USE_THEN "inv" (MP_TAC o CONJUNCT2 o C MP (ASSUME `~(y:real^3 = vec 0)`) o SPEC `y:real^3`) THEN
    USE_THEN "deck" (fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th) (ASSUME `~(y:real^3 = vec 0)`)]) THEN
    REWRITE_TAC[ASSUME `c % (A:real^3->real^3) (inv(norm y pow 2) % y) = y`];
    ALL_TAC] THEN
  MP_TAC(ISPEC `A:real^3->real^3` P2BX1_INVOL_NOFIX) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[rfs_twist] THEN
  REWRITE_TAC[VECTOR_MUL_RNEG; VECTOR_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The 1-jet of the deck map at one point and the deck map of a one-to-one   *)
(* model (P2BX1_DECK_FORM): tau o e is e composed with c times the twist.    *)
(* ------------------------------------------------------------------------- *)

let P2BX1_DECK_JET = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (X:A->real^3) (e:real^3->A)
    (tau:A->A) lam mu s1 s2 y0 z0.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\ &0 < lam /\
     mu pow 2 = &2 * lam /\ ~(y0 = vec 0) /\ ~(z0 = vec 0) /\ tau(e y0) = e z0 /\
     y0 IN s1 /\ mfd_param top atlas s1 (tau o e) /\
     z0 IN s2 /\ mfd_param top atlas s2 e /\
     rfs_pullback atlas (tau o e) G y0 = lam %% cylinder_flow (&0) y0 /\
     rfs_pullback atlas e G z0 = lam %% cylinder_flow (&0) z0 /\
     p2bkg_pform atlas G X (tau o e) y0 = --((mu / norm y0 pow 2) % y0) /\
     p2bkg_pform atlas G X e z0 = (mu / norm z0 pow 2) % z0
     ==> (\z. SND(chart_at atlas (e z0)) (e z)) differentiable at z0 /\
         ?M. linear M /\ (!u. norm(M u) = (norm z0 / norm y0) * norm u) /\ M y0 = --z0 /\
             frechet_derivative (\z. SND(chart_at atlas (e z0)) (tau(e z))) (at y0) =
             frechet_derivative (\z. SND(chart_at atlas (e z0)) (e z)) (at z0) o M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s2:real^3->bool`;
                 `e:real^3->A`; `z0:real^3`] P2BX1_PARAM_CHART_INVERTIBLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `D2':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(e:real^3->A) z0 IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MFD_PARAM_MAPS
      (ASSUME `mfd_param top (atlas:((A->bool)#(A->real^3))->bool) s2 (e:real^3->A)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `IMAGE (e:real^3->A) s2 SUBSET topspace top` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `(e:real^3->A) z0`]
                CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `s1:real^3->bool`;
                 `(tau:A->A) o (e:real^3->A)`;
                 `chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) z0)`; `y0:real^3`]
                P2BX1_PARAM_CHART_DIFFERENTIABLE) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  ABBREV_TAC `D1 = frechet_derivative (\z. SND(chart_at (atlas:((A->bool)#(A->real^3))->bool)
                                                 ((e:real^3->A) z0)) ((tau:A->A) (e z))) (at y0)` THEN
  ABBREV_TAC `D2 = frechet_derivative (\z. SND(chart_at (atlas:((A->bool)#(A->real^3))->bool)
                                                 ((e:real^3->A) z0)) (e z)) (at z0)` THEN
  SUBGOAL_THEN `linear (D1:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "D1" THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(D2':real^3->real^3) o (D1:real^3->real^3)` THEN
  SUBGOAL_THEN `linear ((D2':real^3->real^3) o (D1:real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(D2:real^3->real^3) o ((D2':real^3->real^3) o (D1:real^3->real^3)) = D1`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ABBREV_TAC `M = (D2':real^3->real^3) o (D1:real^3->real^3)` THEN
  ASM_REWRITE_TAC[] THEN
  (* conformality from the metric *)
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                 `(tau:A->A) o (e:real^3->A)`; `e:real^3->A`; `y0:real^3`; `z0:real^3`;
                 `M:real^3->real^3`] P2BX1_RFS_PULLBACK_JET) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!u. norm((M:real^3->real^3) u) = norm(z0:real^3) / norm(y0:real^3) * norm u`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX1_CYL0_CONGRUENT THEN EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the 1-form *)
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`; `X:A->real^3`;
                 `(tau:A->A) o (e:real^3->A)`; `e:real^3->A`; `y0:real^3`; `z0:real^3`;
                 `M:real^3->real^3`] P2BX1_PFORM_JET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[RIEMANNIAN_METRIC_POS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(mu = &0) /\ &0 < norm(y0:real^3) /\ &0 < norm(z0:real^3)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT] THEN MATCH_MP_TAC P2BX1_MU_NZ THEN
    EXISTS_TAC `lam:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp(matrix(M:real^3->real^3)) ** (z0:real^3) =
                --((norm z0 / norm(y0:real^3)) pow 2 % y0)` ASSUME_TAC THENL
   [TRANS_TAC EQ_TRANS
     `--(((mu / norm(y0:real^3) pow 2) / (mu / norm(z0:real^3) pow 2)) % y0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC P2BX1_SCALE_SOLVE THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[REAL_DIV_EQ_0; REAL_POW_EQ_0; NORM_EQ_0; ARITH_EQ];
      AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(mu = &0)` THEN UNDISCH_TAC `&0 < norm(y0:real^3)` THEN
      UNDISCH_TAC `&0 < norm(z0:real^3)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC P2BX1_CONFORMAL_IMAGE THEN EXISTS_TAC `norm(z0:real^3) / norm(y0:real^3)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV]);;

(* The deck map of a one-to-one model is e o (c twist). *)

let P2BX1_DECK_FORM = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (G:A->real^3^3) (X:A->real^3) (e:real^3->A)
    (tau:A->A) lam mu.
     hausdorff_space top /\ smooth_manifold_atlas top atlas /\ riemannian_metric atlas G /\
     &0 < lam /\ mu pow 2 = &2 * lam /\
     IMAGE e {y | ~(y = vec 0)} = topspace top /\
     (!y. ~(y = vec 0)
          ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\ mfd_param top atlas s e) /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (e y = e z <=> z = y)) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas e G y = lam %% cylinder_flow (&0) y) /\
     (!y. ~(y = vec 0)
          ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\
                  mfd_param top atlas s (tau o e)) /\
     (!y. ~(y = vec 0) ==> rfs_pullback atlas (tau o e) G y = lam %% cylinder_flow (&0) y) /\
     (!y. ~(y = vec 0) ==> p2bkg_pform atlas G X e y = (mu / norm y pow 2) % y) /\
     (!y. ~(y = vec 0) ==> p2bkg_pform atlas G X (tau o e) y = --(p2bkg_pform atlas G X e y)) /\
     (!w. w IN topspace top ==> tau w IN topspace top /\ tau(tau w) = w /\ ~(tau w = w))
     ==> ?c. &0 < c /\ !y. ~(y = vec 0) ==> tau(e y) = e(c % rfs_twist y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    LABEL_TAC "im" (el 5 (CONJUNCTS th)) THEN
    LABEL_TAC "loc" (el 6 (CONJUNCTS th)) THEN LABEL_TAC "inj" (el 7 (CONJUNCTS th)) THEN
    LABEL_TAC "pb" (el 8 (CONJUNCTS th)) THEN LABEL_TAC "loct" (el 9 (CONJUNCTS th)) THEN
    LABEL_TAC "pbt" (el 10 (CONJUNCTS th)) THEN LABEL_TAC "om" (el 11 (CONJUNCTS th)) THEN
    LABEL_TAC "omt" (el 12 (CONJUNCTS th)) THEN LABEL_TAC "inv" (el 13 (CONJUNCTS th))) THEN
  ABBREV_TAC `y0:real^3 = basis 1` THEN
  SUBGOAL_THEN `~(y0:real^3 = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "y0" THEN SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. ~(y = vec 0) ==> (e:real^3->A) y IN topspace top` (LABEL_TAC "etop") THENL
   [USE_THEN "im" (fun th -> REWRITE_TAC[SYM th]) THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z0:real^3. ~(z0 = vec 0) /\ (tau:A->A)((e:real^3->A) y0) = e z0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(tau:A->A)((e:real^3->A) y0) IN topspace top` MP_TAC THENL
     [SUBGOAL_THEN `(e:real^3->A) y0 IN topspace top` ASSUME_TAC THENL
       [USE_THEN "etop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "inv" (fun th -> MP_TAC(SPEC `(e:real^3->A) y0` th)) THEN ASM_SIMP_TAC[];
      USE_THEN "im" (fun th -> REWRITE_TAC[SYM th]) THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_pullback atlas ((tau:A->A) o (e:real^3->A)) (G:A->real^3^3) y0 =
                lam %% cylinder_flow (&0) y0 /\
                rfs_pullback atlas e G z0 = lam %% cylinder_flow (&0) z0 /\
                p2bkg_pform atlas G (X:A->real^3) (tau o e) y0 = --((mu / norm y0 pow 2) % y0) /\
                p2bkg_pform atlas G X e z0 = (mu / norm z0 pow 2) % z0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "pbt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "pb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "omt" (fun th -> REWRITE_TAC[MP (SPEC `y0:real^3` th)
        (ASSUME `~(y0:real^3 = vec 0)`)]) THEN
      USE_THEN "om" (fun th -> REWRITE_TAC[MP (SPEC `y0:real^3` th)
        (ASSUME `~(y0:real^3 = vec 0)`)]);
      USE_THEN "om" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "loct" (MP_TAC o C MP (ASSUME `~(y0:real^3 = vec 0)`) o SPEC `y0:real^3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^3->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "loc" (MP_TAC o C MP (ASSUME `~(z0:real^3 = vec 0)`) o SPEC `z0:real^3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                 `X:A->real^3`; `e:real^3->A`; `tau:A->A`; `lam:real`; `mu:real`;
                 `s1:real^3->bool`; `s2:real^3->bool`; `y0:real^3`; `z0:real^3`]
                P2BX1_DECK_JET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `M:real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`M:real^3->real^3`; `y0:real^3`; `z0:real^3`] P2BX1_DECK_ISOM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^3->real^3` (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`A:real^3->real^3`; `c:real`; `lam:real`] P2BX1_INV_ORTHO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Tdiffeo") (CONJUNCTS_THEN2 (LABEL_TAC "Tisom")
    (LABEL_TAC "Tderiv"))) THEN
  ABBREV_TAC `Tm = \y:real^3. c % (A:real^3->real^3) (inv(norm y pow 2) % y)` THEN
  SUBGOAL_THEN `(Tm:real^3->real^3) y0 = z0` ASSUME_TAC THENL
   [EXPAND_TAC "Tm" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* e o Tm is a local isometric parametrization *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                 `e:real^3->A`; `Tm:real^3->real^3`;
                 `(\y:real^3. inv(norm y pow 2) % y) o
                  (\v. (inv c %% transp(matrix(A:real^3->real^3))) ** v)`;
                 `\z:real^3. lam %% cylinder_flow (&0) z`] P2BX1_PRECOMP_PARAMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "locT") (LABEL_TAC "pbT0")) THEN
  SUBGOAL_THEN `!y. ~(y = vec 0)
                    ==> rfs_pullback atlas ((e:real^3->A) o (Tm:real^3->real^3))
                                     (G:A->real^3^3) y =
                        lam %% cylinder_flow (&0) y` (LABEL_TAC "pbT") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "pbT0" (fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
      (ASSUME `~(y:real^3 = vec 0)`)]) THEN
    USE_THEN "Tisom" (fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
      (ASSUME `~(y:real^3 = vec 0)`)]);
    ALL_TAC] THEN
  (* its chart derivative at y0 *)
  SUBGOAL_THEN
   `frechet_derivative (\z. SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) z0))
                              (e((Tm:real^3->real^3) z))) (at y0) =
    frechet_derivative (\z. SND(chart_at atlas (e z0)) (e z)) (at z0) o (M:real^3->real^3)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    SUBGOAL_THEN
     `(\z. SND(chart_at (atlas:((A->bool)#(A->real^3))->bool) ((e:real^3->A) z0))
             (e((Tm:real^3->real^3) z))) =
      (\u. SND(chart_at atlas (e z0)) (e u)) o Tm` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(M:real^3->real^3) =
        (\h. c % (A:real^3->real^3) (inv(norm(y0:real^3) pow 2) % h -
                                     (&2 * (y0 dot h) / (norm y0 pow 2) pow 2) % y0))`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
      USE_THEN "Tderiv" (fun th -> ACCEPT_TAC(MP (SPEC `y0:real^3` th)
        (ASSUME `~(y0:real^3 = vec 0)`)));
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* rigidity *)
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `G:A->real^3^3`;
                 `\z:real^3. lam %% cylinder_flow (&0) z`; `(tau:A->A) o (e:real^3->A)`;
                 `(e:real^3->A) o (Tm:real^3->real^3)`; `y0:real^3`; `(e:real^3->A) z0`]
                P2BX1_MODEL_RIGID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC RFB_METRIC_FIELD_CMUL THEN ASM_REWRITE_TAC[LRG_CYL0_EQ; LRG_CYL_METRIC];
    ALL_TAC] THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN(LABEL_TAC "rig") THEN
  MP_TAC(ISPECL [`e:real^3->A`; `tau:A->A`; `A:real^3->real^3`; `c:real`] P2BX1_DECK_ALGEBRA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THENL
     [USE_THEN "rig" (fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
        (ASSUME `~(y:real^3 = vec 0)`)]) THEN
      EXPAND_TAC "Tm" THEN REWRITE_TAC[];
      USE_THEN "inv" (fun th -> MP_TAC(SPEC `(e:real^3->A) y` th)) THEN ANTS_TAC THENL
       [USE_THEN "etop" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    DISCH_TAC THEN EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "rig" (fun th -> REWRITE_TAC[MP (SPEC `y:real^3` th)
      (ASSUME `~(y:real^3 = vec 0)`)]) THEN
    EXPAND_TAC "Tm" THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The descent.  If the double cover has a one-to-one model pc with tau(pc   *)
(* y) = pc(c twist y), then p = f o pc o (sqrt c) is a two-to-one twisted    *)
(* model of the base (P2BX1_DESCENT).                                        *)
(* ------------------------------------------------------------------------- *)

(* The cylinder fields are invariant under dilations. *)

let P2BX1_CYL_DILATE = prove
 (`!k lam s (y:real^3).
     ~(k = &0) /\ ~(y = vec 0)
     ==> mpullback (\w. k % w) (\z. lam %% cylinder_flow s z) y = lam %% cylinder_flow s y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(norm(y:real^3) = &0)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[APX_MPULLBACK_DILATE] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; cylinder_flow; MATRIX_CMUL_COMPONENT;
           MATRIX_ADD_COMPONENT; MAT_COMPONENT; VECTOR_MUL_COMPONENT;
           NORM_MUL; REAL_POW_MUL; REAL_POW2_ABS] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  UNDISCH_TAC `~(norm(y:real^3) = &0)` THEN UNDISCH_TAC `~(k = &0)` THEN CONV_TAC REAL_FIELD);;

(* Ball parametrizations give local parametrizations avoiding the origin. *)

let P2BX1_BALL_LOCAL = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) (p:real^3->A).
     (!y. ~(y = vec 0) ==> ?r. &0 < r /\ r < norm y /\ mfd_param top atlas (ball(y,r)) p)
     ==> !y. ~(y = vec 0)
             ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\ mfd_param top atlas s p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `~(y:real^3 = vec 0)`) o SPEC `y:real^3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(y:real^3,r)` THEN ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
  ASM_CASES_TAC `z:real^3 = vec 0` THEN ASM_REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC);;

(* The deck map preserves local parametrizations and the pulled-back metric. *)

let P2BX1_TAU_PARAMS = prove
 (`!topc top (atlas:((B->bool)#(B->real^3))->bool) (f:A->B) (tau:A->A) (e:real^3->A).
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     homeomorphic_maps (topc,topc) (tau,tau) /\ (!w. w IN topspace topc ==> f(tau w) = f w) /\
     (!y. ~(y = vec 0)
          ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\
                  mfd_param topc (mfd_lift_atlas topc top f atlas) s e)
     ==> !y. ~(y = vec 0)
             ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\
                     mfd_param topc (mfd_lift_atlas topc top f atlas) s (tau o e)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))))) THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  USE_THEN "loc" (MP_TAC o C MP (ASSUME `~(y:real^3 = vec 0)`) o SPEC `y:real^3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B)
                                              (atlas:((B->bool)#(B->real^3))->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
  MAP_EVERY EXISTS_TAC [`topc:A topology`;
                        `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)`;
                        `topspace topc:A->bool`; `topspace topc:A->bool`; `tau:A->A`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC P2BX1_DECK_DIFFEO THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[OPEN_IN_SUBSET]]);;

let P2BX1_TAU_PULLBACK = prove
 (`!topc top (atlas:((B->bool)#(B->real^3))->bool) (f:A->B) (tau:A->A) (e:real^3->A)
    (g:B->real^3^3) s1 s2 y.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\
     (!w. f(tau w) = f w) /\
     mfd_param topc (mfd_lift_atlas topc top f atlas) s1 e /\ y IN s1 /\
     mfd_param topc (mfd_lift_atlas topc top f atlas) s2 (tau o e) /\ y IN s2
     ==> rfs_pullback (mfd_lift_atlas topc top f atlas) (tau o e)
           (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) y =
         rfs_pullback (mfd_lift_atlas topc top f atlas) e
           (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `f:A->B`; `g:B->real^3^3`; `s2:real^3->bool`; `(tau:A->A) o (e:real^3->A)`;
                 `y:real^3`] P2BX1_RFS_PULLBACK_LIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `f:A->B`; `g:B->real^3^3`; `s1:real^3->bool`; `e:real^3->A`;
                 `y:real^3`] P2BX1_RFS_PULLBACK_LIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[FUN_EQ_THM; o_THM]);;

(* Parametrizations of the base by f o pc o (k %). *)

let P2BX1_DESCENT_PARAM = prove
 (`!topc top (atlas:((B->bool)#(B->real^3))->bool) (f:A->B) (pc:real^3->A) k y.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\ &0 < k /\
     (!y. ~(y = vec 0)
          ==> ?r. &0 < r /\ r < norm y /\
                  mfd_param topc (mfd_lift_atlas topc top f atlas) (ball(y,r)) pc) /\
     ~(y = vec 0)
     ==> ?r. &0 < r /\ r < norm y /\
             mfd_param top atlas (ball(y,r)) ((f o pc) o (\x. k % x)) /\
             mfd_param top atlas (IMAGE (\x. k % x) (ball(y,r))) (f o pc) /\
             diffeomorphism_on (ball(y,r)) (IMAGE (\x. k % x) (ball(y,r)))
                               (\x. k % x) (\x. inv k % x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "loc") ASSUME_TAC)))) THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (f:A->B)
                                              (atlas:((B->bool)#(B->real^3))->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS]; ALL_TAC] THEN
  SUBGOAL_THEN `~(k % y:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o C MP (ASSUME `~(k % y:real^3 = vec 0)`) o SPEC `k % y:real^3`) THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
  DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(pc:real^3->A) (k % y) IN topspace topc` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (pc:real^3->A) (ball(k % y,r1)) SUBSET topspace topc` MP_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_SUBSET];
      MP_TAC(ISPECL [`k % y:real^3`; `r1:real`] CENTRE_IN_BALL) THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `f:A->B`; `(pc:real^3->A) (k % y)`]
                MFDL_LH_SHEET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `S:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `f:A->B`; `S:A->bool`] P2BX1_SHEET_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `sig:B->A`) THEN
  SUBGOAL_THEN `open {z | z IN ball(k % y,r1) /\ (pc:real^3->A) z IN S}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN
    EXISTS_TAC `ball(k % y:real^3,r1)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{z | z IN ball(k % y,r1) /\ (pc:real^3->A) z IN S} =
                    {z | z IN topspace (subtopology euclidean (ball(k % y,r1))) /\ pc z IN S}`
      SUBST1_TAC THENL [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN EXISTS_TAC `topc:A topology` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[GSYM OPEN_IN; OPEN_BALL]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k % y:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `mfd_param top atlas (ball(k % y:real^3,r2)) ((f:A->B) o (pc:real^3->A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_COMPOSE_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`topc:A topology`;
                          `mfd_lift_atlas topc top (f:A->B) (atlas:((B->bool)#(B->real^3))->bool)`;
                          `S:A->bool`; `IMAGE (f:A->B) S`; `sig:B->A`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(k % y:real^3,r1)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `r = min (r2 / k) (norm(y:real^3) / &2)` THEN
  SUBGOAL_THEN `&0 < r /\ r < norm(y:real^3) /\ k * r <= r2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < norm(y:real^3)` ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r2 / k` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < r /\ r <= r2 / k /\ r <= norm(y:real^3) / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `k * r2 / k` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `k * r2 / k = r2` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < k` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x:real^3. k % x) (ball(y,r)) SUBSET ball(k % y,r2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL; dist] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> abs k = k`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `k * r` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real`; `ball(y:real^3,r)`] MFP_SCALE_DIFFEO) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_TAC THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mfd_param top atlas (IMAGE (\x:real^3. k % x) (ball(y,r))) ((f:A->B) o (pc:real^3->A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `ball(k % y:real^3,r2)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (\x:real^3. k % x) (ball(y,r))`;
                        `IMAGE (\x:real^3. k % x) (ball(y,r))`; `\x:real^3. inv k % x`] THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

(* The pullback of the base metric by f o pc o (k %). *)

let P2BX1_DESCENT_PULLBACK = prove
 (`!topc top (atlas:((B->bool)#(B->real^3))->bool) (f:A->B) (g:B->real^3^3) (pc:real^3->A)
    k lam s y.
     smooth_manifold_atlas top atlas /\ local_homeomorphism_map (topc,top) f /\ &0 < k /\
     (!y. ~(y = vec 0)
          ==> ?r. &0 < r /\ r < norm y /\
                  mfd_param topc (mfd_lift_atlas topc top f atlas) (ball(y,r)) pc) /\
     (!y. ~(y = vec 0)
          ==> rfs_pullback (mfd_lift_atlas topc top f atlas) pc
                (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f g) y =
              lam %% cylinder_flow s y) /\
     ~(y = vec 0)
     ==> rfs_pullback atlas ((f o pc) o (\x. k % x)) g y = lam %% cylinder_flow s y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "loc")
    (CONJUNCTS_THEN2 (LABEL_TAC "pb") ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `f:A->B`; `pc:real^3->A`; `k:real`; `y:real^3`] P2BX1_DESCENT_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `IMAGE (\x:real^3. k % x) (ball(y,r))`; `(f:A->B) o (pc:real^3->A)`;
                 `ball(y:real^3,r)`; `\x:real^3. k % x`; `\x:real^3. inv k % x`; `y:real^3`]
                P2BX2_RFS_PULLBACK_PRECOMP) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN DISCH_THEN SUBST1_TAC THEN
  TRANS_TAC EQ_TRANS `mpullback (\x:real^3. k % x) (\z. lam %% cylinder_flow s z) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_MPULLBACK_PT THEN BETA_TAC THEN
    SUBGOAL_THEN `~(k % y:real^3 = vec 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `~(k % y:real^3 = vec 0)`) o SPEC `k % y:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `f:A->B`; `g:B->real^3^3`; `ball(k % y:real^3,r1)`; `pc:real^3->A`;
                   `k % y:real^3`] P2BX1_RFS_PULLBACK_LIFT) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "pb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2BX1_CYL_DILATE THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ]]);;

(* The fibres of f o pc o (sqrt c %). *)

let P2BX1_DESCENT_FIBRES = prove
 (`!topc (f:A->B) (pc:real^3->A) (tau:A->A) c y z.
     &0 < c /\
     IMAGE pc {y | ~(y = vec 0)} = topspace topc /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (pc y = pc z <=> z = y)) /\
     (!w1 w2. w1 IN topspace topc /\ w2 IN topspace topc
              ==> (f w1 = f w2 <=> w2 = w1 \/ w2 = tau w1)) /\
     (!y. ~(y = vec 0) ==> tau(pc y) = pc(c % rfs_twist y)) /\
     ~(y = vec 0) /\ ~(z = vec 0)
     ==> (((f o pc) o (\x. sqrt c % x)) y = ((f o pc) o (\x. sqrt c % x)) z <=>
          z = y \/ z = rfs_twist y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "im")
    (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "fib")
    (CONJUNCTS_THEN2 (LABEL_TAC "deck") STRIP_ASSUME_TAC))))) THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `&0 < sqrt c /\ sqrt c pow 2 = c` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. ~(v = vec 0) ==> ~(sqrt c % v = vec 0)` (LABEL_TAC "nz") THENL
   [ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^3. ~(v = vec 0) ==> (pc:real^3->A) v IN topspace topc` (LABEL_TAC "top") THENL
   [USE_THEN "im" (fun th -> REWRITE_TAC[SYM th]) THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(rfs_twist (y:real^3) = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[P2BX2_TWIST_NONZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `c % rfs_twist(sqrt c % y:real^3) = sqrt c % rfs_twist y` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_twist; NORM_MUL; VECTOR_MUL_RNEG; VECTOR_MUL_ASSOC; REAL_POW_MUL;
                REAL_POW2_ABS] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `~(norm(y:real^3) = &0)` MP_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_0]; ALL_TAC] THEN
    UNDISCH_TAC `sqrt c pow 2 = c` THEN UNDISCH_TAC `&0 < sqrt c` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  USE_THEN "fib" (fun th -> REWRITE_TAC[MP (SPECL [`(pc:real^3->A) (sqrt c % y)`;
    `(pc:real^3->A) (sqrt c % z)`] th)
    (CONJ (MP (SPEC `sqrt c % y:real^3` (ASSUME `!v:real^3. ~(v = vec 0) ==> (pc:real^3->A) v IN topspace topc`))
              (MP (SPEC `y:real^3` (ASSUME `!v:real^3. ~(v = vec 0) ==> ~(sqrt c % v = vec 0)`))
                  (ASSUME `~(y:real^3 = vec 0)`)))
          (MP (SPEC `sqrt c % z:real^3` (ASSUME `!v:real^3. ~(v = vec 0) ==> (pc:real^3->A) v IN topspace topc`))
              (MP (SPEC `z:real^3` (ASSUME `!v:real^3. ~(v = vec 0) ==> ~(sqrt c % v = vec 0)`))
                  (ASSUME `~(z:real^3 = vec 0)`))))]) THEN
  USE_THEN "deck" (fun th -> REWRITE_TAC[MP (SPEC `sqrt c % y:real^3` th)
    (MP (SPEC `y:real^3` (ASSUME `!v:real^3. ~(v = vec 0) ==> ~(sqrt c % v = vec 0)`))
        (ASSUME `~(y:real^3 = vec 0)`))]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(sqrt c % y:real^3 = vec 0) /\ ~(sqrt c % z:real^3 = vec 0) /\
                ~(sqrt c % rfs_twist y:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "nz" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "inj" (fun th -> REWRITE_TAC[MP (SPECL [`sqrt c % z:real^3`; `sqrt c % y:real^3`] th)
    (CONJ (ASSUME `~(sqrt c % z:real^3 = vec 0)`) (ASSUME `~(sqrt c % y:real^3 = vec 0)`))]) THEN
  USE_THEN "inj" (fun th -> REWRITE_TAC[MP (SPECL [`sqrt c % rfs_twist y:real^3`;
    `sqrt c % z:real^3`] th)
    (CONJ (ASSUME `~(sqrt c % rfs_twist y:real^3 = vec 0)`)
          (ASSUME `~(sqrt c % z:real^3 = vec 0)`))]) THEN
  ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ] THEN MESON_TAC[]);;

(* The descent: a twisted model of the base. *)

let P2BX1_DESCENT = prove
 (`!topc top (atlas:((B->bool)#(B->real^3))->bool) (f:A->B) (g:real->B->real^3^3) (tau:A->A)
    (pc:real^3->A) lam c.
     smooth_manifold_atlas top atlas /\ covering_map (topc,top) f /\ &0 < lam /\ &0 < c /\
     IMAGE pc {y | ~(y = vec 0)} = topspace topc /\
     (!y. ~(y = vec 0)
          ==> ?r. &0 < r /\ r < norm y /\
                  mfd_param topc (mfd_lift_atlas topc top f atlas) (ball(y,r)) pc) /\
     (!y z. ~(y = vec 0) /\ ~(z = vec 0) ==> (pc y = pc z <=> z = y)) /\
     (!t y. t <= &0 /\ ~(y = vec 0)
            ==> rfs_pullback (mfd_lift_atlas topc top f atlas) pc
                  (mfd_pullback_metric (mfd_lift_atlas topc top f atlas) atlas f (g t)) y =
                lam %% cylinder_flow (t / lam) y) /\
     (!w1 w2. w1 IN topspace topc /\ w2 IN topspace topc
              ==> (f w1 = f w2 <=> w2 = w1 \/ w2 = tau w1)) /\
     (!y. ~(y = vec 0) ==> tau(pc y) = pc(c % rfs_twist y))
     ==> p2b_cyl_model (top,atlas) g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    LABEL_TAC "loc" (el 5 (CONJUNCTS th)) THEN LABEL_TAC "pb" (el 7 (CONJUNCTS th))) THEN
  SUBGOAL_THEN `local_homeomorphism_map (topc,top) (f:A->B)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COVERING_MAP_LOCAL_HOMEOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt c` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[p2b_cyl_model] THEN
  MAP_EVERY EXISTS_TAC [`((f:A->B) o (pc:real^3->A)) o (\x:real^3. sqrt c % x)`; `lam:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* image *)
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (\x:real^3. sqrt c % x) {y | ~(y = vec 0)} = {y | ~(y = vec 0)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
      EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
        ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ];
        DISCH_TAC THEN EXISTS_TAC `inv(sqrt c) % z:real^3` THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                     VECTOR_MUL_EQ_0; REAL_INV_EQ_0]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[covering_map];
    (* local parametrizations *)
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`topc:A topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `f:A->B`; `pc:real^3->A`; `sqrt c`; `y:real^3`] P2BX1_DESCENT_PARAM) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    (* fibres *)
    DISJ2_TAC THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX1_DESCENT_FIBRES THEN
    MAP_EVERY EXISTS_TAC [`topc:A topology`; `tau:A->A`] THEN ASM_REWRITE_TAC[];
    (* pullback *)
    REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX1_DESCENT_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`topc:A topology`; `top:B topology`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN USE_THEN "pb" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The double-cover case.  The cover model is one-to-one (the twisted one    *)
(* carries no unit parallel field); the deck map is pc o (c twist)           *)
(* (P2BX1_DECK_FORM); the descent gives the twisted model of the base        *)
(* (P2BX1_DESCENT).                                                          *)
(* ------------------------------------------------------------------------- *)

let P2BX1_COVER_DESCENT = prove
 (`!top (atlas:((B->bool)#(B->real^3))->bool) (g:real->B->real^3^3) s0 (U:B->B->bool)
    (Xf:B->B->real^3) (j:B#bool->B) j' topc.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas (g s0) /\
     (!i. open_in top (U i)) /\ (!x. x IN topspace top ==> x IN U x) /\
     (!i. p2b_parallel_on atlas (g s0) (U i) (Xf i)) /\
     (!i y. y IN U i ==> Xf i y dot (g s0 y ** Xf i y) = &1) /\
     (!i j x. x IN U i /\ x IN U j ==> Xf i x = Xf j x \/ Xf i x = --(Xf j x)) /\
     smt_zcocycle top U (\i j x. Xf i x = Xf j x) (\x. x) /\ (!p. j'(j p) = p) /\
     (!W. open_in topc W <=>
          ?V. open_in (smt_zcover top U (\i j x. Xf i x = Xf j x) (\x. x)) V /\
              W = IMAGE j V) /\
     topspace topc =
     IMAGE j (topspace (smt_zcover top U (\i j x. Xf i x = Xf j x) (\x. x))) /\
     homeomorphic_maps (smt_zcover top U (\i j x. Xf i x = Xf j x) (\x. x),topc) (j,j') /\
     hausdorff_space topc /\ covering_map (topc,top) (FST o j') /\
     p2b_cyl_model (topc,mfd_lift_atlas topc top (FST o j') atlas)
       (\t. mfd_pullback_metric (mfd_lift_atlas topc top (FST o j') atlas) atlas
                                (FST o j') (g(t + s0)))
     ==> p2b_cyl_model (top,atlas) (\t. g(t + s0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC(GEN_REWRITE_RULE I [p2b_cyl_model] (last (CONJUNCTS th)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `pc:real^3->B` (X_CHOOSE_THEN `lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "im")
    (CONJUNCTS_THEN2 (LABEL_TAC "balls") (CONJUNCTS_THEN2 (LABEL_TAC "fib")
    (LABEL_TAC "pbt" o BETA_RULE))))))) THEN
  SUBGOAL_THEN `local_homeomorphism_map (topc,top) (FST o (j':B->B#bool))` ASSUME_TAC THENL
   [ASM_MESON_TAC[COVERING_MAP_LOCAL_HOMEOMORPHISM]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas topc (mfd_lift_atlas topc top (FST o (j':B->B#bool))
                                              (atlas:((B->bool)#(B->real^3))->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_ATLAS]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric (mfd_lift_atlas topc top (FST o (j':B->B#bool))
                                     (atlas:((B->bool)#(B->real^3))->bool))
                  (mfd_pullback_metric (mfd_lift_atlas topc top (FST o j') atlas) atlas
                                       (FST o j') ((g:real->B->real^3^3) s0))`
  ASSUME_TAC THENL [ASM_MESON_TAC[MFDL_RIEMANNIAN]; ALL_TAC] THEN
  (* the lifted tautological field *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`; `U:B->B->bool`; `Xf:B->B->real^3`;
                 `j:B#bool->B`; `j':B->B#bool`; `topc:B topology`] P2BX1_TAUT_FIELD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "par") (LABEL_TAC "unit")) THEN
  USE_THEN "balls" (fun th -> LABEL_TAC "loc" (MATCH_MP P2BX1_BALL_LOCAL th)) THEN
  SUBGOAL_THEN
   `!y. ~(y = vec 0)
        ==> rfs_pullback (mfd_lift_atlas topc top (FST o (j':B->B#bool))
                            (atlas:((B->bool)#(B->real^3))->bool)) (pc:real^3->B)
              (mfd_pullback_metric (mfd_lift_atlas topc top (FST o j') atlas) atlas
                                   (FST o j') ((g:real->B->real^3^3) s0)) y =
            lam %% cylinder_flow (&0) y` (LABEL_TAC "pb0") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "pbt" (fun th -> MP_TAC(MP (SPECL [`&0`; `y:real^3`] th)
      (CONJ (SPEC `&0` REAL_LE_REFL) (ASSUME `~(y:real^3 = vec 0)`)))) THEN
    REWRITE_TAC[REAL_ADD_LID; real_div; REAL_MUL_LZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:B topology`;
                 `mfd_lift_atlas topc top (FST o (j':B->B#bool))
                    (atlas:((B->bool)#(B->real^3))->bool)`;
                 `mfd_pullback_metric (mfd_lift_atlas topc top (FST o (j':B->B#bool))
                                         (atlas:((B->bool)#(B->real^3))->bool))
                                      atlas (FST o j') ((g:real->B->real^3^3) s0)`;
                 `mfd_lift_vec topc top (FST o (j':B->B#bool))
                    (atlas:((B->bool)#(B->real^3))->bool)
                    (\w. if SND(j' w) then (Xf:B->B->real^3) (FST(j' w)) (FST(j' w))
                         else --(Xf (FST(j' w)) (FST(j' w))))`;
                 `pc:real^3->B`; `lam:real`] P2BX1_MODEL_MU_CONST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "om"))) THEN
  USE_THEN "fib" (DISJ_CASES_THEN2 (LABEL_TAC "inj") (LABEL_TAC "tw")) THENL
   [ALL_TAC;
    (* the twisted cover is impossible *)
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MATCH_MP_TAC(INST_TYPE [`:B`,`:A`] P2BX1_TWIST_EXCLUDED) THEN
    MAP_EVERY EXISTS_TAC
     [`topc:B topology`;
      `mfd_lift_atlas topc top (FST o (j':B->B#bool)) (atlas:((B->bool)#(B->real^3))->bool)`;
      `mfd_pullback_metric (mfd_lift_atlas topc top (FST o (j':B->B#bool))
                              (atlas:((B->bool)#(B->real^3))->bool))
                           atlas (FST o j') ((g:real->B->real^3^3) s0)`;
      `mfd_lift_vec topc top (FST o (j':B->B#bool)) (atlas:((B->bool)#(B->real^3))->bool)
         (\w. if SND(j' w) then (Xf:B->B->real^3) (FST(j' w)) (FST(j' w))
              else --(Xf (FST(j' w)) (FST(j' w))))`;
      `pc:real^3->B`; `lam:real`; `mu:real`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(rfs_twist y = vec 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[P2BX2_TWIST_NONZERO]; ALL_TAC] THEN
    USE_THEN "tw" (fun th -> MP_TAC(MP (SPECL [`y:real^3`; `rfs_twist y`] th)
      (CONJ (ASSUME `~(y:real^3 = vec 0)`) (ASSUME `~(rfs_twist y = vec 0)`)))) THEN
    MESON_TAC[]] THEN
  (* the deck map *)
  SUBGOAL_THEN `?tau:B->B. !w. tau w = (j:B#bool->B) (FST((j':B->B#bool) w),~SND(j' w))`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\w:B. (j:B#bool->B) (FST((j':B->B#bool) w),~SND(j' w))` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `U:B->B->bool`; `\i j x. (Xf:B->B->real^3) i x = Xf j x`;
                 `j:B#bool->B`; `j':B->B#bool`; `topc:B topology`; `tau:B->B`] P2BX1_DECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dk")
    (CONJUNCTS_THEN2 (LABEL_TAC "dfib") (LABEL_TAC "dhom"))) THEN
  SUBGOAL_THEN `!w:B. (FST o (j':B->B#bool)) (tau w) = (FST o j') w` (LABEL_TAC "ftau") THENL
   [ASM_REWRITE_TAC[o_THM; FST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. ~(y = vec 0)
        ==> ?s. open s /\ y IN s /\ s SUBSET {y | ~(y = vec 0)} /\
                mfd_param topc (mfd_lift_atlas topc top (FST o (j':B->B#bool))
                                  (atlas:((B->bool)#(B->real^3))->bool))
                          s ((tau:B->B) o (pc:real^3->B))` (LABEL_TAC "loct") THENL
   [MATCH_MP_TAC P2BX1_TAU_PARAMS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. ~(y = vec 0)
        ==> rfs_pullback (mfd_lift_atlas topc top (FST o (j':B->B#bool))
                            (atlas:((B->bool)#(B->real^3))->bool)) ((tau:B->B) o (pc:real^3->B))
              (mfd_pullback_metric (mfd_lift_atlas topc top (FST o j') atlas) atlas
                                   (FST o j') ((g:real->B->real^3^3) s0)) y =
            lam %% cylinder_flow (&0) y` (LABEL_TAC "pbt0") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `~(y:real^3 = vec 0)`) o SPEC `y:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "loct" (MP_TAC o C MP (ASSUME `~(y:real^3 = vec 0)`) o SPEC `y:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`topc:B topology`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `FST o (j':B->B#bool)`; `tau:B->B`; `pc:real^3->B`;
                   `(g:real->B->real^3^3) s0`; `s1:real^3->bool`; `s2:real^3->bool`;
                   `y:real^3`] P2BX1_TAU_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "pb0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. ~(y = vec 0)
        ==> p2bkg_pform (mfd_lift_atlas topc top (FST o (j':B->B#bool))
                           (atlas:((B->bool)#(B->real^3))->bool))
              (mfd_pullback_metric (mfd_lift_atlas topc top (FST o j') atlas) atlas
                                   (FST o j') ((g:real->B->real^3^3) s0))
              (mfd_lift_vec topc top (FST o j') atlas
                 (\w. if SND(j' w) then (Xf:B->B->real^3) (FST(j' w)) (FST(j' w))
                      else --(Xf (FST(j' w)) (FST(j' w)))))
              ((tau:B->B) o (pc:real^3->B)) y =
            --(p2bkg_pform (mfd_lift_atlas topc top (FST o j') atlas)
                 (mfd_pullback_metric (mfd_lift_atlas topc top (FST o j') atlas) atlas
                                      (FST o j') (g s0))
                 (mfd_lift_vec topc top (FST o j') atlas
                    (\w. if SND(j' w) then Xf (FST(j' w)) (FST(j' w))
                         else --(Xf (FST(j' w)) (FST(j' w)))))
                 pc y)` (LABEL_TAC "omt") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `~(y:real^3 = vec 0)`) o SPEC `y:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC P2BX1_PFORM_DECK THEN EXISTS_TAC `s1:real^3->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    X_GEN_TAC `w:B` THEN DISCH_TAC THEN ASM_REWRITE_TAC[o_THM; FST; SND] THEN
    BOOL_CASES_TAC `SND((j':B->B#bool) w)` THEN REWRITE_TAC[VECTOR_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN topspace topc
                    ==> (tau:B->B) w IN topspace topc /\ tau(tau w) = w /\ ~(tau w = w)`
  (LABEL_TAC "dk3") THENL
   [X_GEN_TAC `w:B` THEN DISCH_TAC THEN
    USE_THEN "dk" (MP_TAC o C MP (ASSUME `(w:B) IN topspace topc`) o SPEC `w:B`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`topc:B topology`;
                 `mfd_lift_atlas topc top (FST o (j':B->B#bool))
                    (atlas:((B->bool)#(B->real^3))->bool)`;
                 `mfd_pullback_metric (mfd_lift_atlas topc top (FST o (j':B->B#bool))
                                         (atlas:((B->bool)#(B->real^3))->bool))
                                      atlas (FST o j') ((g:real->B->real^3^3) s0)`;
                 `mfd_lift_vec topc top (FST o (j':B->B#bool))
                    (atlas:((B->bool)#(B->real^3))->bool)
                    (\w. if SND(j' w) then (Xf:B->B->real^3) (FST(j' w)) (FST(j' w))
                         else --(Xf (FST(j' w)) (FST(j' w))))`;
                 `pc:real^3->B`; `tau:B->B`; `lam:real`; `mu:real`] P2BX1_DECK_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  (* the descent *)
  MP_TAC(BETA_RULE(ISPECL [`topc:B topology`; `top:B topology`;
                            `atlas:((B->bool)#(B->real^3))->bool`; `FST o (j':B->B#bool)`;
                            `\t. (g:real->B->real^3^3) (t + s0)`; `tau:B->B`;
                            `pc:real^3->B`; `lam:real`; `c:real`]
                           (INST_TYPE [`:B`,`:A`] P2BX1_DESCENT))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[o_THM] THEN FIRST_ASSUM ACCEPT_TAC;
    SIMP_TAC[]]);;

let P2BX1_COVER_CASE = prove
 (`!w:B->bool.
     P2B_SPLIT_ROUND_STATEMENT w
     ==> !kappa top atlas (g:real->B->real^3^3) b s0 (U:B->B->bool) (Xf:B->B->real^3).
           p2b_ancflow kappa (top,atlas) g b /\ s0 < b /\
           (!i. open_in top (U i)) /\ (!x. x IN topspace top ==> x IN U x) /\
           (!i. p2b_parallel_on atlas (g s0) (U i) (Xf i)) /\
           (!i y. y IN U i ==> Xf i y dot (g s0 y ** Xf i y) = &1) /\
           (!i j x. x IN U i /\ x IN U j ==> Xf i x = Xf j x \/ Xf i x = --(Xf j x)) /\
           (!i j. open_in top {x | x IN U i /\ x IN U j /\ Xf i x = Xf j x}) /\
           (!i j. open_in top {x | x IN U i /\ x IN U j /\ ~(Xf i x = Xf j x)}) /\
           ~(?eps. !i. open_in top {x | x IN U i /\ (eps x <=> Xf i x = Xf x x)} /\
                       open_in top {x | x IN U i /\ ~(eps x <=> Xf i x = Xf x x)})
           ==> p2b_cyl_model (top,atlas) (\t. g(t + s0))`,
  GEN_TAC THEN DISCH_THEN(LABEL_TAC "sr") THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`; `s0:real`; `U:B->B->bool`;
                       `Xf:B->B->real^3`] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN LABEL_TAC "noeps" (last (CONJUNCTS th))) THEN
  SUBGOAL_THEN `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2b_ancflow]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BX0_ANC_BASIC) THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) s0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `smt_zcocycle top (U:B->B->bool) (\i j x. (Xf:B->B->real^3) i x = Xf j x) (\x. x)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX1_ZCOCYCLE THEN EXISTS_TAC `(g:real->B->real^3^3) s0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_space (smt_zcover top (U:B->B->bool)
                                  (\i j x. (Xf:B->B->real^3) i x = Xf j x) (\x. x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC P2BX1_ZCOVER_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(topspace top:B->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN USE_THEN "noeps" MP_TAC THEN REWRITE_TAC[] THEN
    EXISTS_TAC `\x:B. T` THEN X_GEN_TAC `i:B` THEN
    SUBGOAL_THEN `(U:B->B->bool) i = {}`
      (fun th -> REWRITE_TAC[th; NOT_IN_EMPTY; EMPTY_GSPEC; OPEN_IN_EMPTY]) THEN
    ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`]
                P2BX1_MANIFOLD_INFINITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP P2BX1_PAIR_INJECTION) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:B#bool->B` (X_CHOOSE_TAC `j':B->B#bool`)) THEN
  MP_TAC(ISPECL [`top:B topology`; `U:B->B->bool`; `\i j x. (Xf:B->B->real^3) i x = Xf j x`;
                 `j:B#bool->B`; `j':B->B#bool`] P2BX1_TRANSPORT_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `topc:B topology` STRIP_ASSUME_TAC) THEN
  USE_THEN "sr" (MP_TAC o MATCH_MP P2BX1_COVER_MODEL) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
    `g:real->B->real^3^3`; `b:real`; `s0:real`; `U:B->B->bool`; `Xf:B->B->real^3`;
    `j:B#bool->B`; `j':B->B#bool`; `topc:B topology`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC P2BX1_COVER_DESCENT THEN
  MAP_EVERY EXISTS_TAC [`U:B->B->bool`; `Xf:B->B->real^3`; `j:B#bool->B`; `j':B->B#bool`;
                        `topc:B topology`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The route theorem P2B_SPLIT_CYL_ROUTE.                                    *)
(* ------------------------------------------------------------------------- *)

let P2B_SPLIT_CYL_ROUTE = prove
 (`!w:B->bool. P2B_SPLIT_CYL_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_SPLIT_CYL_ROUTE_STATEMENT; P2B_SPLIT_CYL_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "sr") THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                       `g:real->B->real^3^3`; `b:real`; `s0:real`; `x0:B`; `u:real^3`;
                       `v:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `p2b_ancflow0 kappa (top,atlas) (g:real->B->real^3^3) b` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2b_ancflow]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_manifold_atlas (top:B topology) (atlas:((B->bool)#(B->real^3))->bool) /\
                riemannian_metric atlas ((g:real->B->real^3^3) s0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `g:real->B->real^3^3`; `b:real`; `s0:real`] P2BX1_SHIFT_CLASS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `--(&1)` o CONJUNCT1 o CONJUNCT2) THEN
    REWRITE_TAC[REAL_ARITH `--(&1) < &0`; rfs_flow_upto; ricci_flow_on; REAL_ADD_LID] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kappa:real`; `top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `g:real->B->real^3^3`; `b:real`; `s0:real`; `x0:B`; `u:real^3`; `v:real^3`]
                P2BX1_LOCALLY_SPLIT_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `(g:real->B->real^3^3) s0`] P2BX1_SIGN_DATA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN MATCH_MP_TAC P2BX1_SCALAR_POS THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `top:B topology`; `b:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:B->B->bool` (X_CHOOSE_THEN `Xf:B->B->real^3` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `?eps. !i. open_in top {x | x IN (U:B->B->bool) i /\
                                           (eps x <=> (Xf:B->B->real^3) i x = Xf x x)} /\
                           open_in top {x | x IN U i /\ ~(eps x <=> Xf i x = Xf x x)}` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `eps:B->bool`) THEN
    USE_THEN "sr" (MP_TAC o MATCH_MP P2BX1_SECTION_CASE) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `b:real`; `U:B->B->bool`; `Xf:B->B->real^3`;
                          `eps:B->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "sr" (MP_TAC o MATCH_MP P2BX1_COVER_CASE) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`kappa:real`; `b:real`; `U:B->B->bool`; `Xf:B->B->real^3`] THEN
    ASM_REWRITE_TAC[]]);;

