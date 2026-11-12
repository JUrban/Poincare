(* ========================================================================= *)
(* pc_p2a_smz: leaf L9 P2A_SMALLZ via route O6 (MT Claims 8.6 and 8.7, Lemma *)
(* 6.60).  L-geodesics from x with 64 eps abs(Z)^2 <= 1 stay in B(x,tt,r/2)  *)
(* up to tau = eps r^2: along them the speed squared E in s = sqrt tau       *)
(* satisfies (MT (6.18))                                                     *)
(*    dE/ds = 4 s^2 dR(A) - 4 s Ric(A,A),                                   *)
(* so with abs(grad R) <= C1 / r^3 (L8) and abs(Ric) <= 2 / r^2 it grows     *)
(* only by a factor close to 1 (Gronwall), and the time-tt length of the    *)
(* curve is about r/4.  Then R >= -6 / r^2 along the curve gives            *)
(* l~ >= -2 eps.                                                             *)
(* The energy identity is P2AL_ENERGY_CURVE (pc_p2a_lric).                   *)
(*                                                                           *)
(* First: the chart-level Cauchy-Schwarz bound for dR.                       *)
(* ========================================================================= *)

needs "src/pc_p2a_lgeo3.ml";;
needs "src/pc_p2a_lconv.ml";;
needs "src/pc_p2a_bvp.ml";;
needs "src/pc_p2a_par.ml";;
needs "src/pc_p2a_lric.ml";;

prioritize_real();;
type_invention_error := true;;

(* dR(A)^2 <= abs(grad R)^2 abs(A)^2 (Cauchy-Schwarz for G with G^-1 dR).   *)

let P2AZ_DR_CS = prove
 (`!U (G:real^N->real^N^N) y (f:real^N->real) A.
     metric_field U G /\ y IN U /\ (\z. lift(f z)) differentiable (at y)
     ==> drop(frechet_derivative (\z. lift(f z)) (at y) A) pow 2 <=
         lgrad2 G f y * (A dot (G y ** A))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = (lambda k. drop(frechet_derivative (\z. lift((f:real^N->real) z)) (at y)
                                  (basis k))):real^N` THEN
  SUBGOAL_THEN `drop(frechet_derivative (\z. lift((f:real^N->real) z)) (at y) A) =
                (A:real^N) dot d` SUBST1_TAC THENL
   [EXPAND_TAC "d" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2A_DOT_LAMBDA_LINEAR THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `transp((G:real^N->real^N^N) y) = G y` ASSUME_TAC THENL
   [ASM_MESON_TAC[metric_field]; ALL_TAC] THEN
  SUBGOAL_THEN `invertible((G:real^N->real^N^N) y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LRG_METRIC_INVERTIBLE]; ALL_TAC] THEN
  SUBGOAL_THEN `lgrad2 (G:real^N->real^N^N) f y = d dot (matrix_inv(G y) ** d)`
  SUBST1_TAC THENL
   [REWRITE_TAC[lgrad2; dot; matrix_vector_mul] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN EXPAND_TAC "d" THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q = matrix_inv((G:real^N->real^N^N) y) ** d` THEN
  SUBGOAL_THEN `(G:real^N->real^N^N) y ** q = d` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC; MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^N) dot q = q dot ((G:real^N->real^N^N) y ** q)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[DOT_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^N) dot d = A dot ((G:real^N->real^N^N) y ** q)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `G:real^N->real^N^N`; `y:real^N`; `A:real^N`; `q:real^N`]
                LRG_METRIC_CS) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The region family read in a region chart (U INTER W,phi) of the atlas at  *)
(* b is, near phi z, the pullback of the slice metric at t by chart_inv      *)
(* (U,phi), for every t in (a,b]; so its scalar curvature and the squared    *)
(* norm of grad R are those of the slice (p2a_vgradR2).                      *)
(* ------------------------------------------------------------------------- *)

(* In a chart, the pullback by its inverse is the chart representative.    *)

let P2AZ_CHART_PULLBACK = prove
 (`!top atlas (U:A->bool) (phi:A->real^N) (g:A->real^N^N) z.
     smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ z IN U
     ==> rfs_pullback atlas (chart_inv (U,phi)) g (phi z) =
         metric_local atlas (U,phi) g (phi z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`] CHART_INV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:A` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:A) IN topspace top` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `(U:A->bool,phi:A->real^N)`] MFDM_CHART) THEN
    ASM_REWRITE_TAC[FST] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT1) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`; `z:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `chart_at (atlas:((A->bool)#(A->real^N))->bool) (z:A)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `psi:A->real^N`] THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  REWRITE_TAC[FST] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_pullback] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `U:A->bool`; `phi:A->real^N`; `V:A->bool`; `psi:A->real^N`;
                 `g:A->real^N^N`; `z:A`] METRIC_LOCAL_TRANS) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[chart_trans; o_DEF; SND]);;

(* The gradient norm of the scalar curvature of a pullback by a             *)
(* parametrisation (the pattern of APX_PULLBACK_SCALAR_GEN).                 *)

let P2AZ_PULLBACK_GRADR_GEN = prove
 (`!top atlas (g:A->real^N^N) s (e:real^N->A) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     mfd_param top atlas s e /\ y IN s
     ==> lgrad2 (rfs_pullback atlas e g) (lscalar (rfs_pullback atlas e g)) y =
         lgrad2 (metric_local atlas (chart_at atlas (e y)) g)
                (lscalar (metric_local atlas (chart_at atlas (e y)) g))
                (SND(chart_at atlas (e y)) (e y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `s:real^N->bool`; `e:real^N->A`; `y:real^N`]
                APX_PARAM_LOCAL_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^N->bool` (X_CHOOSE_THEN `N':real^N->bool`
    (X_CHOOSE_THEN `h':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `G' = metric_local atlas (chart_at atlas ((e:real^N->A) y)) (g:A->real^N^N)` THEN
  ABBREV_TAC `h = SND(chart_at (atlas:((A->bool)#(A->real^N))->bool) ((e:real^N->A) y)) o e` THEN
  SUBGOAL_THEN `(h:real^N->real^N) y = SND(chart_at atlas ((e:real^N->A) y)) (e y)`
  (SUBST1_TAC o SYM) THENL [EXPAND_TAC "h" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `lgrad2 (mpullback (h:real^N->real^N) G') (lscalar G' o h) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `N:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[o_THM] THEN
    TRANS_TAC EQ_TRANS `lscalar (mpullback (h:real^N->real^N) G') z` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `N:real^N->bool` THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC LSCALAR_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`N':real^N->bool`; `N:real^N->bool`; `h':real^N->real^N`] THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC LGRAD2_PULLBACK THEN
    MAP_EVERY EXISTS_TAC [`N':real^N->bool`; `N:real^N->bool`; `h':real^N->real^N`] THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH]]);;

(* The chart inverse of a chart of the atlas at b, on its part in W, is a    *)
(* parametrisation of the slice t, for every t in (a,b].                      *)

let P2AZ_VFAM_PARAM_LE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b t U (phi:A->real^3).
     p2a_region V W a b /\ a < t /\ t <= b /\
     smooth_manifold_atlas (rfs_vtop V t) (rfs_vatlas V t) /\
     smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas V b) /\
     open_in (rfs_vtop V b) W /\ (U,phi) IN rfs_vatlas V b
     ==> mfd_param (rfs_vtop V t) (rfs_vatlas V t) (IMAGE phi (U INTER W))
                   (chart_inv (U,phi))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC MFD_PARAM_RESTRICT THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MFD_PARAM_CHART_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`;
        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) b`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    MATCH_MP_TAC P2AP_VFAM_PARAM THEN MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The local representative of the region family at t near phi z.           *)

let P2AZ_RLOCAL_PULLBACK = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b t U (phi:A->real^3) z.
     p2a_svs V /\ p2a_region V W a b /\ a < t /\ t <= b /\
     (U,phi) IN rfs_vatlas V b /\ z IN U INTER W
     ==> p2a_rlocal V W b (U INTER W,phi) t (phi z) =
         rfs_pullback (rfs_vatlas V t) (chart_inv (U,phi)) (rfs_vmetric V t) (phi z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_rlocal; P2AP_RMETRIC_VFAM; P2A_VIEW_PROJ_3] THEN
  ASM_CASES_TAC `t:real = b` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                             (real->A->real^3^3)) W b b =
                  restrict_metric (rfs_vatlas V b) W (rfs_vmetric V b)`
    SUBST1_TAC THENL [REWRITE_TAC[p2c_vfam; ETA_AX]; ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_manifold_atlas (rfs_vtop V b) (rfs_vatlas (V:(real->A topology)#
        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) b) /\
      open_in (rfs_vtop V b) W`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`]
                    P2AP_REGION_PERSISTS) THEN
      ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
      DISCH_THEN(MP_TAC o SPEC `b:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) b`;
                   `U:A->bool`; `phi:A->real^3`; `W:A->bool`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) b`; `z:A`] METRIC_LOCAL_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2AZ_CHART_PULLBACK THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) b` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC P2AP_VFAM_PULLBACK_LOCAL THEN EXISTS_TAC `a:real` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* Scalar curvature and abs(grad R)^2 of the region family in a region      *)
(* chart are those of the slice.                                              *)

let P2AZ_RLOCAL_SLICE_FACTS = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    W a b t U (phi:A->real^3) z.
     p2a_svs V /\ p2a_region V W a b /\ a < t /\ t <= b /\
     (U,phi) IN rfs_vatlas V b /\ z IN U INTER W
     ==> lscalar (p2a_rlocal V W b (U INTER W,phi) t) (phi z) =
         mfd_scalar (rfs_vatlas V t) (rfs_vmetric V t) z /\
         lgrad2 (p2a_rlocal V W b (U INTER W,phi) t)
                (lscalar (p2a_rlocal V W b (U INTER W,phi) t)) (phi z) =
         p2a_vgradR2 V t z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `rfs_persists (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W a b` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AP_REGION_PERSISTS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] o
              check (fun th -> can (find_term (fun t -> is_const t &&
                fst(dest_const t) = "rfs_persists")) (concl th))) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `t:real` th) THEN MP_TAC(SPEC `b:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(z:A) IN topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t)`
  ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET; IN_INTER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `t:real`; `z:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `b:real`; `t:real`;
                 `U:A->bool`; `phi:A->real^3`] P2AZ_VFAM_PARAM_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^3) (U INTER W)) /\
                (phi:A->real^3) z IN IMAGE phi (U INTER W)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) b`;
        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) b`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN IMAGE (phi:A->real^3) (U INTER W)
        ==> p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                          (real->A->real^3^3)) W b (U INTER W,phi) t w =
            rfs_pullback (rfs_vatlas V t) (chart_inv (U,phi)) (rfs_vmetric V t) w`
  (LABEL_TAC "LOC") THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC P2AZ_RLOCAL_PULLBACK THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) b`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) b`; `U:A->bool`; `phi:A->real^3`;
                 `W:A->bool`; `z:A`] MFDR_CHART_INV_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS
     `lscalar (rfs_pullback (rfs_vatlas V t) (chart_inv (U:A->bool,phi:A->real^3))
                (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t)) ((phi:A->real^3) z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LSCALAR_LOCAL THEN EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t`;
                     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) t`;
                     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) t`;
                     `IMAGE (phi:A->real^3) (U INTER W)`; `chart_inv (U:A->bool,phi:A->real^3)`;
                     `(phi:A->real^3) z`] APX_PULLBACK_SCALAR_GEN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC];
    TRANS_TAC EQ_TRANS
     `lgrad2 (rfs_pullback (rfs_vatlas V t) (chart_inv (U:A->bool,phi:A->real^3))
                (rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) t))
             (lscalar (rfs_pullback (rfs_vatlas V t) (chart_inv (U,phi)) (rfs_vmetric V t)))
             ((phi:A->real^3) z)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LGRAD2_LOCAL THEN EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC LSCALAR_LOCAL THEN
      EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) t`;
                     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) t`;
                     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) t`;
                     `IMAGE (phi:A->real^3) (U INTER W)`; `chart_inv (U:A->bool,phi:A->real^3)`;
                     `(phi:A->real^3) z`] P2AZ_PULLBACK_GRADR_GEN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[p2a_vgradR2; P2A_VIEW_PROJ_3]]]);;

(* ------------------------------------------------------------------------- *)
(* The energy E(s) = 2 lsint(s) - 4 s^2 R (the speed squared of the          *)
(* L-geodesic in s at time tt - s^2), and the L-geodesic read in a region    *)
(* chart of a region over (a,tt] near an interior s0: it solves (6.5) there  *)
(* (P2A_LGEOD_PIECE, P2A_TRANS_ODE), and E is the chart energy.              *)
(* ------------------------------------------------------------------------- *)

let p2az_energy = new_definition
 `p2az_energy (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                 (real->A->real^N^N)) (tt:real) (gamma:real->A) (b:real) (s:real) =
    &2 * p2a_lsint V tt gamma b s -
    &4 * s pow 2 * mfd_scalar (p2a_vatlas V (tt - s pow 2)) (p2a_vmetric V (tt - s pow 2))
                              (gamma(s pow 2))`;;

(* Within an interval containing a neighbourhood the derivative is two-sided. *)

let P2AZ_HVD_WITHIN_AT = prove
 (`!(f:real^1->real^N) f' J s0 e t.
     &0 < e /\ abs(t - s0) < e /\ (!u. abs(drop u - s0) < e ==> u IN J) /\
     (f has_vector_derivative f') (at (lift t) within J)
     ==> (f has_vector_derivative f') (at (lift t))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `f':real^N`; `lift t`; `J:real^1->bool`;
                 `(:real^1)`; `e - abs(t - s0)`] P2A_HVD_WITHIN_LOCAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIV] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `dist(y:real^1,lift t) < e - abs(t - s0)` THEN
      REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN REAL_ARITH_TAC];
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]);;

(* The L-geodesic solves (6.5) in any region chart of a region over (a,tt]  *)
(* near an interior parameter s0.                                             *)

let P2AZ_CHART_SOL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b W a U (phi:A->real^N) s0.
     p2a_Lgeod V tt gamma b /\ &0 < s0 /\ s0 pow 2 < b /\
     p2a_region V W a tt /\ (U,phi) IN p2a_vatlas V tt /\ a < tt - s0 pow 2 /\
     gamma(s0 pow 2) IN U INTER W
     ==> ?e A1. &0 < e /\ e < s0 /\ (s0 + e) pow 2 < b /\
                (!s. abs(s - s0) < e
                     ==> a < tt - s pow 2 /\ tt - s pow 2 < tt /\ gamma(s pow 2) IN U INTER W /\
                         ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A1(lift s))
                           (at (lift s)) /\
                         (A1 has_vector_derivative
                            p2a_lacc (p2a_rlocal V W tt (U INTER W,phi)) tt s
                                     (phi(gamma(s pow 2))) (A1(lift s))) (at (lift s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s0 pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`]
                P2A_LGEOD_PIECE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W2:A->bool`; `a2:real`; `b2:real`; `U2:A->bool`; `phi2:A->real^N`;
                       `d:real`; `A2:real^1->real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "TW2") (CONJUNCTS_THEN2 (LABEL_TAC "IN2")
    (CONJUNCTS_THEN2 (LABEL_TAC "D2") (K ALL_TAC)))))))) THEN
  SUBGOAL_THEN `a2 < tt - s0 pow 2 /\ tt - s0 pow 2 <= b2` STRIP_ASSUME_TAC THENL
   [USE_THEN "TW2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s0 pow 2) IN U2 INTER W2` ASSUME_TAC THENL
   [USE_THEN "IN2" MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the slices and the chart domains *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `b2:real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `open_in (p2a_vtop V tt) (U:A->bool) /\
    open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) b2) (U2:A->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) tt`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt`;
                     `(U:A->bool,phi:A->real^N)`] MFDM_CHART);
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b2`;
                     `(U2:A->bool,phi2:A->real^N)`] MFDM_CHART)] THEN
    ASM_SIMP_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) (tt - s0 pow 2))
            ((U INTER W) INTER (U2 INTER W2):A->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_OPEN_BACK THENL
     [MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`; `tt:real`];
      MAP_EVERY EXISTS_TAC [`W2:A->bool`; `a2:real`; `b2:real`]] THEN
    ASM_SIMP_TAC[INTER_SUBSET; OPEN_IN_INTER] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`;
                 `(U INTER W) INTER (U2 INTER W2):A->bool`] P2A_LGEOD_CONT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C1"))) THEN
  MP_TAC(SPECL [`a:real`; `tt:real`; `tt:real`; `s0:real`] P2A_TIME_WINDOW) THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TW1")))] THEN
  SUBGOAL_THEN `s0 < sqrt b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `e = min (min e1 e2) (min d (min (s0 / &2) ((sqrt b - s0) / &2)))` THEN
  SUBGOAL_THEN `&0 < e /\ e <= e1 /\ e <= e2 /\ e <= d /\ e < s0 /\ s0 + e < sqrt b`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s0 + e) pow 2 < b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `sqrt b pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. abs(s - s0) < e ==> &0 < s /\ &0 <= s /\ s pow 2 <= b /\ s pow 2 < b`
  (LABEL_TAC "SR") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `s pow 2 <= (s0 + e) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `J = {u:real^1 | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < e}` THEN
  SUBGOAL_THEN `!u:real^1. u IN J <=> abs(drop u - s0) < e` (LABEL_TAC "J") THENL
   [GEN_TAC THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EQ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    USE_THEN "SR" (MP_TAC o SPEC `drop(u:real^1)`) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `is_interval(J:real^1->bool) /\
                J SUBSET {v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} /\
                tt - s0 pow 2 <= tt` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "J" THEN REWRITE_TAC[P2A_SWIN_INTERVAL];
      EXPAND_TAC "J" THEN SET_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN J
        ==> s0 - e < drop u /\ drop u < s0 + e /\
            (gamma:real->A)(drop u pow 2) IN (U2 INTER W2) INTER (U INTER W) /\
            a < tt - drop u pow 2 /\ tt - drop u pow 2 <= tt /\
            a2 < tt - drop u pow 2 /\ tt - drop u pow 2 <= b2 /\
            ((\v. (phi2:A->real^N)(gamma(drop v pow 2))) has_vector_derivative
             (A2:real^1->real^N) u)
              (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
            (A2 has_vector_derivative
               p2a_lacc (p2a_rlocal V W2 b2 (U2 INTER W2,phi2)) tt (drop u)
                        (phi2(gamma(drop u pow 2))) (A2 u))
              (at u within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^1` THEN USE_THEN "J" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
    USE_THEN "SR" (MP_TAC o SPEC `drop(u:real^1)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      USE_THEN "C1" (MP_TAC o SPEC `drop(u:real^1)`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SET_TAC[]];
      USE_THEN "TW1" (MP_TAC o SPEC `drop(u:real^1)`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "TW1" (MP_TAC o SPEC `drop(u:real^1)`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "TW2" (MP_TAC o SPEC `drop(u:real^1)`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "TW2" (MP_TAC o SPEC `drop(u:real^1)`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "D2" (MP_TAC o SPEC `u:real^1`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "D2" (MP_TAC o SPEC `u:real^1`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`;
                 `U:A->bool`; `phi:A->real^N`; `W2:A->bool`; `a2:real`; `b2:real`;
                 `U2:A->bool`; `phi2:A->real^N`; `tt - s0 pow 2`; `tt:real`; `gamma:real->A`;
                 `b:real`; `A2:real^1->real^N`; `J:real^1->bool`; `s0 - e`; `s0 + e`]
                P2A_TRANS_ODE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[P2A_LSOL_ODE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "SOL")) (K ALL_TAC)) THEN
  (* the transformed position is the chart curve *)
  SUBGOAL_THEN
   `!u. u IN J
        ==> chart_trans (U2 INTER W2,phi2) (U INTER W,phi:A->real^N)
              (phi2((gamma:real->A)(drop u pow 2))) = phi(gamma(drop u pow 2))`
  (LABEL_TAC "TR") THENL
   [X_GEN_TAC `u:real^1` THEN USE_THEN "J" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC THEN
    REWRITE_TAC[chart_trans; SND] THEN AP_TERM_TAC THEN
    USE_THEN "SR" (MP_TAC o SPEC `drop(u:real^1)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b2`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`; `U2:A->bool`; `phi2:A->real^N`;
                   `W2:A->bool`; `(gamma:real->A)(drop u pow 2)`] MFDR_CHART_INV_RESTRICT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "IN2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC `\u:real^1. frechet_derivative (chart_trans (U2 INTER W2,phi2) (U INTER W,phi:A->real^N))
                           (at (phi2((gamma:real->A)(drop u pow 2)))) ((A2:real^1->real^N) u)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
  USE_THEN "SR" (MP_TAC o SPEC `s:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `lift s IN J` ASSUME_TAC THENL
   [USE_THEN "J" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
  USE_THEN "SOL" (MP_TAC o SPEC `lift s`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LIFT_DROP]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  USE_THEN "TR" (MP_TAC o SPEC `lift s`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LIFT_DROP]] THEN
  DISCH_THEN(LABEL_TAC "TRs") THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "TW1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    SUBGOAL_THEN `&0 < s pow 2` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    USE_THEN "C1" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SET_TAC[]];
    MATCH_MP_TAC P2AZ_HVD_WITHIN_AT THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `s0:real`; `e:real`] THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    EXISTS_TAC `\u:real^1. chart_trans (U2 INTER W2,phi2) (U INTER W,phi:A->real^N)
                             (phi2((gamma:real->A)(drop u pow 2)))` THEN
    EXISTS_TAC `e - abs(s - s0)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "TR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2AZ_HVD_WITHIN_AT THEN
    MAP_EVERY EXISTS_TAC [`J:real^1->bool`; `s0:real`; `e:real`] THEN
    ASM_REWRITE_TAC[] THEN BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    UNDISCH_TAC
     `((\u:real^1. frechet_derivative (chart_trans (U2 INTER W2,phi2) (U INTER W,phi:A->real^N))
                     (at (phi2((gamma:real->A)(drop u pow 2)))) ((A2:real^1->real^N) u))
       has_vector_derivative
       p2a_lacc (p2a_rlocal V W tt (U INTER W,phi)) tt s
         (chart_trans (U2 INTER W2,phi2) (U INTER W,phi) (phi2(gamma(s pow 2))))
         (frechet_derivative (chart_trans (U2 INTER W2,phi2) (U INTER W,phi))
            (at (phi2(gamma(s pow 2)))) (A2(lift s))))
      (at (lift s) within J)` THEN
    USE_THEN "TRs" (fun th -> REWRITE_TAC[th])]);;

(* ------------------------------------------------------------------------- *)
(* Abs R <= 6 abs Rm in dimension 3 (orthonormal frame,                      *)
(* P2B_LSCALAR_FRAME), the energy E as a chart energy near an interior s0,  *)
(* its derivative (P2AL_ENERGY_CURVE), and the bound                         *)
(*    E'(s0) <= 4 s0^2 D sqrt E + 8 s0 K E                                   *)
(* when abs Rm <= K and abs(grad R) <= D at (gamma(s0^2), tt - s0^2), read  *)
(* in the preferred chart of the region manifold at gamma(s0^2).            *)
(* ------------------------------------------------------------------------- *)

let P2AZ_MFD_SCALAR_ABS = prove
 (`!top atlas (g:A->real^3^3) y.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\ y IN topspace top
     ==> abs(mfd_scalar atlas g y) <= &6 * mfd_rm_norm atlas g y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `y:A`] CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                 `y:A`] METRIC_LOCAL_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = chart_at (atlas:((A->bool)#(A->real^3))->bool) (y:A)` THEN
  ABBREV_TAC `G = metric_local atlas (c:(A->bool)#(A->real^3)) (g:A->real^3^3)` THEN
  SUBGOAL_THEN `metric_field (IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c))
                             (G:real^3->real^3^3)` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN UNDISCH_TAC `riemannian_metric atlas (g:A->real^3^3)` THEN
    REWRITE_TAC[riemannian_metric] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `SND(c:(A->bool)#(A->real^3)) y IN IMAGE (SND c) (FST c)` ASSUME_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)`; `G:real^3->real^3^3`;
                 `SND(c:(A->bool)#(A->real^3)) y`] LRG_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:real^3^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `mfd_scalar atlas (g:A->real^3^3) y =
    sum(1..dimindex(:3))
       (\j. mfd_ricci atlas g y (matrix_inv(M:real^3^3) ** basis j) (matrix_inv M ** basis j))`
  SUBST1_TAC THENL
   [REWRITE_TAC[mfd_scalar; mfd_ricci] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC P2B_LSCALAR_FRAME THEN
    EXISTS_TAC `IMAGE (SND(c:(A->bool)#(A->real^3))) (FST c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:3)) (\j. &2 * mfd_rm_norm atlas (g:A->real^3^3) y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`; `g:A->real^3^3`;
                   `y:A`; `matrix_inv(M:real^3^3) ** basis j`] P2AP_MFD_RICCI_ABS) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`transp(M:real^3^3) ** M`; `M:real^3^3`; `j:num`; `j:num`]
                  P2B_FRAME_ORTHO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[SUM_CONST_NUMSEG; DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REAL_ARITH_TAC]);;

(* E is the chart energy near s0, with the derivative of P2AL_ENERGY_CURVE. *)

let P2AZ_ENERGY_LOCAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt gamma b W a U (phi:A->real^3) s0.
     p2a_svs V /\ p2a_Lgeod V tt gamma b /\ &0 < s0 /\ s0 pow 2 < b /\
     p2a_region V W a tt /\ (U,phi) IN rfs_vatlas V tt /\ a < tt - s0 pow 2 /\
     gamma(s0 pow 2) IN U INTER W
     ==> ?A0. ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A0) (at (lift s0)) /\
              (p2az_energy V tt gamma b has_real_derivative
               (&4 * s0 pow 2 *
                drop(frechet_derivative
                       (\z. lift(lscalar (p2a_rlocal V W tt (U INTER W,phi) (tt - s0 pow 2)) z))
                       (at (phi(gamma(s0 pow 2)))) A0) -
                &4 * s0 * lricci (p2a_rlocal V W tt (U INTER W,phi) (tt - s0 pow 2))
                                 (phi(gamma(s0 pow 2))) A0 A0)) (atreal s0) /\
              p2az_energy V tt gamma b s0 =
              A0 dot (p2a_rlocal V W tt (U INTER W,phi) (tt - s0 pow 2) (phi(gamma(s0 pow 2))) **
                      A0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `b:real`; `W:A->bool`;
                 `a:real`; `U:A->bool`; `phi:A->real^3`; `s0:real`] P2AZ_CHART_SOL) THEN
  ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `A1:real^1->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "L")))))) THEN
  SUBGOAL_THEN
   `!s. abs(s - s0) < e
        ==> p2az_energy V tt (gamma:real->A) b s =
            (A1:real^1->real^3)(lift s) dot
            (p2a_rlocal V W tt (U INTER W,phi:A->real^3) (tt - s pow 2) (phi(gamma(s pow 2))) **
             A1(lift s))`
  (LABEL_TAC "EQ") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "L" (MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `&0 <= s /\ s pow 2 <= b` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `s pow 2 <= (s0 + e) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `b:real`; `s:real`;
                   `W:A->bool`; `a:real`; `tt:real`; `U:A->bool`; `phi:A->real^3`;
                   `(A1:real^1->real^3)(lift s)`] P2A_LSINT_CHART) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `tt - s pow 2`;
                   `U:A->bool`; `phi:A->real^3`; `(gamma:real->A)(s pow 2)`]
                  P2AZ_RLOCAL_SLICE_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[p2az_energy; p2a_llag; P2A_VIEW_PROJ_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "L" (MP_TAC o SPEC `s0:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `U:A->bool`;
                 `phi:A->real^3`] P2A_REGION_LRICCI) THEN
  ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) (U INTER W)`; `a:real`; `tt:real`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W tt (U INTER W,phi:A->real^3)`;
                 `tt:real`; `s0:real`; `\v:real^1. (phi:A->real^3)((gamma:real->A)(drop v pow 2))`;
                 `A1:real^1->real^3`] P2AL_ENERGY_CURVE) THEN
  BETA_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  EXISTS_TAC `(A1:real^1->real^3)(lift s0)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_DERIVATIVE_TRANSFORM_ATREAL THEN
    EXISTS_TAC
     `\s'. (A1:real^1->real^3)(lift s') dot
           (p2a_rlocal V W tt (U INTER W,phi:A->real^3) (tt - s' pow 2)
              (phi((gamma:real->A)(s' pow 2))) ** A1(lift s'))` THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:real` THEN DISCH_TAC THEN BETA_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "EQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "EQ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0]]);;

(* The derivative bound at s0.                                               *)

let P2AZ_ENERGY_BOUND = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt gamma b W a s0 K D.
     p2a_svs V /\ p2a_Lgeod V tt gamma b /\ &0 < s0 /\ s0 pow 2 < b /\
     p2a_region V W a tt /\ a < tt - s0 pow 2 /\ gamma(s0 pow 2) IN W /\
     &0 <= K /\ &0 <= D /\
     p3_vrm V (tt - s0 pow 2) (gamma(s0 pow 2)) <= K /\
     p2a_vgradR2 V (tt - s0 pow 2) (gamma(s0 pow 2)) <= D pow 2
     ==> &0 <= p2az_energy V tt gamma b s0 /\
         ?E'. (p2az_energy V tt gamma b has_real_derivative E') (atreal s0) /\
              E' <= &4 * s0 pow 2 * D * sqrt(p2az_energy V tt gamma b s0) +
                    &8 * s0 * K * p2az_energy V tt gamma b s0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `z0 = (gamma:real->A)(s0 pow 2)` THEN
  ABBREV_TAC `t0 = tt - s0 pow 2` THEN
  SUBGOAL_THEN `&0 < s0 pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `a < t0 /\ t0 < tt /\ a < tt` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`]
                P2AP_REGION_PERSISTS) THEN
  ASM_REWRITE_TAC[CONJUNCT2(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `tt:real` th)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `(z0:A) IN topspace(subtopology (rfs_vtop (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W)`
  ASSUME_TAC THENL
   [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`]
                P2AP_REGION_UPTO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                 `a:real`; `tt:real`;
                 `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W tt`; `t0:real`] P2AP_UPTO_RIEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) tt`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`; `W:A->bool`; `z0:A`]
                MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `b:real`; `W:A->bool`;
                 `a:real`; `U:A->bool`; `phi:A->real^3`; `s0:real`] P2AZ_ENERGY_LOCAL) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^3` (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  (* the chart family at t0 at phi z0 is the region metric at z0 *)
  SUBGOAL_THEN
   `metric_local (restrict_atlas (rfs_vatlas V tt) W) (U INTER W,phi:A->real^3)
                 (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) W tt t0) (phi(z0:A)) =
    p2c_vfam V W tt t0 z0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W tt t0`; `z0:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[SND];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_rlocal V W tt (U INTER W,phi:A->real^3) t0 (phi(z0:A)) =
    p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) W tt t0 z0`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2a_rlocal; P2AP_RMETRIC_VFAM; P2A_VIEW_PROJ_3] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2az_energy V tt (gamma:real->A) b s0 =
    (A0:real^3) dot (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) W tt t0 z0 ** A0)`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* Ricci in the preferred chart *)
  SUBGOAL_THEN
   `lricci (p2a_rlocal V W tt (U INTER W,phi:A->real^3) t0) (phi(z0:A)) (A0:real^3) A0 =
    mfd_ricci (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                 (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W)
              (p2c_vfam V W tt t0) z0 A0 A0`
  ASSUME_TAC THENL
   [REWRITE_TAC[p2a_rlocal; P2AP_RMETRIC_VFAM; P2A_VIEW_PROJ_3; mfd_ricci] THEN
    ASM_REWRITE_TAC[SND];
    ALL_TAC] THEN
  ABBREV_TAC `q = (A0:real^3) dot
                  (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) W tt t0 z0 ** A0)` THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
    MAP_EVERY EXISTS_TAC
     [`subtopology (rfs_vtop (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
      `restrict_atlas (rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(mfd_ricci (restrict_atlas (rfs_vatlas (V:(real->A topology)#
          (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W)
          (p2c_vfam V W tt t0) (z0:A) (A0:real^3) A0) <= &2 * K * q`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W tt t0`; `z0:A`; `A0:real^3`]
                  P2AP_MFD_RICCI_ABS) THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `t0:real`;
                   `z0:A`] P2AP_VFAM_RM_NORM_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `m = mfd_rm_norm (restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W)
                      (p2c_vfam V W tt t0) (z0:A)` THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (K - m) * q` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(lricci (p2a_rlocal V W tt (U INTER W,phi:A->real^3) t0) (phi(z0:A)) (A0:real^3) A0)
    <= &2 * K * q`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* dR *)
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `t0:real`;
                 `U:A->bool`; `phi:A->real^3`; `z0:A`] P2AZ_RLOCAL_SLICE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INTER] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^3) (U INTER W)) /\
                (phi:A->real^3) z0 IN IMAGE phi (U INTER W)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MFDR_RESTRICT_IMAGE_OPEN THEN
      MAP_EVERY EXISTS_TAC
       [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) tt`;
        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) tt`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `metric_field (IMAGE (phi:A->real^3) (U INTER W))
                 (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W tt (U INTER W,phi) t0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`;
                   `(U INTER W:A->bool,phi:A->real^3)`; `t0:real`] P2A_RLOCAL_FIELD) THEN
    REWRITE_TAC[FST; SND] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[P2A_VIEW_PROJ_3; IN_RESTRICT_ATLAS] THEN
    CONJ_TAC THENL [EXISTS_TAC `U:A->bool` THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) (U INTER W)`;
                 `p2a_rlocal (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W tt (U INTER W,phi:A->real^3) t0`;
                 `(phi:A->real^3) z0`;
                 `lscalar (p2a_rlocal (V:(real->A topology)#(real->((A->bool)#
                    (A->real^3))->bool)#(real->A->real^3^3)) W tt (U INTER W,phi:A->real^3) t0)`;
                 `A0:real^3`] P2AZ_DR_CS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (phi:A->real^3) (U INTER W)` THEN
    ASM_SIMP_TAC[LRG_LSCALAR_SMOOTH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
  ABBREV_TAC `dR = drop(frechet_derivative
                     (\z. lift(lscalar (p2a_rlocal V W tt (U INTER W,phi:A->real^3) t0) z))
                     (at (phi(z0:A))) (A0:real^3))` THEN
  SUBGOAL_THEN `abs(dR) <= D * sqrt q` ASSUME_TAC THENL
   [SUBGOAL_THEN `dR pow 2 <= (D * sqrt q) pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_POW_MUL] THEN ASM_SIMP_TAC[SQRT_POW_2] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `p2a_vgradR2 (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) t0 z0 * q` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt((D * sqrt q) pow 2)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM POW_2_SQRT_ABS] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC POW_2_SQRT THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE]];
    ALL_TAC] THEN
  ABBREV_TAC `Ric = lricci (p2a_rlocal V W tt (U INTER W,phi:A->real^3) t0) (phi(z0:A))
                           (A0:real^3) A0` THEN
  TRY(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  EXISTS_TAC `&4 * s0 pow 2 * dR - &4 * s0 * Ric` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= s0 pow 2 * (D * sqrt q - abs dR) /\
                &0 <= s0 * (&2 * K * q - abs Ric) /\
                &0 <= s0 pow 2 * (abs dR - dR) /\ &0 <= s0 * (abs Ric + Ric)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The energy bound (MT Lemma 6.60 in the form of Claim 8.6).                *)
(* Gronwall for E' <= al + be E; near s = 0, E <= 4 abs(Z)^2 + 1 (lsint is   *)
(* continuous at 0 with value 2 abs(Z)^2, and abs R <= 6 / r^2); so while   *)
(* the L-geodesic stays in B(x,tt,r/2),                                      *)
(*    E <= (4 abs(Z)^2 + 2) exp(be sqrt b),                                  *)
(* al = 2 b C1 / r^3, be = al + 8 sqrt b / r^2.                              *)
(* ------------------------------------------------------------------------- *)

let p2az_setting = new_definition
 `p2az_setting (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                  (real->A->real^3^3)) (tt:real) (x:A) (r:real) (C1:real) <=>
    p2a_svs V /\ &0 < r /\ x IN topspace(rfs_vtop V tt) /\ &0 <= C1 /\
    p2a_region V (rfs_vball V tt x r) (tt - r pow 2) tt /\
    compact_in (rfs_vtop V tt) ((rfs_vtop V tt) closure_of (rfs_vball V tt x r)) /\
    (!s y. tt - r pow 2 < s /\ s <= tt /\ y IN rfs_vball V tt x r
           ==> p3_vrm V s y <= inv(r pow 2)) /\
    (!s y. tt - r pow 2 / &2 <= s /\ s <= tt /\ y IN rfs_vball V tt x (r / &2)
           ==> p2a_vgradR2 V s y <= C1 pow 2 * inv(r pow 6))`;;

let P2AZ_GRONWALL = prove
 (`!(E:real->real) E' al be s1 s2.
     &0 <= al /\ &0 < be /\ s1 <= s2 /\
     (!s. s1 <= s /\ s <= s2
          ==> (E has_real_derivative E' s) (atreal s) /\ E' s <= al + be * E s)
     ==> E s2 + al / be <= (E s1 + al / be) * exp(be * (s2 - s1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s. (E:real->real) s + al / be`; `E':real->real`; `be:real`;
                 `real_interval[s1,s2]`; `s1:real`] ODE_GRONWALL_REAL_FORWARD) THEN
  REWRITE_TAC[IS_REALINTERVAL_INTERVAL; IN_REAL_INTERVAL] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      SUBGOAL_THEN `(E':real->real) s = E' s + &0` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ADD THEN
      ASM_REWRITE_TAC[HAS_REAL_DERIVATIVE_CONST; ETA_AX];
      SUBGOAL_THEN `be * ((E:real->real) s + al / be) = al + be * E s` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < be` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]];
    DISCH_THEN(MP_TAC o SPEC `s2:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL]]);;

(* lsint at s = 0 is 2 abs(Z)^2 in g(tt).                                    *)

let P2AZ_LSINT_ZERO = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x Z b gamma.
     p2a_Lgeod_from V tt x Z b gamma
     ==> p2a_lsint V tt gamma b (&0) = &2 * p2a_znorm2 V tt x Z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_MESON_TAC[p2a_Lgeod]; ALL_TAC] THEN
  REWRITE_TAC[p2a_lsint; p2a_znorm2] THEN
  REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_SUB_RZERO; REAL_MUL_LZERO; REAL_MUL_RZERO;
              REAL_ADD_RID] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vector_derivative
      (\v. SND(chart_at (p2a_vatlas V tt) (x:A)) ((gamma:real->A)(drop v pow 2)))
      (at (lift(&0)) within {v | &0 <= drop v /\ drop v pow 2 <= b}) = &2 % (Z:real^N)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[P2A_SDOM_INTERVAL; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    REWRITE_TAC[LIFT_NUM; DROP_VEC; LIFT_DROP; IN_INTERVAL_1] THEN
    ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POS_LE; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC
     `((\v. SND(chart_at (p2a_vatlas V tt) (x:A)) ((gamma:real->A)(drop v pow 2)))
       has_vector_derivative &2 % (Z:real^N))
      (at (vec 0) within {v | &0 <= drop v /\ drop v pow 2 <= b})` THEN
    ASM_SIMP_TAC[P2A_SDOM_INTERVAL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL; MATRIX_VECTOR_MUL_RMUL] THEN REAL_ARITH_TAC);;

(* Continuity of lsint at s = 0 along the L-geodesic of Z (from the joint   *)
(* continuity P2A_LSINT_CONT_ZERO).                                          *)

let P2AZ_LSINT_CONT0 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z e.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b /\ &0 < e
     ==> ?d. &0 < d /\
             !u. &0 <= u /\ u <= sqrt b /\ u < d
                 ==> abs(p2a_lsint V tt (p2a_Lgeo V tt x Z b) b u -
                         p2a_lsint V tt (p2a_Lgeo V tt x Z b) b (&0)) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`; `Z:real^N`]
                P2A_LSINT_CONT_ZERO) THEN
  ASM_REWRITE_TAC[continuous_within] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift u) (Z:real^N)`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
              IN_INTERVAL_1; DROP_VEC; DIST_PASTECART_CANCEL; DIST_LIFT] THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[]]);;

(* Near s = 0 the energy is at most 4 abs(Z)^2 + 1.                          *)

let P2AZ_ENERGY_NEAR0 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x r C1 b Z.
     p2az_setting V tt x r C1 /\ &0 < b /\ b < r pow 2 /\ Z IN p2a_Ldom V tt x b
     ==> ?e0. &0 < e0 /\
              !u. &0 <= u /\ u <= sqrt b /\ u < e0 /\
                  p2a_Lgeo V tt x Z b (u pow 2) IN rfs_vball V tt x r
                  ==> p2az_energy V tt (p2a_Lgeo V tt x Z b) b u <=
                      &4 * p2a_znorm2 V tt x Z + &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2az_setting] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN rfs_vball V tt x r` ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tt`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) tt`; `x:A`; `r:real`]
                  MFD_CENTRE_IN_BALL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2a_bsmooth (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) x tt` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_bsmooth] THEN
    MAP_EVERY EXISTS_TAC [`rfs_vball V tt (x:A) r`; `tt - r pow 2`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < r pow 2` MP_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `b:real`; `Z:real^3`;
                 `inv(&4)`] P2AZ_LSINT_CONT0) THEN
  ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN
  ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `Z:real^3`; `b:real`;
                 `p2a_Lgeo V tt (x:A) (Z:real^3) b`] P2AZ_LSINT_ZERO) THEN
  ANTS_TAC THENL [MATCH_MP_TAC P2A_LGEO_PROP THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `p2a_Lgeod V tt (p2a_Lgeo V tt (x:A) (Z:real^3) b) b` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `x:A`; `Z:real^3`; `b:real`]
                  P2A_LGEO_PROP) THEN
    ASM_SIMP_TAC[p2a_Lgeod_from];
    ALL_TAC] THEN
  EXISTS_TAC `min d (r / &7)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < d /\ &0 < r ==> &0 < min d (r / &7)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  ABBREV_TAC `gamma = p2a_Lgeo V tt (x:A) (Z:real^3) b` THEN
  SUBGOAL_THEN `&0 <= u pow 2 /\ u pow 2 <= b /\ u pow 2 < r pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN
    SUBGOAL_THEN `u pow 2 <= sqrt b pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* abs R <= 6 / r^2 at gamma(u^2) *)
  SUBGOAL_THEN
   `(gamma:real->A)(u pow 2) IN topspace(rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - u pow 2))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) tt (gamma:real->A) b` THEN
    REWRITE_TAC[p2a_Lgeod; P2A_VIEW_PROJ_3] THEN
    DISCH_THEN(MP_TAC o SPEC `u pow 2` o CONJUNCT1 o CONJUNCT2) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt - u pow 2`; `(gamma:real->A)(u pow 2)`]
                P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) (tt - u pow 2)`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (tt - u pow 2)`;
                 `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) (tt - u pow 2)`;
                 `(gamma:real->A)(u pow 2)`] P2AZ_MFD_SCALAR_ABS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `p3_vrm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
           (tt - u pow 2) ((gamma:real->A)(u pow 2)) <= inv(r pow 2)`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_vrm")) (concl th) &&
      is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p3_vrm] THEN DISCH_TAC THEN
  (* lsint near 0 *)
  USE_THEN "D" (MP_TAC o SPEC `u:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
  (* u^2 / r^2 <= 1 / 49 *)
  SUBGOAL_THEN `u pow 2 * inv(r pow 2) <= inv(&49)` ASSUME_TAC THENL
   [SUBGOAL_THEN `u pow 2 <= (r / &7) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_DIV] THEN
    SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
                 REAL_ARITH `&0 < &7 pow 2`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[p2az_energy; P2A_VIEW_PROJ_3] THEN
  ABBREV_TAC `R = mfd_scalar (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - u pow 2))
                    (rfs_vmetric V (tt - u pow 2)) ((gamma:real->A)(u pow 2))` THEN
  ABBREV_TAC `m = mfd_rm_norm (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - u pow 2))
                    (rfs_vmetric V (tt - u pow 2)) ((gamma:real->A)(u pow 2))` THEN
  SUBGOAL_THEN `abs(&4 * u pow 2 * R) <= &24 * (u pow 2 * inv(r pow 2))` MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_POW] THEN
    REWRITE_TAC[REAL_POW2_ABS] THEN
    SUBGOAL_THEN `abs R <= &6 * inv(r pow 2)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= u pow 2 * (&6 * inv(r pow 2) - abs R)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The energy bound while the L-geodesic stays in B(x,tt,r/2).               *)

let P2AZ_ENERGY_APRIORI = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x r C1 b Z s.
     p2az_setting V tt x r C1 /\ &0 < b /\ b <= r pow 2 / &2 /\ Z IN p2a_Ldom V tt x b /\
     &0 < s /\ s <= sqrt b /\
     (!u. &0 <= u /\ u <= s ==> p2a_Lgeo V tt x Z b (u pow 2) IN rfs_vball V tt x (r / &2))
     ==> !u. &0 < u /\ u < s
             ==> p2az_energy V tt (p2a_Lgeo V tt x Z b) b u <=
                 (&4 * p2a_znorm2 V tt x Z + &2) *
                 exp((&2 * b * (C1 * inv(r pow 3)) + &8 * sqrt b * inv(r pow 2)) * sqrt b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2az_setting]) THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `b < r pow 2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `r:real`; `C1:real`; `b:real`;
                 `Z:real^3`] P2AZ_ENERGY_NEAR0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "N0"))) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `Z:real^3`; `b:real`]
                P2A_LGEO_PROP) THEN
  ASM_REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  ABBREV_TAC `gamma = p2a_Lgeo V tt (x:A) (Z:real^3) b` THEN
  (* the half ball lies in the ball *)
  SUBGOAL_THEN `!u. &0 <= u /\ u <= s ==> (gamma:real->A)(u pow 2) IN rfs_vball V tt x r`
  (LABEL_TAC "INW") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tt`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) tt`;
                   `x:A`; `r / &2`; `r:real`] RFA_MFD_BALL_MONO) THEN
    REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)))] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(y:A) IN s ==> s SUBSET t ==> y IN t`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* constants *)
  SUBGOAL_THEN `&0 < sqrt b /\ &0 <= C1 * inv(r pow 3) /\ &0 < inv(r pow 2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_POW_LE; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `D = C1 * inv(r pow 3)` THEN ABBREV_TAC `K = inv(r pow 2)` THEN
  SUBGOAL_THEN `&0 <= &2 * b * D /\ &0 < &2 * b * D + &8 * sqrt b * K` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= b * D /\ &0 < sqrt b * K` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `al = &2 * b * D` THEN ABBREV_TAC `be = al + &8 * sqrt b * K` THEN
  (* the derivative bound on (0,s) *)
  SUBGOAL_THEN
   `!v. ?d. &0 < v /\ v < s
            ==> &0 <= p2az_energy (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) b v /\
                (p2az_energy V tt gamma b has_real_derivative d) (atreal v) /\
                d <= al + be * p2az_energy V tt gamma b v`
  MP_TAC THENL
   [X_GEN_TAC `v:real` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= v /\ v pow 2 < b /\ v pow 2 <= b /\ &0 <= v pow 2`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2] THEN
      SUBGOAL_THEN `v pow 2 < sqrt b pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(gamma:real->A)(v pow 2) IN rfs_vball V tt x (r / &2) /\
                  gamma(v pow 2) IN rfs_vball V tt x r` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> t = `r / &2`)) (concl th) && is_forall(concl th))) THEN
        ASM_REAL_ARITH_TAC;
        USE_THEN "INW" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `rfs_vball V tt (x:A) r`; `tt - r pow 2`; `v:real`; `K:real`; `D:real`]
                  P2AZ_ENERGY_BOUND) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_vrm")) (concl th) &&
          is_forall(concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "D" THEN
        REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV; REAL_POW_POW] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> is_const t && fst(dest_const t) = "p2a_vgradR2")) (concl th) &&
          is_forall(concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `E = p2az_energy (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) b v` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `w = sqrt E` THEN
    SUBGOAL_THEN `&0 <= w /\ w pow 2 = E` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `&2 * w <= &1 + E` ASSUME_TAC THENL
     [MP_TAC(SPEC `w - &1` REAL_LE_POW_2) THEN
      SUBGOAL_THEN `(w - &1) pow 2 = w pow 2 - &2 * w + &1` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 <= (v pow 2 * D) * ((&1 + E) - &2 * w) /\
      &0 <= ((b - v pow 2) * D) * (&1 + E) /\
      &0 <= ((sqrt b - v) * K) * E`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      (CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; ALL_TAC]) THEN
      ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["be"; "al"] THEN
    UNDISCH_TAC `d <= &4 * v pow 2 * D * w + &8 * v * K * E` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `E':real->real` (LABEL_TAC "DE")) THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  ABBREV_TAC `s1 = min u (e0 / &2)` THEN
  SUBGOAL_THEN `&0 < s1 /\ s1 <= u /\ s1 < e0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s1" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p2az_energy (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) b s1 <= &4 * p2a_znorm2 V tt x (Z:real^3) + &1`
  ASSUME_TAC THENL
   [USE_THEN "N0" MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "INW" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p2az_energy (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) b s1` ASSUME_TAC THENL
   [USE_THEN "DE" (MP_TAC o SPEC `s1:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2az_energy (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) b`; `E':real->real`; `al:real`; `be:real`;
                 `s1:real`; `u:real`] P2AZ_GRONWALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real` THEN STRIP_TAC THEN
    USE_THEN "DE" (MP_TAC o SPEC `v:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= al / be /\ al / be <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 < sqrt b * K` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "be" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(be * (u - s1)) <= exp(be * sqrt b)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p2az_energy (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) b s1 + al / be) * exp(be * (u - s1)) <=
    (&4 * p2a_znorm2 V tt x (Z:real^3) + &2) * exp(be * sqrt b)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * b * (C1 * inv(r pow 3)) + &8 * sqrt b * inv(r pow 2)) = be`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["be"; "al"; "D"; "K"] THEN REFL_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The curve s |-> gamma(s^2) on [0,s1] in the region manifold (W with the   *)
(* restricted atlas at tt) is C^1 (in every region chart it solves (6.5),    *)
(* P2AZ_CHART_SOL_W, one-sided at the ends), its speed in the time-tt metric *)
(* is at most e^(2 b / r^2) sqrt E, and its length bounds the time-tt        *)
(* distance from x.                                                          *)
(* ------------------------------------------------------------------------- *)

(* The chart curve in a region chart, near any s0 in [0, sqrt b], with      *)
(* derivatives within the parameter window (one-sided at the ends).          *)

let P2AZ_CHART_SOL_W = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt gamma b W a U (phi:A->real^N) s0.
     p2a_Lgeod V tt gamma b /\ &0 <= s0 /\ s0 pow 2 <= b /\
     p2a_region V W a tt /\ (U,phi) IN p2a_vatlas V tt /\ a < tt - s0 pow 2 /\
     gamma(s0 pow 2) IN U INTER W
     ==> ?e A1. &0 < e /\
                !u. u IN {u | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < e}
                    ==> gamma(drop u pow 2) IN U INTER W /\ a < tt - drop u pow 2 /\
                        ((\v. phi(gamma(drop v pow 2))) has_vector_derivative A1 u)
                          (at u within {u | &0 <= drop u /\ drop u pow 2 <= b /\
                                            abs(drop u - s0) < e}) /\
                        (A1 has_vector_derivative
                           p2a_lacc (p2a_rlocal V W tt (U INTER W,phi)) tt (drop u)
                                    (phi(gamma(drop u pow 2))) (A1 u))
                          (at u within {u | &0 <= drop u /\ drop u pow 2 <= b /\
                                            abs(drop u - s0) < e})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= s0 pow 2 /\ (&0 < s0 ==> &0 < s0 pow 2)` STRIP_ASSUME_TAC THENL
   [SIMP_TAC[REAL_LE_POW_2; REAL_POW_LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`]
                P2A_LGEOD_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`W2:A->bool`; `a2:real`; `b2:real`; `U2:A->bool`; `phi2:A->real^N`;
                       `d:real`; `A2:real^1->real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "TW2") (CONJUNCTS_THEN2 (LABEL_TAC "IN2")
    (CONJUNCTS_THEN2 (LABEL_TAC "D2") (K ALL_TAC)))))))) THEN
  SUBGOAL_THEN `a2 < tt - s0 pow 2 /\ tt - s0 pow 2 <= b2` STRIP_ASSUME_TAC THENL
   [USE_THEN "TW2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(s0 pow 2) IN U2 INTER W2` ASSUME_TAC THENL
   [USE_THEN "IN2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W2:A->bool`; `a2:real`; `b2:real`; `b2:real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `open_in (p2a_vtop V tt) (U:A->bool) /\
    open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) b2) (U2:A->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) tt`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) tt`;
                     `(U:A->bool,phi:A->real^N)`] MFDM_CHART);
      MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`;
                     `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                    (real->A->real^N^N)) b2`;
                     `(U2:A->bool,phi2:A->real^N)`] MFDM_CHART)] THEN
    ASM_SIMP_TAC[FST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                         (real->A->real^N^N)) (tt - s0 pow 2))
            ((U INTER W) INTER (U2 INTER W2):A->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC THEN MATCH_MP_TAC P2A_REGION_OPEN_BACK THENL
     [MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`; `tt:real`];
      MAP_EVERY EXISTS_TAC [`W2:A->bool`; `a2:real`; `b2:real`]] THEN
    ASM_SIMP_TAC[INTER_SUBSET; OPEN_IN_INTER] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `gamma:real->A`; `b:real`; `s0:real`;
                 `(U INTER W) INTER (U2 INTER W2):A->bool`] P2A_LGEOD_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C1"))) THEN
  MP_TAC(SPECL [`a:real`; `tt:real`; `tt:real`; `s0:real`] P2A_TIME_WINDOW) THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TW1")))] THEN
  ABBREV_TAC `e = min (min e1 e2) d` THEN
  SUBGOAL_THEN `&0 < e /\ e <= e1 /\ e <= e2 /\ e <= d` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `J = {u:real^1 | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < e}` THEN
  SUBGOAL_THEN
   `!u:real^1. u IN J <=> &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - s0) < e`
  (LABEL_TAC "J") THENL
   [GEN_TAC THEN EXPAND_TAC "J" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `is_interval(J:real^1->bool) /\
                J SUBSET {v:real^1 | &0 <= drop v /\ drop v pow 2 <= b} /\
                tt - s0 pow 2 <= tt` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "J" THEN REWRITE_TAC[P2A_SWIN_INTERVAL];
      EXPAND_TAC "J" THEN SET_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN J
        ==> s0 - e < drop u /\ drop u < s0 + e /\
            (gamma:real->A)(drop u pow 2) IN (U2 INTER W2) INTER (U INTER W) /\
            a < tt - drop u pow 2 /\ tt - drop u pow 2 <= tt /\
            a2 < tt - drop u pow 2 /\ tt - drop u pow 2 <= b2 /\
            ((\v. (phi2:A->real^N)(gamma(drop v pow 2))) has_vector_derivative
             (A2:real^1->real^N) u)
              (at u within {v | &0 <= drop v /\ drop v pow 2 <= b}) /\
            (A2 has_vector_derivative
               p2a_lacc (p2a_rlocal V W2 b2 (U2 INTER W2,phi2)) tt (drop u)
                        (phi2(gamma(drop u pow 2))) (A2 u))
              (at u within {v | &0 <= drop v /\ drop v pow 2 <= b})`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^1` THEN USE_THEN "J" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      USE_THEN "C1" (MP_TAC o SPEC `drop(u:real^1)`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SET_TAC[]];
      USE_THEN "TW1" (MP_TAC o SPEC `drop(u:real^1)`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "TW1" (MP_TAC o SPEC `drop(u:real^1)`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "TW2" (MP_TAC o SPEC `drop(u:real^1)`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "TW2" (MP_TAC o SPEC `drop(u:real^1)`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "D2" (MP_TAC o SPEC `u:real^1`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "D2" (MP_TAC o SPEC `u:real^1`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `W:A->bool`; `a:real`; `tt:real`;
                 `U:A->bool`; `phi:A->real^N`; `W2:A->bool`; `a2:real`; `b2:real`;
                 `U2:A->bool`; `phi2:A->real^N`; `tt - s0 pow 2`; `tt:real`; `gamma:real->A`;
                 `b:real`; `A2:real^1->real^N`; `J:real^1->bool`; `s0 - e`; `s0 + e`]
                P2A_TRANS_ODE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[P2A_LSOL_ODE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "SOL")) (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `!u. u IN J
        ==> chart_trans (U2 INTER W2,phi2) (U INTER W,phi:A->real^N)
              (phi2((gamma:real->A)(drop u pow 2))) = phi(gamma(drop u pow 2))`
  (LABEL_TAC "TR") THENL
   [X_GEN_TAC `u:real^1` THEN USE_THEN "J" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    REWRITE_TAC[chart_trans; SND] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p2a_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                (real->A->real^N^N)) b2`;
                   `p2a_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                                  (real->A->real^N^N)) b2`; `U2:A->bool`; `phi2:A->real^N`;
                   `W2:A->bool`; `(gamma:real->A)(drop u pow 2)`] MFDR_CHART_INV_RESTRICT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "IN2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `e:real` THEN
  EXISTS_TAC `\u:real^1. frechet_derivative (chart_trans (U2 INTER W2,phi2) (U INTER W,phi:A->real^N))
                           (at (phi2((gamma:real->A)(drop u pow 2)))) ((A2:real^1->real^N) u)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^1) IN J` ASSUME_TAC THENL
   [USE_THEN "J" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "SOL" (MP_TAC o SPEC `u:real^1`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  USE_THEN "TR" (MP_TAC o SPEC `u:real^1`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "TRu")] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "C1" (MP_TAC o SPEC `drop(u:real^1)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SET_TAC[]];
    USE_THEN "TW1" (MP_TAC o SPEC `drop(u:real^1)`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    BETA_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN THEN
    EXISTS_TAC `\u:real^1. chart_trans (U2 INTER W2,phi2) (U INTER W,phi:A->real^N)
                             (phi2((gamma:real->A)(drop u pow 2)))` THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN BETA_TAC THEN
    USE_THEN "TR" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    BETA_TAC THEN
    UNDISCH_TAC
     `((\u:real^1. frechet_derivative (chart_trans (U2 INTER W2,phi2) (U INTER W,phi:A->real^N))
                     (at (phi2((gamma:real->A)(drop u pow 2)))) ((A2:real^1->real^N) u))
       has_vector_derivative
       p2a_lacc (p2a_rlocal V W tt (U INTER W,phi)) tt (drop u)
         (chart_trans (U2 INTER W2,phi2) (U INTER W,phi) (phi2(gamma(drop u pow 2))))
         (frechet_derivative (chart_trans (U2 INTER W2,phi2) (U INTER W,phi))
            (at (phi2(gamma(drop u pow 2)))) (A2 u)))
      (at u within J)` THEN
    USE_THEN "TRu" (fun th -> REWRITE_TAC[th])]);;

(* C^1 from derivatives within a superset, continuous there.                *)

let P2AZ_CD1_FROM_WITHIN = prove
 (`!(f:real^1->real^N) f' S J.
     S SUBSET J /\
     (!x. x IN S ==> (f has_vector_derivative f' x) (at x within J) /\
                     f' continuous (at x within J))
     ==> continuously_differentiable 1 S f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[num_CONV `1`; continuously_differentiable] THEN
  EXISTS_TAC `\x:real^1 h:real^1. drop h % (f':real^1->real^N) x` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `J:real^1->bool` THEN ASM_REWRITE_TAC[GSYM has_vector_derivative];
    X_GEN_TAC `h:real^1` THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC CONTINUOUS_CMUL THEN MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
    EXISTS_TAC `J:real^1->bool` THEN ASM_MESON_TAC[]]);;

(* The curve s |-> gamma(s^2) on [0,s1] is continuous into the region       *)
(* manifold while it stays in W.                                             *)

let P2AZ_KAPPA_CONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt gamma b W a s1.
     p2a_Lgeod V tt gamma b /\ p2a_region V W a tt /\ a < tt - b /\
     &0 <= s1 /\ s1 pow 2 <= b /\
     (!u. &0 <= u /\ u <= s1 ==> gamma(u pow 2) IN W)
     ==> continuous_map (subtopology euclideanreal (real_interval[&0,s1]),
                         subtopology (rfs_vtop V tt) W) (\u. gamma(u pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
   [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[P2A_VIEW_PROJ_3] THEN STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN ASM_MESON_TAC[]] THEN
  REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gamma:real->A)(u pow 2) IN W` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`; `W:A->bool`] OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `O:A->bool` THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `u0:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `u0 pow 2 <= b /\ &0 <= u0 pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A)(u0 pow 2) IN W` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `b:real`; `u0:real`;
                 `(O:A->bool) INTER W`] P2A_LGEOD_CONT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INTER] THEN
    MATCH_MP_TAC P2A_REGION_OPEN_BACK THEN
    MAP_EVERY EXISTS_TAC [`W:A->bool`; `a:real`; `tt:real`] THEN
    ASM_SIMP_TAC[P2A_VIEW_PROJ_3; OPEN_IN_INTER; INTER_SUBSET] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `real_interval(u0 - e,u0 + e) INTER real_interval[&0,s1]` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
    EXISTS_TAC `real_interval(u0 - e,u0 + e)` THEN
    REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_REAL_INTERVAL];
    REWRITE_TAC[IN_INTER; IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_INTER; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `u pow 2 <= b` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(y:A) IN O INTER W ==> y IN O`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ... and C^1 there (in every region chart, by P2AZ_CHART_SOL_W).           *)

let P2AZ_KAPPA_C1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt gamma b W a s1.
     p2a_Lgeod V tt gamma b /\ p2a_region V W a tt /\ a < tt - b /\
     &0 < s1 /\ s1 pow 2 <= b /\
     (!u. &0 <= u /\ u <= s1 ==> gamma(u pow 2) IN W)
     ==> mfd_c1_curve (subtopology (rfs_vtop V tt) W,restrict_atlas (rfs_vatlas V tt) W)
                      (\u. gamma(u pow 2)) (&0) s1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[mfd_c1_curve] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2AZ_KAPPA_CONT THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `a:real`] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_RESTRICT_ATLAS; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`UW:A->bool`; `phi:A->real^3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  ABBREV_TAC `S = {s:real^1 | s IN interval[lift(&0),lift s1] /\
                              (gamma:real->A)(drop s pow 2) IN U INTER W}` THEN
  (* local C^1 pieces *)
  SUBGOAL_THEN
   `!v0. v0 IN S
         ==> ?S'. open_in (subtopology euclidean (interval[lift(&0),lift s1])) S' /\
                  v0 IN S' /\ S' SUBSET S /\
                  continuously_differentiable 1 S'
                    (\s:real^1. (phi:A->real^3)((gamma:real->A)(drop s pow 2)))`
  (LABEL_TAC "LOC") THENL
   [X_GEN_TAC `v0:real^1` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN STRIP_TAC THEN
    SUBGOAL_THEN `drop v0 pow 2 <= b` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `b:real`;
                   `W:A->bool`; `a:real`; `U:A->bool`; `phi:A->real^3`; `drop(v0:real^1)`]
                  P2AZ_CHART_SOL_W) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN
      SUBGOAL_THEN `&0 <= drop(v0:real^1) pow 2` MP_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `A1:real^1->real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W1")))) THEN
    EXISTS_TAC `interval[lift(&0),lift s1] INTER ball(v0:real^1,e)` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `ball(v0:real^1,e)` THEN
      REWRITE_TAC[OPEN_BALL];
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL; IN_INTERVAL_1; LIFT_DROP; DROP_VEC];
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "W1" (MP_TAC o SPEC `w:real^1`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `dist(v0:real^1,w) < e` THEN
          REWRITE_TAC[DIST_REAL; GSYM drop] THEN REAL_ARITH_TAC];
        SIMP_TAC[IN_INTER]];
      MATCH_MP_TAC P2AZ_CD1_FROM_WITHIN THEN
      MAP_EVERY EXISTS_TAC
       [`A1:real^1->real^3`;
        `{u:real^1 | &0 <= drop u /\ drop u pow 2 <= b /\ abs(drop u - drop v0) < e}`] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_INTERVAL_1; LIFT_DROP; DROP_VEC;
                    IN_ELIM_THM] THEN
        X_GEN_TAC `w:real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `dist(v0:real^1,w) < e` THEN
          REWRITE_TAC[DIST_REAL; GSYM drop] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      X_GEN_TAC `w:real^1` THEN
      REWRITE_TAC[IN_INTER; IN_BALL; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN STRIP_TAC THEN
      USE_THEN "W1" (MP_TAC o SPEC `w:real^1`) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s1 pow 2` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `dist(v0:real^1,w) < e` THEN
          REWRITE_TAC[DIST_REAL; GSYM drop] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN THEN
      REWRITE_TAC[differentiable] THEN
      EXISTS_TAC `\h:real^1. drop h %
                    p2a_lacc (p2a_rlocal V W tt (U INTER W,phi:A->real^3)) tt (drop w)
                      (phi((gamma:real->A)(drop w pow 2))) ((A1:real^1->real^3) w)` THEN
      ASM_REWRITE_TAC[GSYM has_vector_derivative]];
    ALL_TAC] THEN
  MATCH_MP_TAC GRGD_C1_LOCAL THEN EXISTS_TAC `&0` THEN EXISTS_TAC `s1:real` THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `v0:real^1` THEN DISCH_TAC THEN
  USE_THEN "LOC" (MP_TAC o SPEC `v0:real^1`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]]);;

(* The time-tt speed of the curve at an interior u is at most                *)
(* exp(2 K u^2) sqrt E(u) (metric comparison P2AP_METRIC_COMPARE).          *)

let P2AZ_SPEED_BOUND = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt gamma b W a K s1 u.
     p2a_svs V /\ p2a_Lgeod V tt gamma b /\ p2a_region V W a tt /\ a < tt - b /\ &0 <= K /\
     (!t z. a < t /\ t <= tt /\ z IN W ==> p3_vrm V t z <= K) /\
     &0 < s1 /\ s1 pow 2 <= b /\ (!v. &0 <= v /\ v <= s1 ==> gamma(v pow 2) IN W) /\
     &0 < u /\ u < s1
     ==> mfd_speed (restrict_atlas (rfs_vatlas V tt) W)
                   (restrict_metric (rfs_vatlas V tt) W (rfs_vmetric V tt))
                   (\v. gamma(v pow 2)) (&0) s1 u
         <= exp(&2 * K * u pow 2) * sqrt(p2az_energy V tt gamma b u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < u pow 2 /\ u pow 2 < b /\ u pow 2 <= b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT] THEN
    SUBGOAL_THEN `u pow 2 < s1 pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `z = (gamma:real->A)(u pow 2)` THEN
  ABBREV_TAC `t = tt - u pow 2` THEN
  SUBGOAL_THEN `(z:A) IN W /\ a < t /\ t < tt /\ t <= tt` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> t = `s1:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[P2A_VIEW_PROJ_3] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) tt`;
                 `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`; `W:A->bool`; `z:A`]
                MFDR_CHART_AT_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `b:real`; `W:A->bool`;
                 `a:real`; `U:A->bool`; `phi:A->real^3`; `u:real`] P2AZ_ENERGY_LOCAL) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `A0:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC))) THEN
  (* the velocity *)
  SUBGOAL_THEN
   `mfd_velocity (restrict_atlas (rfs_vatlas V tt) W) (\v. (gamma:real->A)(v pow 2))
                 (&0) s1 u = (A0:real^3)`
  ASSUME_TAC THENL
   [REWRITE_TAC[mfd_velocity] THEN BETA_TAC THEN ASM_REWRITE_TAC[SND] THEN
    MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN
    REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the chart family at a time t' at phi z is the region metric at z *)
  SUBGOAL_THEN
   `!t'. a < t' /\ t' <= tt
         ==> p2a_rlocal V W tt (U INTER W,phi:A->real^3) t' (phi(z:A)) =
             p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                         (real->A->real^3^3)) W tt t' z`
  (LABEL_TAC "PT") THENL
   [X_GEN_TAC `t':real` THEN STRIP_TAC THEN
    REWRITE_TAC[p2a_rlocal; P2AP_RMETRIC_VFAM; P2A_VIEW_PROJ_3] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`]
                  P2AP_REGION_UPTO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `a:real`; `tt:real`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W tt`; `t':real`] P2AP_UPTO_RIEM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                   `p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) W tt t'`; `z:A`] METRIC_LOCAL_AT) THEN
    ASM_REWRITE_TAC[SND; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `restrict_metric (rfs_vatlas V tt) W (rfs_vmetric V tt) (z:A) =
    p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                (real->A->real^3^3)) W tt tt z`
  ASSUME_TAC THENL [REWRITE_TAC[p2c_vfam; ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2az_energy V tt (gamma:real->A) b u =
    (A0:real^3) dot (p2c_vfam (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                 (real->A->real^3^3)) W tt t z ** A0)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    USE_THEN "PT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `K:real`;
                 `t:real`; `z:A`; `A0:real^3`] P2AP_METRIC_COMPARE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[P2AP_RMETRIC_VFAM] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `tt - t = u pow 2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[mfd_speed] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `exp(&2 * K * u pow 2) = sqrt(exp(&4 * K * u pow 2))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    REWRITE_TAC[REAL_EXP_POS_LE; GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
  USE_THEN "PT" (fun th -> REWRITE_TAC[MATCH_MP th
    (CONJ (ASSUME `a < t`) (ASSUME `t <= tt`))]) THEN
  ASM_REWRITE_TAC[]);;

(* A continuous bound on the open interval holds at the ends.               *)

let P2AZ_CONT_LE_ENDS = prove
 (`!f a b L.
     a < b /\ f real_continuous_on real_interval[a,b] /\
     (!u. a < u /\ u < b ==> f u <= L)
     ==> !u. a <= u /\ u <= b ==> f u <= L`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `(f:real->real) real_continuous_on real_interval[a,b]` THEN
  REWRITE_TAC[real_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `u:real`) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN DISCH_THEN(MP_TAC o SPEC `(f:real->real) u - L`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `u < b` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u + min (d / &2) ((b - u) / &2)`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u + min (d / &2) ((b - u) / &2)`);
    FIRST_X_ASSUM(MP_TAC o SPEC `u - min (d / &2) ((b - a) / &2)`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u - min (d / &2) ((b - a) / &2)`)] THEN
  ASM_REAL_ARITH_TAC);;

(* The length of the curve bounds the time-tt distance from x.              *)

let P2AZ_KAPPA_BALL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x gamma b W a s1 L rho.
     p2a_svs V /\ p2a_Lgeod V tt gamma b /\ gamma(&0) = x /\
     p2a_region V W a tt /\ a < tt - b /\
     &0 < s1 /\ s1 pow 2 <= b /\ (!v. &0 <= v /\ v <= s1 ==> gamma(v pow 2) IN W) /\
     (!u. &0 < u /\ u < s1
          ==> mfd_speed (restrict_atlas (rfs_vatlas V tt) W)
                        (restrict_metric (rfs_vatlas V tt) W (rfs_vmetric V tt))
                        (\v. gamma(v pow 2)) (&0) s1 u <= L) /\
     L * s1 < rho
     ==> gamma(s1 pow 2) IN
         mfd_ball (rfs_vtop V tt,rfs_vatlas V tt) (rfs_vmetric V tt) x rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= b` ASSUME_TAC THENL
   [MP_TAC(SPEC `s1:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `W:A->bool`; `a:real`; `tt:real`; `tt:real`]
                P2A_REGION_SLICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[P2A_VIEW_PROJ_3] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN W` ASSUME_TAC THENL
   [SUBGOAL_THEN `(gamma:real->A)(&0 pow 2) IN W` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_POW_ZERO; ARITH]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2AP_SLICE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `smooth_manifold_atlas (subtopology (rfs_vtop V tt) W)
      (restrict_atlas (rfs_vatlas (V:(real->A topology)#
         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W) /\
    riemannian_metric (restrict_atlas (rfs_vatlas V tt) W)
      (restrict_metric (rfs_vatlas V tt) W (rfs_vmetric V tt))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN
    MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
    EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3)) tt` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `b:real`; `W:A->bool`;
                 `a:real`; `s1:real`] P2AZ_KAPPA_C1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `sp = mfd_speed (restrict_atlas (rfs_vatlas V tt) W)
                     (restrict_metric (rfs_vatlas V tt) W
                        (rfs_vmetric (V:(real->A topology)#
                           (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt))
                     (\v. (gamma:real->A)(v pow 2)) (&0) s1` THEN
  SUBGOAL_THEN `!u. &0 <= u /\ u <= s1 ==> sp u <= L` ASSUME_TAC THENL
   [MATCH_MP_TAC P2AZ_CONT_LE_ENDS THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "sp" THEN
    MATCH_MP_TAC MFD_SPEED_CONTINUOUS THEN
    EXISTS_TAC `subtopology (rfs_vtop (V:(real->A topology)#
                  (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `mfd_length (restrict_atlas (rfs_vatlas V tt) W)
      (restrict_metric (rfs_vatlas V tt) W
         (rfs_vmetric (V:(real->A topology)#
            (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt))
      (\v. (gamma:real->A)(v pow 2)) (&0) s1 <= L * s1`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[mfd_length] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[&0,s1]) (\u:real. L)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
      CONJ_TAC THENL
       [EXPAND_TAC "sp" THEN MATCH_MP_TAC GRGD_SPEED_INTEGRABLE THEN
        EXISTS_TAC `subtopology (rfs_vtop (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_MESON_TAC[]];
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                 `restrict_metric (rfs_vatlas V tt) W
                    (rfs_vmetric (V:(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)`;
                 `\v. (gamma:real->A)(v pow 2)`; `&0`; `s1:real`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_POW_ZERO; ARITH] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                 `restrict_atlas (rfs_vatlas (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) W`;
                 `\v. (gamma:real->A)(v pow 2)`; `&0`; `s1:real`] MFD_C1_CURVE_JOINABLE) THEN
  ASM_REWRITE_TAC[] THEN BETA_TAC THEN
  REWRITE_TAC[REAL_POW_ZERO; ARITH] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(SET_RULE `!s t. (y:A) IN s /\ s SUBSET t ==> y IN t`) THEN
  EXISTS_TAC `mfd_ball (subtopology (rfs_vtop V tt) W,restrict_atlas (rfs_vatlas V tt) W)
                (restrict_metric (rfs_vatlas V tt) W
                  (rfs_vmetric (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)) x rho` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[mfd_ball; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC P2AP_RESTRICT_BALL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MT Claim 8.7.  The constants: for eps <= 1/256 and C1 eps <= 1/16 the     *)
(* length bound of the previous section is at most 3 r / 8 < 2 r / 5         *)
(* (P2AZ_ARITH); then the continuity induction (P2A_REAL_CONT_INDUCT) keeps  *)
(* the L-geodesic in B(x,tt,r/2): while it stays there it stays in the       *)
(* compact ball cbar B(x,tt,2r/5), which is closed in every slice of the     *)
(* region.                                                                   *)
(* ------------------------------------------------------------------------- *)

let P2AZ_ARITH = prove
 (`!r eps C1 zn.
     &0 < r /\ &0 < eps /\ eps <= inv(&256) /\ &0 <= C1 /\ C1 * eps <= inv(&16) /\
     &0 <= zn /\ &64 * eps * zn <= &1
     ==> exp(&2 * inv(r pow 2) * (eps * r pow 2)) *
         sqrt((&4 * zn + &2) *
              exp((&2 * (eps * r pow 2) * (C1 * inv(r pow 3)) +
                   &8 * sqrt(eps * r pow 2) * inv(r pow 2)) * sqrt(eps * r pow 2))) *
         sqrt(eps * r pow 2) < &2 * r / &5`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(eps * r pow 2) = sqrt eps * r` SUBST1_TAC THENL
   [REWRITE_TAC[SQRT_MUL] THEN AP_TERM_TAC THEN MATCH_MP_TAC POW_2_SQRT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `se = sqrt eps` THEN
  SUBGOAL_THEN `&0 < se /\ se pow 2 = eps /\ se <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "se" THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[SQRT_POS_LT];
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * inv(r pow 2) * (eps * r pow 2) = &2 * eps` SUBST1_TAC THENL
   [UNDISCH_TAC `~(r = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 * (eps * r pow 2) * (C1 * inv(r pow 3)) + &8 * (se * r) * inv(r pow 2)) * (se * r) =
    &2 * eps * se * C1 + &8 * eps`
  SUBST1_TAC THENL
   [UNDISCH_TAC `se pow 2 = eps` THEN UNDISCH_TAC `~(r = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(&2 * eps) = sqrt(exp(&4 * eps))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
    REWRITE_TAC[REAL_EXP_POS_LE; GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(exp(&4 * eps)) * sqrt((&4 * zn + &2) * exp(&2 * eps * se * C1 + &8 * eps)) *
    se * r =
    sqrt((&4 * zn + &2) * eps * exp(&4 * eps + (&2 * eps * se * C1 + &8 * eps))) * r`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `se = sqrt eps` SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM SQRT_MUL; REAL_EXP_ADD; REAL_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * eps + (&2 * eps * se * C1 + &8 * eps) <= inv(&2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `eps * se * C1 <= C1 * eps` MP_TAC THENL
     [SUBGOAL_THEN `&0 <= (C1 * eps) * (&1 - se)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 * eps + (&2 * eps * se * C1 + &8 * eps)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= eps * se * C1` MP_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `&4 * eps + (&2 * eps * se * C1 + &8 * eps)` REAL_EXP_BOUND_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `X = exp(&4 * eps + (&2 * eps * se * C1 + &8 * eps))` THEN
  SUBGOAL_THEN `&0 <= X /\ X <= &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 * zn + &2) * eps * X <= &9 / &64` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= (&4 * zn + &2) * eps /\ (&4 * zn + &2) * eps <= &9 / &128`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&9 / &128) * &2` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
      CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&3 / &8 * r` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&9 / &64)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SQRT_UNIQUE THEN
        CONV_TAC REAL_RAT_REDUCE_CONV];
      ASM_REAL_ARITH_TAC];
    ASM_REAL_ARITH_TAC]);;

(* While the L-geodesic stays in B(x,tt,r/2) on [0,s], gamma(s^2) lies in   *)
(* B(x,tt,2r/5).                                                              *)

let P2AZ_STEP_BALL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x r C1 eps Z s.
     p2az_setting V tt x r C1 /\ &0 < eps /\ eps <= inv(&256) /\ C1 * eps <= inv(&16) /\
     Z IN p2a_Ldom V tt x (eps * r pow 2) /\ &64 * eps * p2a_znorm2 V tt x Z <= &1 /\
     &0 < s /\ s <= sqrt(eps * r pow 2) /\
     (!u. &0 <= u /\ u <= s
          ==> p2a_Lgeo V tt x Z (eps * r pow 2) (u pow 2) IN rfs_vball V tt x (r / &2))
     ==> p2a_Lgeo V tt x Z (eps * r pow 2) (s pow 2) IN
         mfd_ball (rfs_vtop V tt,rfs_vatlas V tt) (rfs_vmetric V tt) x (&2 * r / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2az_setting]) THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps * r pow 2 /\ eps * r pow 2 <= r pow 2 / &2 /\
                eps * r pow 2 < r pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (inv(&2) - eps) * r pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p2a_znorm2 V tt (x:A) (Z:real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_znorm2; P2A_VIEW_PROJ_3] THEN MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
    MAP_EVERY EXISTS_TAC
     [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                   (real->A->real^3^3)) tt`;
      `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) tt`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `r:real`; `C1:real`;
                 `eps * r pow 2`; `Z:real^3`; `s:real`] P2AZ_ENERGY_APRIORI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "AP") THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `Z:real^3`; `eps * r pow 2`]
                P2A_LGEO_PROP) THEN
  ASM_REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  ABBREV_TAC `gamma = p2a_Lgeo V tt (x:A) (Z:real^3) (eps * r pow 2)` THEN
  SUBGOAL_THEN `!u. &0 <= u /\ u <= s ==> (gamma:real->A)(u pow 2) IN rfs_vball V tt x r`
  (LABEL_TAC "INW") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tt`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) tt`;
                   `x:A`; `r / &2`; `r:real`] RFA_MFD_BALL_MONO) THEN
    REWRITE_TAC[GSYM(CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND)))] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(y:A) IN s ==> s SUBSET t ==> y IN t`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s pow 2 <= eps * r pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps * r pow 2) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC
   `L = exp(&2 * inv(r pow 2) * (eps * r pow 2)) *
        sqrt((&4 * p2a_znorm2 V tt (x:A) (Z:real^3) + &2) *
             exp((&2 * (eps * r pow 2) * (C1 * inv(r pow 3)) +
                  &8 * sqrt(eps * r pow 2) * inv(r pow 2)) * sqrt(eps * r pow 2)))` THEN
  MATCH_MP_TAC P2AZ_KAPPA_BALL THEN
  MAP_EVERY EXISTS_TAC [`eps * r pow 2`; `rfs_vball V tt (x:A) r`; `tt - r pow 2`; `L:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `u:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `eps * r pow 2`;
                   `rfs_vball V tt (x:A) r`; `tt - r pow 2`; `inv(r pow 2)`; `s:real`; `u:real`]
                  P2AZ_SPEED_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    ABBREV_TAC `sp = mfd_speed (restrict_atlas (rfs_vatlas V tt) (rfs_vball V tt x r))
                       (restrict_metric (rfs_vatlas V tt) (rfs_vball V tt x r)
                          (rfs_vmetric (V:(real->A topology)#
                             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt))
                       (\v. (gamma:real->A)(v pow 2)) (&0) s u` THEN
    DISCH_TAC THEN
    USE_THEN "AP" (MP_TAC o SPEC `u:real`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= sp` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `rfs_vball V tt (x:A) r`; `tt - r pow 2`;
                     `tt:real`; `tt:real`] P2A_REGION_SLICE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[P2A_VIEW_PROJ_3] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `smooth_manifold_atlas (subtopology (rfs_vtop V tt) (rfs_vball V tt x r))
          (restrict_atlas (rfs_vatlas (V:(real->A topology)#
             (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)
             (rfs_vball V tt (x:A) r)) /\
        riemannian_metric (restrict_atlas (rfs_vatlas V tt) (rfs_vball V tt x r))
          (restrict_metric (rfs_vatlas V tt) (rfs_vball V tt x r) (rfs_vmetric V tt)) /\
        mfd_c1_curve (subtopology (rfs_vtop V tt) (rfs_vball V tt x r),
                      restrict_atlas (rfs_vatlas V tt) (rfs_vball V tt x r))
                     (\v. (gamma:real->A)(v pow 2)) (&0) s`
      STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[SMOOTH_MANIFOLD_ATLAS_RESTRICT] THEN CONJ_TAC THENL
         [MATCH_MP_TAC RIEMANNIAN_METRIC_RESTRICT THEN
          EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tt` THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC P2AZ_KAPPA_C1 THEN
          MAP_EVERY EXISTS_TAC [`eps * r pow 2`; `tt - r pow 2`] THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      EXPAND_TAC "sp" THEN MATCH_MP_TAC MFD_SPEED_POS_LE THEN
      EXISTS_TAC `subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)
                    (rfs_vball V tt (x:A) r)` THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "L" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(&2 * inv(r pow 2) * u pow 2) *
                sqrt(p2az_energy (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) (eps * r pow 2) u)` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sqrt(p2az_energy (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) (eps * r pow 2) u)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= exp(&2 * inv(r pow 2) * u pow 2) *
                         sqrt(p2az_energy (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) (eps * r pow 2) u)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; SIMP_TAC[REAL_LE_MUL_EQ; REAL_EXP_POS_LT]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      SUBGOAL_THEN `u pow 2 <= eps * r pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `s pow 2` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= inv(r pow 2) * (eps * r pow 2 - u pow 2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `L * sqrt(eps * r pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "L" THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "L" THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC P2AZ_ARITH THEN ASM_REWRITE_TAC[]]]);;

(* MT Claim 8.7: the L-geodesic stays in B(x,tt,r/2) up to tau = eps r^2.   *)

let P2AZ_IN_HALF = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x r C1 eps Z.
     p2az_setting V tt x r C1 /\ &0 < eps /\ eps <= inv(&256) /\ C1 * eps <= inv(&16) /\
     Z IN p2a_Ldom V tt x (eps * r pow 2) /\ &64 * eps * p2a_znorm2 V tt x Z <= &1
     ==> !s. &0 <= s /\ s <= sqrt(eps * r pow 2)
             ==> p2a_Lgeo V tt x Z (eps * r pow 2) (s pow 2) IN rfs_vball V tt x (r / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2az_setting]) THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps * r pow 2 /\ eps * r pow 2 < r pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 - eps) * r pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `Z:real^3`; `eps * r pow 2`]
                P2A_LGEO_PROP) THEN
  ASM_REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  ABBREV_TAC `gamma = p2a_Lgeo V tt (x:A) (Z:real^3) (eps * r pow 2)` THEN
  SUBGOAL_THEN
   `open_in (rfs_vtop (V:(real->A topology)#
      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)
      (rfs_vball V tt (x:A) (r / &2)) /\
    rfs_vball V tt x (r / &2) SUBSET rfs_vball V tt x r /\
    rfs_vball V tt x r SUBSET topspace(rfs_vtop V tt) /\
    x IN rfs_vball V tt x (r / &2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MFD_BALL_OPEN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RFA_MFD_BALL_MONO THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[P2AP_BALL_SUBSET];
      MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tt`;
                     `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                    (real->A->real^3^3)) tt`;
                     `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                     (real->A->real^3^3)) tt`; `x:A`; `r / &2`]
                    MFD_CENTRE_IN_BALL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the compact ball cbar B(x,tt,2r/5) *)
  ABBREV_TAC `K0 = mfd_cball (rfs_vtop V tt,rfs_vatlas V tt)
                     (rfs_vmetric (V:(real->A topology)#
                        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)
                     (x:A) (&2 * r / &5)` THEN
  SUBGOAL_THEN `(K0:A->bool) SUBSET rfs_vball V tt x (r / &2) /\
                K0 SUBSET rfs_vball V tt x r /\
                mfd_ball (rfs_vtop V tt,rfs_vatlas V tt)
                  (rfs_vmetric (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)
                  (x:A) (&2 * r / &5) SUBSET K0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
    REWRITE_TAC[mfd_ball; mfd_cball; SUBSET; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. tt - r pow 2 < t /\ t <= tt
        ==> closed_in (rfs_vtop (V:(real->A topology)#
                         (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t) K0`
  (LABEL_TAC "KC") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `compact_in (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt) K0`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSED_COMPACT_IN THEN
      EXISTS_TAC `rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                              (real->A->real^3^3)) tt closure_of rfs_vball V tt x r` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `rfs_vball V tt (x:A) r` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_SUBSET THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "K0" THEN MATCH_MP_TAC MFD_CBALL_CLOSED THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `compact_in (subtopology (rfs_vtop (V:(real->A topology)#
                    (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) t)
                    (rfs_vball V tt (x:A) r)) K0`
    MP_TAC THENL
     [MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                        (real->A->real^3^3)`; `rfs_vball V tt (x:A) r`; `tt - r pow 2`;
                     `tt:real`; `t:real`] P2A_REGION_SUBTOP) THEN
      ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY] THEN STRIP_TAC THEN
    MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2a_svs (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                            (real->A->real^3^3))` THEN
    REWRITE_TAC[p2a_svs; P2A_VIEW_PROJ_3] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the s-range *)
  SUBGOAL_THEN `!s. &0 <= s /\ s <= sqrt(eps * r pow 2)
                    ==> s pow 2 <= eps * r pow 2 /\ tt - r pow 2 < tt - s pow 2 /\
                        tt - s pow 2 <= tt`
  (LABEL_TAC "SR") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `s pow 2 <= eps * r pow 2 /\ &0 <= s pow 2` MP_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(eps * r pow 2) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_LE_REFL]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC P2A_REAL_CONT_INDUCT THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
  REPEAT CONJ_TAC THENL
   [(* start *)
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `eps * r pow 2`;
                   `&0`; `rfs_vball V tt (x:A) (r / &2)`] P2A_LGEOD_CONT) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POW_ZERO; ARITH; REAL_SUB_RZERO; P2A_VIEW_PROJ_3] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "C0"))) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "C0" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [USE_THEN "SR" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[];
      ASM_REAL_ARITH_TAC];
    (* closed step *)
    X_GEN_TAC `Tm:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH"))) THEN
    USE_THEN "SR" (MP_TAC o SPEC `Tm:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `!s. &0 < s /\ s < Tm ==> (gamma:real->A)(s pow 2) IN K0` (LABEL_TAC "IK")
    THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s t. (y:A) IN s /\ s SUBSET t ==> y IN t`) THEN
      EXISTS_TAC `mfd_ball (rfs_vtop V tt,rfs_vatlas V tt)
                    (rfs_vmetric (V:(real->A topology)#
                       (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt)
                    (x:A) (&2 * r / &5)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "gamma" THEN
      MATCH_MP_TAC P2AZ_STEP_BALL THEN EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      USE_THEN "IH" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s. (y:A) IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `K0:A->bool` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `eps * r pow 2`;
                   `Tm:real`;
                   `topspace(rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                         (real->A->real^3^3)) (tt - Tm pow 2)) DIFF K0`]
                  P2A_LGEOD_CONT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE; P2A_VIEW_PROJ_3] THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_TOPSPACE] THEN
        USE_THEN "KC" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_DIFF] THEN
        UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tt (gamma:real->A) (eps * r pow 2)` THEN
        REWRITE_TAC[p2a_Lgeod; P2A_VIEW_PROJ_3] THEN
        DISCH_THEN(MP_TAC o SPEC `Tm pow 2` o CONJUNCT1 o CONJUNCT2) THEN
        ASM_SIMP_TAC[REAL_LE_POW_2]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CT"))) THEN
    USE_THEN "IK" (MP_TAC o SPEC `Tm - min e Tm / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    USE_THEN "SR" (MP_TAC o SPEC `Tm - min e Tm / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    USE_THEN "CT" (MP_TAC o SPEC `Tm - min e Tm / &2`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_DIFF];
    (* open step *)
    X_GEN_TAC `Tm:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IH"))) THEN
    USE_THEN "SR" (MP_TAC o SPEC `Tm:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `eps * r pow 2`;
                   `Tm:real`; `rfs_vball V tt (x:A) (r / &2)`] P2A_LGEOD_CONT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[P2A_VIEW_PROJ_3] (ISPEC
          `V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`
          P2A_REGION_OPEN_BACK)) THEN
        MAP_EVERY EXISTS_TAC [`rfs_vball V tt (x:A) r`; `tt - r pow 2`; `tt:real`] THEN
        ASM_REWRITE_TAC[];
        USE_THEN "IH" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "CT"))) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    USE_THEN "CT" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "SR" (MP_TAC o SPEC `s:real`) THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* l~ >= -2 eps (the L-length in s-form, lsint >= 2 s^2 R and R >= -6 / r^2  *)
(* along the curve, which stays in B(x,tt,r/2)), and the headlines: route O6 *)
(* and L9 with eps0 = min(1/256, 1/(16 (C1 + 1))).                           *)
(* ------------------------------------------------------------------------- *)

(* lsint is continuous on [0, sqrt b] along the L-geodesic of Z.            *)

let P2AZ_LSINT_CONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#(real->A->real^N^N))
    tt x b Z.
     p2a_svs V /\ x IN topspace(p2a_vtop V tt) /\ p2a_bsmooth V x tt /\
     Z IN p2a_Ldom V tt x b
     ==> (p2a_lsint V tt (p2a_Lgeo V tt x Z b) b) real_continuous_on real_interval[&0,sqrt b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `b:real`] P2A_LSINT_JOINT) THEN
  ASM_REWRITE_TAC[continuous_on; real_continuous_on] THEN DISCH_TAC THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s) (Z:real^N)`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s':real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (lift s') (Z:real^N)`) THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP;
              IN_INTERVAL_1; DROP_VEC; DIST_PASTECART_CANCEL; DIST_LIFT] THEN
  ASM_REWRITE_TAC[]);;

(* The reduced length of a short L-geodesic is at least -2 eps.             *)

let P2AZ_LTIL_BOUND = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tt x r C1 eps Z.
     p2az_setting V tt x r C1 /\ &0 < eps /\ eps <= inv(&256) /\ C1 * eps <= inv(&16) /\
     Z IN p2a_Ldom V tt x (eps * r pow 2) /\ &64 * eps * p2a_znorm2 V tt x Z <= &1
     ==> --(&2 * eps) <= p2a_ltil V tt x (eps * r pow 2) Z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `r:real`; `C1:real`; `eps:real`;
                 `Z:real^3`] P2AZ_IN_HALF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2az_setting]) THEN
  SUBGOAL_THEN `&0 < r pow 2` ASSUME_TAC THENL [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eps * r pow 2 /\ eps * r pow 2 < r pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 - eps) * r pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `b = eps * r pow 2` THEN
  SUBGOAL_THEN `&0 < sqrt b /\ sqrt b pow 2 = b` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`] P2AP_SLICE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2a_bsmooth (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                               (real->A->real^3^3)) x tt` ASSUME_TAC THENL
   [REWRITE_TAC[p2a_bsmooth] THEN
    MAP_EVERY EXISTS_TAC [`rfs_vball V tt (x:A) r`; `tt - r pow 2`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) tt`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) tt`; `x:A`; `r:real`]
                  MFD_CENTRE_IN_BALL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `b:real`; `Z:real^3`]
                P2AZ_LSINT_CONT) THEN
  ASM_REWRITE_TAC[P2A_VIEW_PROJ_3] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `x:A`; `Z:real^3`; `b:real`]
                P2A_LGEO_PROP) THEN
  ASM_REWRITE_TAC[p2a_Lgeod_from] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_ltil; p2a_Ltil] THEN
  ABBREV_TAC `gamma = p2a_Lgeo V tt (x:A) (Z:real^3) b` THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                    (real->A->real^3^3)`; `tt:real`; `gamma:real->A`; `b:real`]
                P2A_L_LENGTH_SFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  (* the pointwise lower bound *)
  SUBGOAL_THEN
   `!s. s IN real_interval[&0,sqrt b]
        ==> --(&12 * inv(r pow 2)) * s pow 2 <= p2a_lsint (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) b s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= s pow 2 /\ s pow 2 <= b` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LE_POW_2] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && lhand(concl th) = `sqrt b pow 2`)) THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(gamma:real->A)(s pow 2) IN rfs_vball V tt x r` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t. (y:A) IN s /\ s SUBSET t ==> y IN t`) THEN
      EXISTS_TAC `rfs_vball V tt (x:A) (r / &2)` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term (fun t -> t = `r / &2`)) (concl th) && is_forall(concl th))) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[CONJUNCT1(CONJUNCT2(SPEC_ALL P2C_VIEW_EXPAND))] THEN
        MATCH_MP_TAC RFA_MFD_BALL_MONO THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(gamma:real->A)(s pow 2) IN topspace(rfs_vtop (V:(real->A topology)#
        (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - s pow 2))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `p2a_Lgeod (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) tt (gamma:real->A) b` THEN
      REWRITE_TAC[p2a_Lgeod; P2A_VIEW_PROJ_3] THEN
      DISCH_THEN(MP_TAC o SPEC `s pow 2` o CONJUNCT1 o CONJUNCT2) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt - s pow 2`; `(gamma:real->A)(s pow 2)`]
                  P2AP_SLICE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                (real->A->real^3^3)) (tt - s pow 2)`;
                   `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                  (real->A->real^3^3)) (tt - s pow 2)`;
                   `rfs_vmetric (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                                   (real->A->real^3^3)) (tt - s pow 2)`;
                   `(gamma:real->A)(s pow 2)`] P2AZ_MFD_SCALAR_ABS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `p3_vrm (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
             (tt - s pow 2) ((gamma:real->A)(s pow 2)) <= inv(r pow 2)`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "p3_vrm")) (concl th) &&
        is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[p3_vrm] THEN DISCH_TAC THEN
    REWRITE_TAC[p2a_lsint; P2A_VIEW_PROJ_3] THEN
    ABBREV_TAC `R = mfd_scalar (rfs_vatlas (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - s pow 2))
                      (rfs_vmetric V (tt - s pow 2)) ((gamma:real->A)(s pow 2))` THEN
    ABBREV_TAC
     `vd = vector_derivative
             (\v. SND(chart_at (rfs_vatlas (V:(real->A topology)#
                     (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) (tt - s pow 2))
                     ((gamma:real->A)(s pow 2))) (gamma(drop v pow 2)))
             (at (lift s) within {v | &0 <= drop v /\ drop v pow 2 <= b})` THEN
    SUBGOAL_THEN
     `&0 <= vd dot (rfs_vmetric (V:(real->A topology)#
                      (real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
                      (tt - s pow 2) ((gamma:real->A)(s pow 2)) ** vd)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC P2AP_QFORM_NONNEG THEN
      MAP_EVERY EXISTS_TAC
       [`rfs_vtop (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                     (real->A->real^3^3)) (tt - s pow 2)`;
        `rfs_vatlas (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                       (real->A->real^3^3)) (tt - s pow 2)`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s pow 2 * (&6 * inv(r pow 2) + R)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* integrate *)
  SUBGOAL_THEN
   `((\s. --(&12 * inv(r pow 2)) * s pow 2) has_real_integral
     (--(&4 * inv(r pow 2)) * sqrt b pow 3 - --(&4 * inv(r pow 2)) * &0 pow 3))
    (real_interval[&0,sqrt b])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s. --(&4 * inv(r pow 2)) * s pow 3`;
                   `\s. --(&12 * inv(r pow 2)) * s pow 2`; `&0`; `sqrt b`]
                  REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
    REAL_DIFF_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `--(&4 * inv(r pow 2)) * sqrt b pow 3 <=
    real_integral (real_interval[&0,sqrt b]) (p2a_lsint (V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)) tt (gamma:real->A) b)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[&0,sqrt b])
                  (\s. --(&12 * inv(r pow 2)) * s pow 2)` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
      REWRITE_TAC[REAL_POW_ZERO; ARITH] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS] THEN
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_REAL_INTEGRAL_INTEGRABLE)];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * sqrt b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `--(&4 * inv(r pow 2)) * sqrt b pow 3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sqrt b pow 3 = b * sqrt b` SUBST1_TAC THENL
   [SUBGOAL_THEN `sqrt b pow 3 = sqrt b pow 2 * sqrt b` SUBST1_TAC THENL
     [CONV_TAC REAL_RING; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&4 * inv(r pow 2)) * (b * sqrt b) = --(&4 * eps) * sqrt b`
  SUBST1_TAC THENL
   [UNDISCH_TAC `eps * r pow 2 = b` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD;
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Headlines.                                                                *)
(* ------------------------------------------------------------------------- *)

let P2AZ_ROUTE_SMALLZ = prove
 (`!u:A->bool. P2A_ROUTE_SMALLZ_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_ROUTE_SMALLZ_STATEMENT] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[P2A_PARABOLIC_STATEMENT; P2A_SMALLZ_STATEMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PAR"))) THEN
  X_GEN_TAC `taub:real` THEN DISCH_TAC THEN
  EXISTS_TAC `min (inv(&256)) (inv(&16 * (C1 + &1)))` THEN
  SUBGOAL_THEN `&0 < inv(&16 * (C1 + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> &0 < min a b`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
    `tt:real`; `x:A`; `r:real`; `eps:real`; `Z:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `eps <= inv(&256) /\ C1 * eps <= inv(&16)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `eps <= inv(&256) /\ eps <= inv(&16 * (C1 + &1))` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `eps * (&16 * (C1 + &1)) <= &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv(&16 * (C1 + &1)) * (&16 * (C1 + &1))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_MUL_LINV THEN
        ASM_REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `p2az_setting V tt (x:A) r C1` ASSUME_TAC THENL
   [REWRITE_TAC[p2az_setting] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "PAR" (MP_TAC o SPECL
     [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3)`;
      `tt:real`; `x:A`; `r:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#
                      (real->A->real^3^3)`; `tt:real`; `x:A`; `r:real`; `C1:real`; `eps:real`;
                   `Z:real^3`] P2AZ_IN_HALF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `sqrt tau`) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; SQRT_MONO_LE; SQRT_POW_2];
    MATCH_MP_TAC P2AZ_LTIL_BOUND THEN EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[]]);;

let P2AZ_SMALLZ = prove
 (`!u:A->bool. P2A_SMALLZ_STATEMENT u`,
  GEN_TAC THEN MP_TAC(SPEC `u:A->bool` P2AZ_ROUTE_SMALLZ) THEN
  REWRITE_TAC[P2A_ROUTE_SMALLZ_STATEMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[P2AP_PARABOLIC; P2A_LGEOD_FLOW]);;

