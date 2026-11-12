(* ========================================================================= *)
(* Unit pc_p2b_c914 (Part 2B): MT Cor 9.14 as the route                      *)
(* P2B_COR_9_14_ROUTE_STATEMENT of pc_p2b_w920g, from FL5 and FL5R of        *)
(* pc_p2a_fldefs.  Also the shared lemmas of the global layer: locality of   *)
(* the reduced length in the view interval (P2BX_LX_VIEW_LOCAL,              *)
(* P2BX_KLX_VIEW, P2BX_KFRV_VIEW: the views of [a,0] with a < -tau agree at  *)
(* backward time tau) and the bridge from kappa-solutions to p2a_cbflow      *)
(* (P2BX_KSOL_CBFLOW).                                                       *)
(*                                                                           *)
(* First: views of a flow on [a,0]: projections, regions, smooth points,     *)
(* admissible curves, the reduced length and the reduced volume.             *)
(* ========================================================================= *)

needs "src/pc_p2b_w920g.ml";;

prioritize_real();;
type_invention_error := true;;

let P2BX_VIEW_PROJ = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) J (g:real->A->real^N^N) t.
     p2a_vtop (p2a_flow_view (top,atlas) J g) t =
       (if t IN J then top else discrete_topology {}) /\
     p2a_vatlas (p2a_flow_view (top,atlas) J g) = (\t. atlas) /\
     p2a_vmetric (p2a_flow_view (top,atlas) J g) = g`,
  REWRITE_TAC[p2a_flow_view; p2a_vtop; p2a_vatlas; p2a_vmetric]);;

(* Restriction of a flow smooth up to b to a later initial time. *)

let P2BX_FLOW_UPTO_MONO = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a a' b (g:real->A->real^N^N).
     p2a_flow_upto (top,atlas) a b g /\ a <= a' /\ a' < b
     ==> p2a_flow_upto (top,atlas) a' b g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_flow_upto] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RICCI_FLOW_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:(A->bool)#(A->real^N)` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(A->bool)#(A->real^N)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (X_CHOOSE_THEN `Fx:real^(1,N)finite_sum->real^(N,N)finite_prod`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `Fx:real^(1,N)finite_sum->real^(N,N)finite_prod`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `interval(lift a,lift(b + e)) PCROSS
                IMAGE (SND (c:(A->bool)#(A->real^N))) (FST c)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SUBSET; IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* A nonempty region of the view of J lies in J. *)

let P2BX_REGION_IN_J = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) J (g:real->A->real^N^N) W a b s.
     p2a_region (p2a_flow_view (top,atlas) J g) W a b /\ ~(W = {}) /\ a < s /\ s <= b
     ==> s IN J`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_region; P2A_PERSISTS_ALT; P2BX_VIEW_PROJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 (LABEL_TAC "R1") (K ALL_TAC))
                             STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "R1" (MP_TAC o SPEC `s:real`) THEN
  ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET o CONJUNCT2) THEN
  REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY] THEN ASM SET_TAC[]);;

(* A region of the view of J1 restricted to (a',b], an interval in J1 and   *)
(* J2, is a region of the view of J2.                                        *)

let P2BX_REGION_TRANSFER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) J1 J2 (g:real->A->real^N^N)
    W a a' b.
     p2a_region (p2a_flow_view (top,atlas) J1 g) W a b /\ a <= a' /\ a' < b /\
     (!s. a' < s /\ s <= b ==> s IN J1 /\ s IN J2)
     ==> p2a_region (p2a_flow_view (top,atlas) J2 g) W a' b`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `p2a_rmetric (p2a_flow_view (top:A topology,atlas) J2 (g:real->A->real^N^N)) =
                p2a_rmetric (p2a_flow_view (top,atlas) J1 g)` ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; p2a_rmetric; P2BX_VIEW_PROJ]; ALL_TAC] THEN
  REWRITE_TAC[p2a_region; P2A_PERSISTS_ALT; P2BX_VIEW_PROJ] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 (LABEL_TAC "R1") (CONJUNCTS_THEN2 (LABEL_TAC "R2") (LABEL_TAC "R3")))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "J")))) THEN
  SUBGOAL_THEN `(b:real) IN J1 /\ b IN J2` STRIP_ASSUME_TAC THENL
   [USE_THEN "J" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real) IN J1 /\ s IN J2` STRIP_ASSUME_TAC THENL
     [USE_THEN "J" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "R1" (MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `s:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real) IN J1 /\ s IN J2` STRIP_ASSUME_TAC THENL
     [USE_THEN "J" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "R2" (MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REMOVE_THEN "R3" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC P2BX_FLOW_UPTO_MONO THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[]]);;

(* Smooth points at times t > max(a1,a2) are the same for both views. *)

let P2BX_SMOOTH_TRANSFER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a1 a2 (g:real->A->real^N^N) y t.
     a1 < t /\ a2 < t /\
     p2a_smooth (p2a_flow_view (top,atlas) (real_interval[a1,&0]) g) y t
     ==> p2a_smooth (p2a_flow_view (top,atlas) (real_interval[a2,&0]) g) y t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_smooth] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `W:A->bool` (X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
      STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `!s. a < s /\ s <= b ==> s IN real_interval[a1,&0]` (LABEL_TAC "J") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_REGION_IN_J THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                          `g:real->A->real^N^N`; `W:A->bool`; `a:real`; `b:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a1 <= a /\ b <= &0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      USE_THEN "J" (MP_TAC o SPEC `(a + a1) / &2`) THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC;
      USE_THEN "J" (MP_TAC o SPEC `b:real`) THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`W:A->bool`; `max a a2`; `b:real`] THEN
  ASM_REWRITE_TAC[REAL_MAX_LT] THEN
  MATCH_MP_TAC P2BX_REGION_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`real_interval[a1,&0]`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN CONJ_TAC THENL
   [USE_THEN "J" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;

(* Admissible curves up to backward time b < -a1, -a2 are the same. *)

let P2BX_ADM_TRANSFER = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a1 a2 (g:real->A->real^N^N)
    x b gamma.
     b < --a1 /\ b < --a2 /\
     p2a_adm (p2a_flow_view (top,atlas) (real_interval[a1,&0]) g) (&0) x b gamma
     ==> p2a_adm (p2a_flow_view (top,atlas) (real_interval[a2,&0]) g) (&0) x b gamma`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN
   `!tau. &0 <= tau /\ tau <= b
          ==> p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a2,&0])
                          (g:real->A->real^N^N)) (&0 - tau) =
              p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a1,&0]) g) (&0 - tau)`
  (LABEL_TAC "VT") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 - tau IN real_interval[a1,&0] /\ &0 - tau IN real_interval[a2,&0]`
    (fun th -> REWRITE_TAC[th; P2BX_VIEW_PROJ]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2a_pc1 (p2a_flow_view (top,atlas) (real_interval[a2,&0]) (g:real->A->real^N^N)) =
    p2a_pc1 (p2a_flow_view (top,atlas) (real_interval[a1,&0]) g) /\
    p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a2,&0]) g) =
    p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a1,&0]) g)`
  (fun th -> REWRITE_TAC[p2a_adm; th]) THENL
   [REWRITE_TAC[FUN_EQ_THM; p2a_pc1; p2a_L_integrand; P2BX_VIEW_PROJ]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "A3") (CONJUNCTS_THEN2 (LABEL_TAC "A4")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "A6") ASSUME_TAC)))))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    USE_THEN "VT" (MP_TAC o SPEC `tau:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REMOVE_THEN "A3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    USE_THEN "VT" (MP_TAC o SPEC `tau0:real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    UNDISCH_TAC `open_in (p2a_vtop (p2a_flow_view (top,atlas) (real_interval[a2,&0])
                          (g:real->A->real^N^N)) (&0 - tau0)) (O:A->bool)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REMOVE_THEN "A4" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2BX_SMOOTH_TRANSFER THEN
    EXISTS_TAC `a1:real` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "A6" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The reduced length at backward time tau does not depend on the view      *)
(* interval [a,0] as long as a < -tau.                                       *)

let P2BX_LX_VIEW_LOCAL = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) a1 a2 (g:real->A->real^N^N)
    p tau q.
     tau < --a1 /\ tau < --a2
     ==> p2a_lx (p2a_flow_view (top,atlas) (real_interval[a1,&0]) g) (&0) p tau q =
         p2a_lx (p2a_flow_view (top,atlas) (real_interval[a2,&0]) g) (&0) p tau q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_lx; p2a_Lx] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a1,&0]) (g:real->A->real^N^N)) =
    p2a_L_length (p2a_flow_view (top,atlas) (real_interval[a2,&0]) g)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a1,&0])
                        (g:real->A->real^N^N)) =
      p2a_L_integrand (p2a_flow_view (top,atlas) (real_interval[a2,&0]) g)`
    (fun th -> REWRITE_TAC[FUN_EQ_THM; p2a_L_length; th]) THEN
    REWRITE_TAC[FUN_EQ_THM; p2a_L_integrand; P2BX_VIEW_PROJ];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real` THEN
  EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `gamma:real->A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BX_ADM_TRANSFER THEN
  ASM_MESON_TAC[]);;

(* The Part 2B reduced length p2b_klx and reduced volume p2b_kfrv of a flow  *)
(* on t <= 0, read on the view of any [a,0] with a < -tau.                   *)

let P2BX_KLX_VIEW = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) p tau q a.
     &0 < tau /\ tau < --a
     ==> p2b_klx (top,atlas) g p tau q =
         p2a_lx (p2a_flow_view (top,atlas) (real_interval[a,&0]) g) (&0) p tau q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2b_klx] THEN
  MATCH_MP_TAC P2BX_LX_VIEW_LOCAL THEN ASM_REAL_ARITH_TAC);;

let P2BX_KFRV_VIEW = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) (g:real->A->real^3^3) p tau a.
     &0 < tau /\ tau < --a
     ==> p2b_kfrv (top,atlas) g p tau = p2a_frv (top,atlas) a (&0) g p tau`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2b_kfrv; p2a_frv] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `q:A` THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC P2BX_LX_VIEW_LOCAL THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* kappa-solutions as p2a_cbflow on every [a,0], and the route of MT Cor     *)
(* 9.14.                                                                     *)
(* ========================================================================= *)


let P2BX_KSOL_CBFLOW = prove
 (`!kappa top atlas (g:real->B->real^3^3) a.
     p2b_kappa_solution kappa (top,atlas) g /\ a < &0
     ==> p2a_cbflow (top,atlas) a (&0) g`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2B_KSOL_BASIC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "flow")
    (CONJUNCTS_THEN2 (LABEL_TAC "compl") (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bnd"))))) THEN
  SUBGOAL_THEN `rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [USE_THEN "flow" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) (a - &1) (&0) (g:real->B->real^3^3)` MP_TAC THENL
   [USE_THEN "flow" (MP_TAC o SPEC `a - &1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[rfs_flow_upto]]; ALL_TAC] THEN
  REWRITE_TAC[ricci_flow_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "met") (CONJUNCTS_THEN2 (LABEL_TAC "sm") ASSUME_TAC)))) THEN
  SUBGOAL_THEN `ricci_flow_on (top,atlas) a (&0) (g:real->B->real^3^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_flow_upto (top,atlas) a (&0) (g:real->B->real^3^3)` THEN
    SIMP_TAC[rfs_flow_upto]; ALL_TAC] THEN
  SUBGOAL_THEN `riemannian_metric atlas ((g:real->B->real^3^3) a)` ASSUME_TAC THENL
   [USE_THEN "met" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN atlas
        ==> ?e F. &0 < e /\
                  smooth_map_on
                    (interval(lift(a - e),lift (&0)) PCROSS IMAGE (SND c) (FST c)) F /\
                  !t y. a <= t /\ t < &0 /\ y IN IMAGE (SND c) (FST c)
                        ==> F(pastecart (lift t) y) =
                            (vectorize:real^3^3->real^(3,3)finite_prod)
                            (metric_local atlas c ((g:real->B->real^3^3) t) y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:(B->bool)#(B->real^3)` THEN DISCH_TAC THEN
    EXISTS_TAC `&1` THEN
    EXISTS_TAC `\z:real^(1,3)finite_sum.
                  (vectorize:real^3^3->real^(3,3)finite_prod)
                  (metric_local atlas c ((g:real->B->real^3^3) (drop(fstcart z))) (sndcart z))` THEN
    REWRITE_TAC[REAL_LT_01; FSTCART_PASTECART; SNDCART_PASTECART; LIFT_DROP] THEN
    USE_THEN "sm" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. a <= t /\ t <= &0 ==> mfd_complete (top,atlas) ((g:real->B->real^3^3) t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN USE_THEN "compl" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?K. !t y. a <= t /\ t <= &0 /\ y IN topspace top
                          ==> mfd_rm_norm atlas ((g:real->B->real^3^3) t) y <= K`
  ASSUME_TAC THENL
   [USE_THEN "bnd" (MP_TAC o SPEC `a:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; MESON_TAC[]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[P2AF_CBFLOW_3; ricci_flow_from]);;

(* Two noncollinear vectors of real^3, and |Rm| = 0 when all sectional      *)
(* curvatures vanish (mfd_rm_norm is the sup of their absolute values).     *)

let P2BX_NONCOLLINEAR_BASIS = prove
 (`~collinear {vec 0:real^3, basis 1, basis 2}`,
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
  X_GEN_TAC `c:real` THEN DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. v$2`) THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REAL_ARITH_TAC);;

let P2BX_RM_NORM_FLAT = prove
 (`!(atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3) x.
     (!u v. ~collinear {vec 0,u,v} ==> mfd_sectional atlas g x u v = &0)
     ==> mfd_rm_norm atlas g x <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_rm_norm] THEN MATCH_MP_TAC REAL_SUP_LE THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC
     [`abs(mfd_sectional atlas (g:B->real^3^3) x (basis 1) (basis 2))`;
      `basis 1:real^3`; `basis 2:real^3`] THEN
    REWRITE_TAC[P2BX_NONCOLLINEAR_BASIS];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REAL_ARITH_TAC]);;

(* A nonnegative nonincreasing function on (0,inf) converges at infinity to *)
(* its infimum.                                                              *)

let P2BX_DECREASING_LIMIT = prove
 (`!f:real->real.
     (!t. &0 < t ==> &0 <= f t) /\ (!t1 t2. &0 < t1 /\ t1 <= t2 ==> f t2 <= f t1)
     ==> (f ---> inf {f t | &0 < t}) at_posinfinity /\
         &0 <= inf {f t | &0 < t} /\
         (!t. &0 < t ==> inf {f t | &0 < t} <= f t)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `{(f:real->real) t | &0 < t}` INF) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    CONJ_TAC THENL [MAP_EVERY EXISTS_TAC [`(f:real->real) (&1)`; `&1`] THEN
                    REWRITE_TAC[REAL_LT_01];
                    EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  ABBREV_TAC `V = inf {(f:real->real) t | &0 < t}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "glb")) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; USE_THEN "glb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?t0. &0 < t0 /\ (f:real->real) t0 < V + e` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?t0. &0 < t0 /\ (f:real->real) t0 < V + e` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "glb" (MP_TAC o SPEC `V + e:real`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[REAL_NOT_LT]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `t0:real` THEN X_GEN_TAC `x:real` THEN REWRITE_TAC[real_ge] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `V <= (f:real->real) x /\ f x <= f t0` MP_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* The route of MT Cor 9.14: FL5 on [-2 tau, 0] (and on larger views by      *)
(* P2BX_KFRV_VIEW) makes tau -> p2b_kfrv positive, at most (4 pi)^(3/2) and  *)
(* nonincreasing, so it has a limit V >= 0 at infinity; V = (4 pi)^(3/2)     *)
(* would make the reduced volume maximal at tau = 1, and FL5R would make     *)
(* g(0) flat, against the non-flatness of kappa-solutions.                    *)

let P2B_COR_9_14_ROUTE = prove
 (`!w:B->bool. P2B_COR_9_14_ROUTE_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[P2B_COR_9_14_ROUTE_STATEMENT; P2B_COR_9_14_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "FL5") (LABEL_TAC "FL5R")) THEN
  MAP_EVERY X_GEN_TAC [`kappa:real`; `top:B topology`;
                       `atlas:((B->bool)#(B->real^3))->bool`; `g:real->B->real^3^3`;
                       `p:B`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `connected_space (top:B topology)` ASSUME_TAC THENL
   [UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
    SIMP_TAC[p2b_kappa_solution; p2c_kappa_sol]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. a < &0 ==> p2a_cbflow (top,atlas) a (&0) (g:real->B->real^3^3)`
  (LABEL_TAC "CB") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P2BX_KSOL_CBFLOW THEN
    EXISTS_TAC `kappa:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a tau1 tau2.
      a < &0 /\ &0 < tau1 /\ tau1 <= tau2 /\ tau2 < --a
      ==> &0 < p2a_frv (top,atlas) a (&0) (g:real->B->real^3^3) p tau2 /\
          p2a_frv (top,atlas) a (&0) g p tau2 <= sqrt(&4 * pi) pow 3 /\
          p2a_frv (top,atlas) a (&0) g p tau2 <= p2a_frv (top,atlas) a (&0) g p tau1`
  (LABEL_TAC "FV") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "FL5" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                    `a:real`; `&0`; `g:real->B->real^3^3`; `p:B`] o
                    REWRITE_RULE[P2A_FLOW_RV_STATEMENT]) THEN
    ASM_SIMP_TAC[DIMINDEX_3] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `tau2:real`)
                               (MP_TAC o SPECL [`tau1:real`; `tau2:real`] o CONJUNCT1)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `RV = \t. p2b_kfrv (top,atlas) (g:real->B->real^3^3) p t` THEN
  SUBGOAL_THEN
   `!t. &0 < t ==> &0 < (RV:real->real) t /\ RV t <= sqrt(&4 * pi) pow 3`
  (LABEL_TAC "FB") THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN EXPAND_TAC "RV" THEN
    REWRITE_TAC[p2b_kfrv] THEN
    USE_THEN "FV" (MP_TAC o SPECL [`--(&2 * t)`; `t:real`; `t:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t1 t2. &0 < t1 /\ t1 <= t2 ==> (RV:real->real) t2 <= RV t1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "RV" THEN
    SUBGOAL_THEN
     `p2b_kfrv (top,atlas) (g:real->B->real^3^3) p t1 =
      p2a_frv (top,atlas) (--(&2 * t2)) (&0) g p t1 /\
      p2b_kfrv (top,atlas) (g:real->B->real^3^3) p t2 =
      p2a_frv (top,atlas) (--(&2 * t2)) (&0) g p t2`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC P2BX_KFRV_VIEW THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "FV" (MP_TAC o SPECL [`--(&2 * t2)`; `t1:real`; `t2:real`]) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `RV:real->real` P2BX_DECREASING_LIMIT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `V = inf {(RV:real->real) t | &0 < t}` THEN STRIP_TAC THEN
  EXISTS_TAC `V:real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(RV:real->real) (&1) = sqrt(&4 * pi) pow 3` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!a v f:real. a <= v /\ v <= f /\ f <= a ==> f = a`) THEN
    EXISTS_TAC `V:real` THEN ASM_SIMP_TAC[REAL_LT_01];
    ALL_TAC] THEN
  EXPAND_TAC "RV" THEN REWRITE_TAC[p2b_kfrv] THEN DISCH_TAC THEN
  USE_THEN "FL5R" (MP_TAC o SPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                                   `--(&2 * &1)`; `&0`; `g:real->B->real^3^3`; `p:B`;
                                   `&1`] o
                   REWRITE_RULE[P2A_FLOW_RV_RIGID_STATEMENT; DIMINDEX_3]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [USE_THEN "CB" MATCH_MP_TAC THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    DISCH_TAC] THEN
  UNDISCH_TAC `p2b_kappa_solution kappa (top,atlas) (g:real->B->real^3^3)` THEN
  REWRITE_TAC[p2b_kappa_solution; p2c_kappa_sol] THEN
  DISCH_THEN(MP_TAC o SPEC `&0` o el 9 o CONJUNCTS) THEN
  REWRITE_TAC[REAL_LE_REFL; NOT_EXISTS_THM] THEN X_GEN_TAC `x:B` THEN
  REWRITE_TAC[REAL_NOT_LT; DE_MORGAN_THM] THEN
  ASM_CASES_TAC `(x:B) IN topspace top` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BX_RM_NORM_FLAT THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

