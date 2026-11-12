(* ========================================================================= *)
(* Unit pc_p3e_flowext: the extension of the last slab of a history by Ricci *)
(* flow (MT p. 409: Prop 4.12, Thm 3.11, Thm 4.32) in route form,            *)
(* P3_FLOW_EXTENSION_ROUTE_STATEMENT, with the general tools: locality in    *)
(* time of strong necks and strong canonical neighbourhoods, transfer of the *)
(* surgery clauses to extensions, and P3E_STRUCT_EXTEND (an extension with   *)
(* the same events, rfs_history_ok and pinching keeps p3_struct).            *)
(* ========================================================================= *)

needs "src/pc_p3_route.ml";;
needs "src/pc_p3_assembly.ml";;
needs "src/pc_rf_extend.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Locality in time.  Evolving necks of any length, strong necks and strong  *)
(* canonical neighbourhoods at time t only read the view at times <= t (the  *)
(* evolving neck runs backwards because R > 0), so they are unchanged by     *)
(* truncating the view at any tau > t, in both directions                    *)
(* (RFS_STRONG_CANONICAL_TRUNC of pc_p3_assembly is one direction of the     *)
(* third statement).  P3E_EVNECK_TRUNC treats the general length, as needed  *)
(* for the necks of rescaled length 2 of p3_neck2_ok.                        *)
(* ------------------------------------------------------------------------- *)

let P3E_EVNECK_TRUNC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps x t len e tau.
     t < tau
     ==> (rfs_evolving_neck (rfs_trunc V tau) eps x t len e <=>
          rfs_evolving_neck V eps x t len e)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `eps:real`; `x:A`; `t:real`; `len:real`;
                       `e:real^3->A`; `tau:real`] THEN
  DISCH_TAC THEN
  REWRITE_TAC[rfs_trunc; rfs_evolving_neck; rfs_persists; rfs_close_fam] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `rfs_neck ((TM:real->A topology) t,
                           (AT:real->((A->bool)#(A->real^3))->bool) t)
                          ((G:real->A->real^3^3) t) eps x e` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                                ((G:real->A->real^3^3) t) x`
  ASSUME_TAC THENL [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s <= t ==> s < tau` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s <= &0 ==> t + s / mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                                       ((G:real->A->real^3^3) t) x < tau`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `s / mfd_scalar ((AT:real->((A->bool)#(A->real^3))->bool) t)
                                 ((G:real->A->real^3^3) t) x <= &0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LZERO]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IN_ELIM_THM]);;

let P3E_STRONG_NECK_TRUNC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    eps x t e tau.
     t < tau
     ==> (rfs_strong_neck (rfs_trunc V tau) eps x t e <=> rfs_strong_neck V eps x t e)`,
  SIMP_TAC[rfs_strong_neck; P3E_EVNECK_TRUNC]);;

let P3E_STRONG_CANONICAL_TRUNC = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    C eps x t U tau.
     t < tau
     ==> (rfs_strong_canonical (rfs_trunc V tau) C eps x t U <=>
          rfs_strong_canonical V C eps x t U)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`TM:real->A topology`; `AT:real->((A->bool)#(A->real^3))->bool`;
                       `G:real->A->real^3^3`; `C:real`; `eps:real`; `x:A`; `t:real`;
                       `U:A->bool`; `tau:real`] THEN
  DISCH_TAC THEN
  MP_TAC(GEN `e:real^3->A` (ISPECL
    [`(TM:real->A topology,AT:real->((A->bool)#(A->real^3))->bool,G:real->A->real^3^3)`;
     `eps:real`; `x:A`; `t:real`; `e:real^3->A`; `tau:real`] P3E_STRONG_NECK_TRUNC)) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[rfs_trunc; rfs_strong_canonical] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let P3E_VIEW_TRUNC_AT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^3))->bool)#(real->A->real^3^3))
    tau t.
     t < tau
     ==> rfs_vtop (rfs_trunc V tau) t = rfs_vtop V t /\
         rfs_vatlas (rfs_trunc V tau) t = rfs_vatlas V t /\
         rfs_vmetric (rfs_trunc V tau) t = rfs_vmetric V t /\
         (!y. rfs_vscalar (rfs_trunc V tau) t y = rfs_vscalar V t y)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_trunc; rfs_vtop; rfs_vatlas; rfs_vmetric;
              rfs_vscalar] THEN
  SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* An extension hs' of hs agrees with hs on the stages, times                *)
(* and events up to hs_count hs, its previews of events of hs have the same  *)
(* truncation at the horizon of hs, so the surgery clauses, the evolving     *)
(* necks of rescaled length 2 (p3_neck2_ok), Omega_rho, the caps             *)
(* and the maximality of earlier slabs transfer; P3E_STRUCT_EXTEND: an       *)
(* extension with the same number of events, rfs_history_ok and pinching     *)
(* keeps p3_struct.                                                          *)
(* ------------------------------------------------------------------------- *)

let P3E_EXTENDS_STAGE = prove
 (`!hs hs':(A)rfs_history k.
     rfs_history_ok hs /\ rfs_extends hs hs' /\ 1 <= k /\ k <= hs_count hs
     ==> hs_time hs' k = hs_time hs k /\ hs_time hs' (k - 1) = hs_time hs (k - 1) /\
         hs_top hs' k = hs_top hs k /\ hs_top hs' (k - 1) = hs_top hs (k - 1) /\
         hs_atlas hs' k = hs_atlas hs k /\ hs_atlas hs' (k - 1) = hs_atlas hs (k - 1) /\
         hs_event hs' k = hs_event hs k /\
         hs_metric hs' k (hs_time hs k) = hs_metric hs k (hs_time hs k) /\
         hs_time hs k < rfs_horizon hs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_extends]) THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < hs_time hs (k + 1)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) k < rfs_horizon hs` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_horizon] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `hs_time (hs:(A)rfs_history) (k + 1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RFS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `hs_top (hs':(A)rfs_history)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k - 1` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `hs_top (hs':(A)rfs_history)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_REFL]);;

let P3E_PREVIEW_TRUNC = prove
 (`!hs hs':(A)rfs_history k.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     1 <= k /\ k <= hs_count hs
     ==> rfs_trunc (rfs_preview hs' k) (rfs_horizon hs) =
         rfs_trunc (rfs_preview hs k) (rfs_horizon hs)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_EXTENDS_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[rfs_preview; rfs_trunc; PAIR_EQ; FUN_EQ_THM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `t:real` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `t:real`] RFS_EXTENDS_AT) THEN
  ASM_SIMP_TAC[]);;

let P3E_CANONICAL_EXTEND = prove
 (`!hs hs':(A)rfs_history C eps x t U.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     t < rfs_horizon hs
     ==> (rfs_strong_canonical (rfs_view hs') C eps x t U <=>
          rfs_strong_canonical (rfs_view hs) C eps x t U)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `rfs_horizon (hs:(A)rfs_history)`]
    RFS_EXTENDS_TRUNC) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rfs_view (hs':(A)rfs_history)`; `C:real`; `eps:real`; `x:A`; `t:real`;
                 `U:A->bool`; `rfs_horizon (hs:(A)rfs_history)`] P3E_STRONG_CANONICAL_TRUNC) THEN
  MP_TAC(ISPECL [`rfs_view (hs:(A)rfs_history)`; `C:real`; `eps:real`; `x:A`; `t:real`;
                 `U:A->bool`; `rfs_horizon (hs:(A)rfs_history)`] P3E_STRONG_CANONICAL_TRUNC) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let P3E_PREVIEW_EXTEND = prove
 (`!hs hs':(A)rfs_history k.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     1 <= k /\ k <= hs_count hs
     ==> (!d y e. rfs_strong_neck (rfs_preview hs' k) d y (hs_time hs k) e <=>
                  rfs_strong_neck (rfs_preview hs k) d y (hs_time hs k) e) /\
         (!y. rfs_vscalar (rfs_preview hs' k) (hs_time hs k) y =
              rfs_vscalar (rfs_preview hs k) (hs_time hs k) y) /\
         rfs_vatlas (rfs_preview hs' k) (hs_time hs k) =
         rfs_vatlas (rfs_preview hs k) (hs_time hs k) /\
         rfs_vmetric (rfs_preview hs' k) (hs_time hs k) =
         rfs_vmetric (rfs_preview hs k) (hs_time hs k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_EXTENDS_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_PREVIEW_TRUNC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`rfs_preview (hs':(A)rfs_history) k`; `rfs_horizon (hs:(A)rfs_history)`;
                 `hs_time (hs:(A)rfs_history) k`] P3E_VIEW_TRUNC_AT) THEN
  MP_TAC(ISPECL [`rfs_preview (hs:(A)rfs_history) k`; `rfs_horizon (hs:(A)rfs_history)`;
                 `hs_time (hs:(A)rfs_history) k`] P3E_VIEW_TRUNC_AT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN TRY(ASM_MESON_TAC[]) THEN
  MP_TAC(ISPECL [`rfs_preview (hs':(A)rfs_history) k`; `d:real`; `y:A`;
                 `hs_time (hs:(A)rfs_history) k`; `e:real^3->A`;
                 `rfs_horizon (hs:(A)rfs_history)`] P3E_STRONG_NECK_TRUNC) THEN
  MP_TAC(ISPECL [`rfs_preview (hs:(A)rfs_history) k`; `d:real`; `y:A`;
                 `hs_time (hs:(A)rfs_history) k`; `e:real^3->A`;
                 `rfs_horizon (hs:(A)rfs_history)`] P3E_STRONG_NECK_TRUNC) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let P3E_PREVIEW_EVNECK_EXTEND = prove
 (`!hs hs':(A)rfs_history k.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     1 <= k /\ k <= hs_count hs
     ==> !d y len e.
           rfs_evolving_neck (rfs_preview hs' k) d y (hs_time hs k) len e <=>
           rfs_evolving_neck (rfs_preview hs k) d y (hs_time hs k) len e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_EXTENDS_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_PREVIEW_TRUNC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`d:real`; `y:A`; `len:real`; `e:real^3->A`] THEN
  MP_TAC(ISPECL [`rfs_preview (hs':(A)rfs_history) k`; `d:real`; `y:A`;
                 `hs_time (hs:(A)rfs_history) k`; `len:real`; `e:real^3->A`;
                 `rfs_horizon (hs:(A)rfs_history)`] P3E_EVNECK_TRUNC) THEN
  MP_TAC(ISPECL [`rfs_preview (hs:(A)rfs_history) k`; `d:real`; `y:A`;
                 `hs_time (hs:(A)rfs_history) k`; `len:real`; `e:real^3->A`;
                 `rfs_horizon (hs:(A)rfs_history)`] P3E_EVNECK_TRUNC) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let P3E_SURGERY_OK_EXTEND = prove
 (`!hs hs':(A)rfs_history C eps dl h k.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     1 <= k /\ k <= hs_count hs
     ==> (rfs_surgery_ok hs' C eps dl h k <=> rfs_surgery_ok hs C eps dl h k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_EXTENDS_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_PREVIEW_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x t U. t < hs_time (hs:(A)rfs_history) k
            ==> (rfs_strong_canonical (rfs_view (hs':(A)rfs_history)) C eps x t U <=>
                 rfs_strong_canonical (rfs_view hs) C eps x t U)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC P3E_CANONICAL_EXTEND THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_surgery_ok] THEN ASM_SIMP_TAC[]);;

let P3E_OMEGA_RHO_EXTEND = prove
 (`!hs hs':(A)rfs_history rp dl k.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     1 <= k /\ k <= hs_count hs
     ==> (p3_omega_rho_ok hs' (rp,dl) k <=> p3_omega_rho_ok hs (rp,dl) k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_EXTENDS_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_PREVIEW_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3_omega_rho_ok] THEN ASM_REWRITE_TAC[]);;

let P3E_CAP_OK_EXTEND = prove
 (`!hs hs':(A)rfs_history md g0 A0 dl h k i.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     1 <= k /\ k <= hs_count hs
     ==> (p3_cap_ok (md,g0,A0) (dl,h) hs' k i <=> p3_cap_ok (md,g0,A0) (dl,h) hs k i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_EXTENDS_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_PREVIEW_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p3_cap_ok; p3_cap_param] THEN ASM_REWRITE_TAC[]);;

let P3E_NECK2_EXTEND = prove
 (`!hs hs':(A)rfs_history dl h k.
     rfs_history_ok hs /\ rfs_history_ok hs' /\ rfs_extends hs hs' /\
     1 <= k /\ k <= hs_count hs
     ==> (p3_neck2_ok (dl,h) hs' k <=> p3_neck2_ok (dl,h) hs k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_EXTENDS_STAGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_PREVIEW_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`]
    P3E_PREVIEW_EVNECK_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[p3_neck2_ok] THEN ASM_REWRITE_TAC[]);;

let P3E_SLAB_MAXIMAL_EXTEND = prove
 (`!hs hs':(A)rfs_history k.
     rfs_history_ok hs /\ rfs_extends hs hs' /\ k < hs_count hs
     ==> (rfs_slab_maximal hs' k <=> rfs_slab_maximal hs k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_extends]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `hs_top (hs':(A)rfs_history)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `k + 1` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `hs_top (hs':(A)rfs_history)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  REWRITE_TAC[rfs_slab_maximal] THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `B:real` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) o
    SPEC `B:real`) THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `x:A`] THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[]);;

let P3E_STRUCT_EXTEND = prove
 (`!C eps hf md g0 A0 rp dl (hs:(A)rfs_history) hs'.
     p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\ rfs_history_ok hs' /\
     rfs_extends hs hs' /\ hs_count hs' = hs_count hs /\ rfs_pinched (rfs_view hs')
     ==> p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p3_struct] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`] RFS_EXTENDS_INITIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_extends]) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `hs_top (hs':(A)rfs_history)`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `dl:real->real`;
                   `p3_hscale hf rp dl`; `k:num`] P3E_NECK2_EXTEND) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`] P3E_EXTENDS_STAGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[P3E_SURGERY_OK_EXTEND; P3E_OMEGA_RHO_EXTEND; P3E_CAP_OK_EXTEND];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `k:num`]
      P3E_SLAB_MAXIMAL_EXTEND) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The history whose last slab is replaced by a longer flow G'               *)
(* (equal to the old slab metric before the old horizon): fields,          *)
(* rfs_history_ok, rfs_extends and the view on [old horizon, new horizon). *)
(* ------------------------------------------------------------------------- *)

let P3E_EVENT_OK_CONG = prove
 (`!X (gX:real->A->real^3^3) ts Y gY gY' (ev:(A)rfs_event).
     gY' ts = gY ts
     ==> (rfs_event_ok X gX ts Y gY' ev <=> rfs_event_ok X gX ts Y gY ev)`,
  REWRITE_TAC[FORALL_PAIR_THM; rfs_event_ok] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let P3E_HIST_EXTEND = prove
 (`!(hs:(A)rfs_history) hs' G' T'.
     rfs_history_ok hs /\ rfs_horizon hs < T' /\
     ricci_flow_from (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                     (hs_time hs (hs_count hs)) T' G' /\
     (!t. t < rfs_horizon hs ==> G' t = hs_metric hs (hs_count hs) t) /\
     hs' = RfsHistory (hs_count hs)
             (\k. if k = hs_count hs + 1 then T' else hs_time hs k)
             (hs_top hs) (hs_atlas hs)
             (\k. if k = hs_count hs then G' else hs_metric hs k)
             (hs_event hs)
     ==> rfs_history_ok hs' /\ rfs_extends hs hs' /\ hs_count hs' = hs_count hs /\
         rfs_horizon hs' = T' /\
         (!k. k <= hs_count hs ==> hs_time hs' k = hs_time hs k) /\
         (!k. hs_top hs' k = hs_top hs k) /\ (!k. hs_atlas hs' k = hs_atlas hs k) /\
         hs_metric hs' (hs_count hs) = G' /\
         (!t. rfs_horizon hs <= t /\ t < T'
              ==> rfs_top_at hs' t = hs_top hs (hs_count hs) /\
                  rfs_atlas_at hs' t = hs_atlas hs (hs_count hs) /\
                  rfs_metric_at hs' t = G' t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
  ABBREV_TAC `n = hs_count (hs:(A)rfs_history)` THEN
  SUBGOAL_THEN `rfs_horizon (hs:(A)rfs_history) = hs_time hs (n + 1)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[rfs_horizon]; ALL_TAC] THEN
  SUBGOAL_THEN `hs_time (hs:(A)rfs_history) n < rfs_horizon hs` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `(<):real->real->bool`)) (concl th) &&
      not (can (find_term ((=) `rfs_horizon:(A)rfs_history->real`)) (concl th)))) THEN
    REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hs_count (hs':(A)rfs_history) = n /\
    (!k. hs_time hs' k = if k = n + 1 then T' else hs_time (hs:(A)rfs_history) k) /\
    (!k. hs_top hs' k = hs_top hs k) /\ (!k. hs_atlas hs' k = hs_atlas hs k) /\
    (!k. hs_metric hs' k = if k = n then G' else hs_metric hs k) /\
    (!k. hs_event hs' k = hs_event hs k)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[hs_count; hs_time; hs_top; hs_atlas; hs_metric; hs_event];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `hs':(A)rfs_history`)) THEN
  SUBGOAL_THEN `rfs_horizon (hs':(A)rfs_history) = T'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[rfs_horizon]; ALL_TAC] THEN
  SUBGOAL_THEN `rfs_history_ok (hs':(A)rfs_history)` ASSUME_TAC THENL
   [REWRITE_TAC[rfs_history_ok] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `~(0 = n + 1)`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = n + 1)`; EQ_ADD_RCANCEL] THEN
      COND_CASES_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `(<):real->real->bool`)) (concl th) &&
          not (can (find_term ((=) `rfs_horizon:(A)rfs_history->real`)) (concl th)))) THEN
        ASM_REWRITE_TAC[]];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `hausdorff_space:A topology->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = n + 1)`; EQ_ADD_RCANCEL] THEN
      ASM_CASES_TAC `k:num = n` THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun tm -> is_const tm && fst(dest_const tm) = "rfs_event_ok"))
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= k /\ k <= n ==> ~(k - 1 = n + 1) /\ ~(k = n + 1)`;
                   ARITH_RULE `1 <= k /\ k <= n ==> ~(k - 1 = n)`] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC(TAUT `(a <=> b) ==> b ==> a`) THEN
      MATCH_MP_TAC P3E_EVENT_OK_CONG THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!k. k <= n ==> hs_time (hs':(A)rfs_history) k = hs_time (hs:(A)rfs_history) k`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = n + 1)`]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[rfs_extends] THEN ASM_REWRITE_TAC[LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = n + 1)`] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [SIMP_TAC[ARITH_RULE `k <= n ==> ~(k = n + 1)`]; ALL_TAC] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= hs_time (hs:(A)rfs_history) n` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `hs_time (hs:(A)rfs_history) 0 = &0`)) THEN
    MATCH_MP_TAC RFS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rfs_slab (hs':(A)rfs_history) t = n` ASSUME_TAC THENL
   [MATCH_MP_TAC RFS_SLAB_UNIQUE THEN
    ASM_SIMP_TAC[LE_REFL; ARITH_RULE `~(n = n + 1)`] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rfs_top_at; rfs_atlas_at; rfs_metric_at; rfs_live] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= t` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The extension of the last slab (MT p. 409) in route form.                 *)
(* The maximal flow G from the slab metric at the slab time agrees with the  *)
(* slab before the horizon (uniqueness); it lives past the horizon because   *)
(* the slab curvature is bounded; the new horizon T' is Tb or the maximal   *)
(* time; G' glues the old slab metric before the horizon to G.              *)
(* ------------------------------------------------------------------------- *)

let P3E_FLOW_EXTENSION_ROUTE = prove
 (`!(u:A->bool). P3_FLOW_EXTENSION_ROUTE_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[P3_FLOW_EXTENSION_ROUTE_STATEMENT; P3_FLOW_EXTENSION_STATEMENT] THEN
  REWRITE_TAC[PDE_MAXIMAL_FLOW_STATEMENT; PDE_UNIQUENESS_STATEMENT;
              P2_THM_4_32_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "max")
    (CONJUNCTS_THEN2 (LABEL_TAC "uniq") (LABEL_TAC "pinch"))) THEN
  MAP_EVERY X_GEN_TAC [`C:real`; `eps:real`; `hf:real->real->real`; `md:real->real`;
                       `g0:real^3->real^3^3`; `A0:real`; `rp:real->real`;
                       `dl:real->real`; `hs:(A)rfs_history`; `Tb:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `rfs_history_ok (hs:(A)rfs_history) /\ rfs_pinched (rfs_view hs)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[p3_struct]; ALL_TAC] THEN
  SUBGOAL_THEN
   `hausdorff_space (hs_top (hs:(A)rfs_history) (hs_count hs)) /\
    smooth_manifold_atlas (hs_top hs (hs_count hs)) (hs_atlas hs (hs_count hs)) /\
    compact_space (hs_top hs (hs_count hs)) /\
    ricci_flow_from (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                    (hs_time hs (hs_count hs)) (rfs_horizon hs) (hs_metric hs (hs_count hs))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN
    REWRITE_TAC[rfs_history_ok; rfs_horizon] THEN MESON_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= hs_time (hs:(A)rfs_history) (hs_count hs) /\
                hs_time hs (hs_count hs) < rfs_horizon hs`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT1 o GEN_REWRITE_RULE I [rfs_history_ok]) THEN
      MATCH_MP_TAC RFS_TIME_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      UNDISCH_TAC `rfs_history_ok (hs:(A)rfs_history)` THEN
      REWRITE_TAC[rfs_history_ok; rfs_horizon] THEN MESON_TAC[LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `riemannian_metric (hs_atlas (hs:(A)rfs_history) (hs_count hs))
                      (hs_metric hs (hs_count hs) (hs_time hs (hs_count hs)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `ricci_flow_from (hs_top (hs:(A)rfs_history) (hs_count hs),
                                  hs_atlas hs (hs_count hs))
                   (hs_time hs (hs_count hs)) (rfs_horizon hs) (hs_metric hs (hs_count hs))` THEN
    SIMP_TAC[ricci_flow_from];
    ALL_TAC] THEN
  (* the bound of the last slab *)
  UNDISCH_TAC `~rfs_slab_maximal (hs:(A)rfs_history) (hs_count hs)` THEN
  REWRITE_TAC[rfs_slab_maximal; NOT_FORALL_THM; NOT_EXISTS_THM; GSYM rfs_horizon] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` MP_TAC) THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c /\ d) <=> a /\ b /\ c ==> ~d`; REAL_NOT_LT] THEN
  DISCH_THEN(LABEL_TAC "bd") THEN
  (* the maximal flow *)
  REMOVE_THEN "max" (MP_TAC o SPECL
    [`hs_top (hs:(A)rfs_history) (hs_count hs)`; `hs_atlas (hs:(A)rfs_history) (hs_count hs)`;
     `hs_metric (hs:(A)rfs_history) (hs_count hs) (hs_time hs (hs_count hs))`;
     `hs_time (hs:(A)rfs_history) (hs_count hs)`]) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real->A->real^3^3` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN
   `!b. ricci_flow_from (hs_top (hs:(A)rfs_history) (hs_count hs),hs_atlas hs (hs_count hs))
                        (hs_time hs (hs_count hs)) b G
        ==> !t x. hs_time hs (hs_count hs) <= t /\ t < rfs_horizon hs /\ t < b /\
                  x IN topspace (hs_top hs (hs_count hs))
                  ==> G t x = hs_metric hs (hs_count hs) t x`
  (LABEL_TAC "agree") THENL
   [X_GEN_TAC `b:real` THEN DISCH_TAC THEN
    USE_THEN "uniq" (MP_TAC o SPECL
      [`hs_top (hs:(A)rfs_history) (hs_count hs)`; `hs_atlas (hs:(A)rfs_history) (hs_count hs)`;
       `hs_time (hs:(A)rfs_history) (hs_count hs)`; `rfs_horizon (hs:(A)rfs_history)`;
       `b:real`; `hs_metric (hs:(A)rfs_history) (hs_count hs)`; `G:real->A->real^3^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the new horizon *)
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?T'. rfs_horizon (hs:(A)rfs_history) < T' /\ T' <= Tb /\
         ricci_flow_from (hs_top hs (hs_count hs),hs_atlas hs (hs_count hs))
                         (hs_time hs (hs_count hs)) T' G /\
         (T' = Tb \/
          !B. ?t x. hs_time hs (hs_count hs) <= t /\ t < T' /\
                    x IN topspace (hs_top hs (hs_count hs)) /\
                    B < mfd_rm_norm (hs_atlas hs (hs_count hs)) (G t) x)`
  (X_CHOOSE_THEN `T':real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 (LABEL_TAC "all")
      (X_CHOOSE_THEN `bm:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unb"))))) THENL
     [EXISTS_TAC `Tb:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      USE_THEN "all" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `Tb < bm` THENL
     [EXISTS_TAC `Tb:real` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC PDE_RFF_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`hs_time (hs:(A)rfs_history) (hs_count hs)`; `bm:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `bm:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    USE_THEN "unb" (X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) o
      SPEC `B:real`) THEN
    SUBGOAL_THEN
     `mfd_rm_norm (hs_atlas (hs:(A)rfs_history) (hs_count hs)) ((G:real->A->real^3^3) t) x =
      mfd_rm_norm (hs_atlas hs (hs_count hs)) (hs_metric hs (hs_count hs) t) x`
    MP_TAC THENL
     [MATCH_MP_TAC PDE_MFD_RM_NORM_CONG THEN
      EXISTS_TAC `hs_top (hs:(A)rfs_history) (hs_count hs)` THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN USE_THEN "agree" (MP_TAC o SPEC `bm:real`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "bd" (MP_TAC o SPECL [`t:real`; `x:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the glued flow *)
  ABBREV_TAC `G' = \t. if t < rfs_horizon (hs:(A)rfs_history)
                       then hs_metric hs (hs_count hs) t else (G:real->A->real^3^3) t` THEN
  SUBGOAL_THEN `!t. t < rfs_horizon (hs:(A)rfs_history)
                    ==> (G':real->A->real^3^3) t = hs_metric hs (hs_count hs) t`
  ASSUME_TAC THENL [EXPAND_TAC "G'" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t x. hs_time (hs:(A)rfs_history) (hs_count hs) <= t /\ t < T' /\
          x IN topspace (hs_top hs (hs_count hs))
          ==> (G':real->A->real^3^3) t x = G t x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "G'" THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "agree" (MP_TAC o SPEC `T':real`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ricci_flow_from (hs_top (hs:(A)rfs_history) (hs_count hs),hs_atlas hs (hs_count hs))
                    (hs_time hs (hs_count hs)) T' G'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PDE_RFF_CONG THEN EXISTS_TAC `G:real->A->real^3^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the extended history *)
  ABBREV_TAC `hs' = RfsHistory (hs_count (hs:(A)rfs_history))
                      (\k. if k = hs_count hs + 1 then T' else hs_time hs k)
                      (hs_top hs) (hs_atlas hs)
                      (\k. if k = hs_count hs then G' else hs_metric hs k)
                      (hs_event hs)` THEN
  MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `G':real->A->real^3^3`;
                 `T':real`] P3E_HIST_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `hs':(A)rfs_history` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* T' = Tb or the new slab is maximal *)
    FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (fun th -> is_disj(concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
    REWRITE_TAC[rfs_slab_maximal] THEN
    SUBGOAL_THEN `hs_time (hs':(A)rfs_history) (hs_count (hs:(A)rfs_history)) =
                  hs_time hs (hs_count hs) /\
                  hs_time hs' (hs_count hs + 1) = T'`
    (fun th -> REWRITE_TAC[th]) THENL
     [ASM_SIMP_TAC[LE_REFL] THEN
      UNDISCH_TAC `rfs_horizon (hs':(A)rfs_history) = T'` THEN
      ASM_REWRITE_TAC[rfs_horizon];
      ALL_TAC] THEN
    X_GEN_TAC `B':real` THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) o
      SPEC `B':real`) THEN
    MAP_EVERY EXISTS_TAC [`t:real`; `x:A`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `mfd_rm_norm (hs_atlas (hs:(A)rfs_history) (hs_count hs)) ((G':real->A->real^3^3) t) x =
      mfd_rm_norm (hs_atlas hs (hs_count hs)) (G t) x`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC PDE_MFD_RM_NORM_CONG THEN
    EXISTS_TAC `hs_top (hs:(A)rfs_history) (hs_count hs)` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* p3_struct of the extension *)
  MATCH_MP_TAC P3E_STRUCT_EXTEND THEN EXISTS_TAC `hs:(A)rfs_history` THEN
  ASM_REWRITE_TAC[rfs_pinched; rfs_view] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `x:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `t < rfs_horizon (hs:(A)rfs_history)` THENL
   [MP_TAC(ISPECL [`hs:(A)rfs_history`; `hs':(A)rfs_history`; `t:real`] RFS_EXTENDS_AT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:A) IN topspace (rfs_top_at (hs':(A)rfs_history) t)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
    REWRITE_TAC[rfs_pinched; rfs_view] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `t < T'` THENL
   [ALL_TAC;
    UNDISCH_TAC `(x:A) IN topspace (rfs_top_at (hs':(A)rfs_history) t)` THEN
    REWRITE_TAC[rfs_top_at; rfs_live] THEN
    SUBGOAL_THEN `hs_time (hs':(A)rfs_history) (hs_count hs' + 1) = T'` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM rfs_horizon]; ALL_TAC] THEN
    ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; NOT_IN_EMPTY]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:real` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `rfs_top_at (hs':(A)rfs_history)`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  UNDISCH_TAC `(x:A) IN topspace (rfs_top_at (hs':(A)rfs_history) t)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "pinch" (MP_TAC o SPECL
    [`hs_top (hs:(A)rfs_history) (hs_count hs)`; `hs_atlas (hs:(A)rfs_history) (hs_count hs)`;
     `hs_time (hs:(A)rfs_history) (hs_count hs)`; `T':real`; `G':real->A->real^3^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(G':real->A->real^3^3) (hs_time (hs:(A)rfs_history) (hs_count hs)) =
                  hs_metric hs (hs_count hs) (hs_time hs (hs_count hs))`
    SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `rfs_slab (hs:(A)rfs_history) (hs_time hs (hs_count hs)) = hs_count hs`
    ASSUME_TAC THENL
     [MATCH_MP_TAC RFS_SLAB_UNIQUE THEN ASM_REWRITE_TAC[LE_REFL; REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[GSYM rfs_horizon];
      ALL_TAC] THEN
    UNDISCH_TAC `rfs_pinched (rfs_view (hs:(A)rfs_history))` THEN
    REWRITE_TAC[rfs_pinched; rfs_view; rfs_top_at; rfs_atlas_at; rfs_metric_at; rfs_live] THEN
    DISCH_THEN(MP_TAC o SPECL [`hs_time (hs:(A)rfs_history) (hs_count hs)`; `y:A`]) THEN
    ASM_REWRITE_TAC[GSYM rfs_horizon];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

