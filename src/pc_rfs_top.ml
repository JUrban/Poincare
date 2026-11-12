(* ========================================================================= *)
(* Unit pc_rfs_top: the top statements of the Ricci flow with surgery layer  *)
(* and of the topological endgame, as statement constants (each argument     *)
(* only fixes a type): METRIC_EXISTENCE_STATEMENT, RFS_EXTINCTION_STATEMENT, *)
(* EVENT_TOPOLOGY_STATEMENT, RFS_CUTCAP_SC_STATEMENT,                        *)
(* RFS_LISTED_SC_S3_STATEMENT, RFS_SPHERE_SYSTEM_STATEMENT.  From them       *)
(* pc_rfs_assembly proves POINCARE_SMOOTH_STATEMENT.  The cut-and-cap data   *)
(* are mfd_cut_cap of pc_mfd_cut.                                            *)
(* ========================================================================= *)

needs "src/pc_rfs_history.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* T1. Closed smooth manifolds carry Riemannian metrics (partition of unity *)
(* on a finite chart cover).  Any dimension.                                 *)
(* ------------------------------------------------------------------------- *)

let METRIC_EXISTENCE_STATEMENT = new_definition
 `METRIC_EXISTENCE_STATEMENT (u:A->bool) (n:N->bool) <=>
    !top atlas.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^N))->bool) /\
        compact_space top
        ==> ?g. riemannian_metric atlas g`;;

(* ------------------------------------------------------------------------- *)
(* T2. The main analytic theorem (MT Thm 15.9 / Cor 15.10 + Thm 18.1, simply *)
(* connected case): for every eps0 there are eps <= eps0 and C (MT Sec      *)
(* 15.1.1 fixes any eps below its thresholds and C = C(eps)) such that for   *)
(* every bound dl0 on the surgery control, every closed simply connected     *)
(* Riemannian 3-manifold (top,atlas,g0) has, after scaling g0 to a           *)
(* normalized metric q g0, a controlled history on the carrier type          *)
(* A + num#num#real^3 starting at it and becoming extinct.  The parameter    *)
(* functions may depend on (top,atlas,g0) (as in Qin et al.).                *)
(* ------------------------------------------------------------------------- *)

let RFS_EXTINCTION_STATEMENT = new_definition
 `RFS_EXTINCTION_STATEMENT (u:A->bool) <=>
    !eps0. &0 < eps0
      ==> ?C eps. &0 < C /\ &0 < eps /\ eps <= eps0 /\
            !dl0. &0 < dl0
              ==> !top atlas g0.
                    hausdorff_space top /\
                    smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
                    compact_space top /\ ~(topspace top = {}) /\
                    simply_connected_space top /\
                    riemannian_metric atlas g0
                    ==> ?(hs:(A+num#num#real^3)rfs_history) rp dl kp h q iota iota'.
                          &0 < q /\
                          rfs_controlled (C,eps) (rp,dl,kp,h) hs /\
                          (!t. &0 <= t ==> dl t <= dl0) /\
                          rfs_initial (top,atlas) (\x. q %% g0 x) hs iota iota' /\
                          rfs_normalized (hs_top hs 0,hs_atlas hs 0)
                                         (hs_metric hs 0 (&0)) /\
                          rfs_extinct hs`;;

(* ------------------------------------------------------------------------- *)
(* T3. Topology of one surgery event (MT Prop 15.3, in cut-and-cap form):    *)
(* for eps small and the surgery control small relative to (C,eps), if the   *)
(* components of the old stage are simply connected (so every neck sphere    *)
(* separates: the hypothesis of MT Prop A.19), every                         *)
(* discarded component of the capped manifold Z is of one of the listed      *)
(* types (S^3, space form, S^2-bundle over S^1, containing RP^3 minus a      *)
(* point).  Uses only Assumptions (4)-(6) (rfs_surgery_ok).                  *)
(* ------------------------------------------------------------------------- *)

let EVENT_TOPOLOGY_STATEMENT = new_definition
 `EVENT_TOPOLOGY_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps. &0 < C /\ &0 < eps /\ eps <= eps0
        ==> ?dl0. &0 < dl0 /\
              !(hs:(A)rfs_history) rp dl kp h k.
                 rfs_history_ok hs /\ rfs_params (rp,dl,kp,h) /\
                 (!t. &0 <= t ==> dl t <= dl0) /\
                 1 <= k /\ k <= hs_count hs /\
                 rfs_surgery_ok hs C eps dl h k /\
                 rfs_components_sc (hs_top hs (k - 1))
                 ==> !U. U IN connected_components_of (ev_ztop(hs_event hs k)) /\
                         U SUBSET ev_disc(hs_event hs k)
                         ==> rfs_listed_piece
                               (subtopology (ev_ztop(hs_event hs k)) U)
                               (restrict_atlas (ev_zatlas(hs_event hs k)) U)`;;

(* ------------------------------------------------------------------------- *)
(* T4. Endgame, topology of one cut: cutting along finitely many neck        *)
(* spheres and capping keeps all components simply connected (every 2-      *)
(* sphere in a simply connected 3-manifold separates; pinch                  *)
(* maps; loops pushed off the caps).  MT Remark 0.6(ii).                     *)
(* ------------------------------------------------------------------------- *)

let RFS_CUTCAP_SC_STATEMENT = new_definition
 `RFS_CUTCAP_SC_STATEMENT (u:A->bool) (v:B->bool) <=>
    !topX atlasX topZ atlasZ J e cp cm ff gg.
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        compact_space topX /\ rfs_components_sc topX /\
        hausdorff_space topZ /\
        smooth_manifold_atlas topZ (atlasZ:((B->bool)#(B->real^3))->bool) /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg
        ==> rfs_components_sc topZ`;;

(* ------------------------------------------------------------------------- *)
(* T5. Endgame, recognition: a simply connected listed piece is S^3          *)
(* (Killing-Hopf for space forms; S^2-bundles over S^1 and manifolds         *)
(* containing RP^3 minus a point are not simply connected).                  *)
(* ------------------------------------------------------------------------- *)

let RFS_LISTED_SC_S3_STATEMENT = new_definition
 `RFS_LISTED_SC_S3_STATEMENT (u:A->bool) <=>
    !top atlas U.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        compact_space top /\ U IN connected_components_of top /\
        simply_connected_space (subtopology top U) /\
        rfs_listed_piece (subtopology top U) (restrict_atlas atlas U)
        ==> mfd_diffeomorphic (subtopology top U) (restrict_atlas atlas U)
              (subtopology euclidean (sphere(vec 0:real^4,&1))) sphere3_atlas`;;

(* ------------------------------------------------------------------------- *)
(* T6. The componentwise form of the endgame sphere-system statement: X      *)
(* closed with simply connected components (not necessarily connected), cut  *)
(* along neck spheres and capped to Z; if every component of Z is S^3 then   *)
(* every component of X is S^3.  It implies SMT_SPHERE_SYSTEM_STATEMENT      *)
(* (RFS_SPHERE_SYSTEM_IMP_SMT, pc_rfs_sanity) and lets the backward          *)
(* induction run over disconnected stages without splitting an event by      *)
(* components.                                                               *)
(* ------------------------------------------------------------------------- *)

let RFS_SPHERE_SYSTEM_STATEMENT = new_definition
 `RFS_SPHERE_SYSTEM_STATEMENT (u:A->bool) (v:B->bool) <=>
    !topX atlasX topZ atlasZ J e cp cm ff gg.
        hausdorff_space topX /\
        smooth_manifold_atlas topX (atlasX:((A->bool)#(A->real^3))->bool) /\
        compact_space topX /\ rfs_components_sc topX /\
        hausdorff_space topZ /\
        smooth_manifold_atlas topZ (atlasZ:((B->bool)#(B->real^3))->bool) /\
        mfd_cut_cap topX atlasX topZ atlasZ J e cp cm ff gg /\
        rfs_components_s3 topZ atlasZ
        ==> rfs_components_s3 topX atlasX`;;

