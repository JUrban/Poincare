(* ========================================================================= *)
(* Top-level interfaces of the Poincare development: the topological form    *)
(* follows from the smooth form and Moise smoothing                          *)
(* (POINCARE_FROM_SMOOTH_AND_MOISE).                                         *)
(*                                                                           *)
(* MOISE_SMOOTHING_STATEMENT: every compact Hausdorff space that is locally  *)
(* Euclidean of dimension 3 admits a smooth atlas (its charts are            *)
(* homeomorphisms for the given topology, so the smooth structure is         *)
(* compatible with it).  This is the only input the classical topological   *)
(* form needs beyond the smooth form.                                        *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;

let MOISE_SMOOTHING_STATEMENT = new_definition
 `MOISE_SMOOTHING_STATEMENT (u:A->bool) <=>
    !top:A topology.
        hausdorff_space top /\ compact_space top /\
        locally_euclidean_space (:3) top
        ==> ?atlas:((A->bool)#(A->real^3))->bool.
                smooth_manifold_atlas top atlas`;;

let POINCARE_FROM_SMOOTH_AND_MOISE = prove
 (`!u:A->bool.
        POINCARE_SMOOTH_STATEMENT u /\ MOISE_SMOOTHING_STATEMENT u
        ==> POINCARE_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[POINCARE_SMOOTH_STATEMENT; MOISE_SMOOTHING_STATEMENT;
              POINCARE_STATEMENT] THEN
  STRIP_TAC THEN X_GEN_TAC `top:A topology` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `top:A topology`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `atlas:((A->bool)#(A->real^3))->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[homeomorphic_space] THEN MESON_TAC[HOMEOMORPHIC_MAP_MAPS]);;
