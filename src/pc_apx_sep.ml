(* ========================================================================= *)
(* pc_apx_sep: separation of neck spheres (the separation that MT's proof of *)
(* Prop A.19 uses).  S separates p from q when both lie off S and no         *)
(* connected subset of the complement contains both; apx_sphere_sep: every   *)
(* neck-chart sphere separates its two sides (component-relative, metric     *)
(* free, covering every level sphere of every neck).  Statement constants:   *)
(* APX_SC_SPHERE_SEP_STATEMENT (components simply connected ==> spheres      *)
(* separate; proved as SMT_SC_SPHERE_SEP in pc_smt_sep) and the passage to   *)
(* open subsets.  Needs no definition of the pc_rfs units: the simple        *)
(* connectivity of the components is written out (it is rfs_components_sc of *)
(* pc_rfs_history).                                                          *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;
needs "src/pc_mfd_maps.ml";;

prioritize_real();;
type_invention_error := true;;

let apx_separates = new_definition
 `apx_separates (top:A topology) (S:A->bool) (p:A) (q:A) <=>
    p IN topspace top DIFF S /\ q IN topspace top DIFF S /\
    ~(connected_component_of (subtopology top (topspace top DIFF S)) p q)`;;

let apx_sphere_sep = new_definition
 `apx_sphere_sep (top:A topology) (atlas:((A->bool)#(A->real^3))->bool) <=>
    !e. mfd_neck_chart top atlas e
        ==> apx_separates top (IMAGE e (sphere(vec 0,&1)))
                          (e(&3 / &4 % basis 1)) (e(&4 / &3 % basis 1))`;;

(* APX_SC_SPHERE_SEP_STATEMENT (topology layer, shared with                  *)
(* RFS_CUTCAP_SC_STATEMENT): in a smooth 3-manifold whose components are     *)
(* simply connected every neck-chart sphere separates (a loop crossing it    *)
(* once would have winding number one).                                      *)

let APX_SC_SPHERE_SEP_STATEMENT = new_definition
 `APX_SC_SPHERE_SEP_STATEMENT (u:A->bool) <=>
    !top atlas.
        hausdorff_space top /\
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        (!U. U IN connected_components_of top
             ==> simply_connected_space (subtopology top U))
        ==> apx_sphere_sep top atlas`;;

(* Separation passes to open subsets (Omega at a surgery time, the slices    *)
(* of Ch 11 are open subsets of stages).                                     *)

let APX_SEP_OPEN_STATEMENT = new_definition
 `APX_SEP_OPEN_STATEMENT (u:A->bool) <=>
    !top atlas W.
        smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
        apx_sphere_sep top atlas /\ open_in top W
        ==> apx_sphere_sep (subtopology top W) (restrict_atlas atlas W)`;;

let APX_SEPARATES_SYM = prove
 (`!top S p q:A. apx_separates top S p q <=> apx_separates top S q p`,
  REWRITE_TAC[apx_separates] THEN MESON_TAC[CONNECTED_COMPONENT_OF_SYM]);;

