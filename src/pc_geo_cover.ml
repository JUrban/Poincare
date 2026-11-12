(* ========================================================================= *)
(* pc_geo_cover: the covering-space fact used by the Killing-Hopf units, in  *)
(* the form of the geodesics API pc_geo_iface: a local homeomorphism from a  *)
(* compact Hausdorff path-connected space into a Hausdorff simply connected  *)
(* space is injective, and onto when the domain is nonempty.  The general    *)
(* topology is proved in pc_top_cover; this unit only restates its theorem   *)
(* COMPACT_LOCAL_HOMEOMORPHISM_SIMPLY_CONNECTED_BIJECTIVE with the           *)
(* definition local_homeomorphism_map unfolded.                              *)
(* ========================================================================= *)

needs "src/pc_top_cover.ml";;

prioritize_real();;
type_invention_error := true;;

let GEO_LOCAL_HOMEO_SC_BIJECTIVE = prove
 (`!(X:A topology) (Y:B topology) f.
        compact_space X /\ hausdorff_space X /\ path_connected_space X /\
        hausdorff_space Y /\ simply_connected_space Y /\
        continuous_map (X,Y) f /\
        (!x. x IN topspace X
             ==> ?U V. open_in X U /\ x IN U /\ open_in Y V /\
                       homeomorphic_map (subtopology X U,subtopology Y V) f)
        ==> (!x y. x IN topspace X /\ y IN topspace X /\ f x = f y ==> x = y) /\
            (~(topspace X = {}) ==> IMAGE f (topspace X) = topspace Y)`,
  REWRITE_TAC[GSYM local_homeomorphism_map;
              COMPACT_LOCAL_HOMEOMORPHISM_SIMPLY_CONNECTED_BIJECTIVE]);;

