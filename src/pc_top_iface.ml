(* ========================================================================= *)
(* pc_top_iface: definitions and statement constants of the algebraic        *)
(* topology part. Homological orientations of topological manifolds          *)
(* (Hatcher, Algebraic Topology, Sec 3.3) and the statement constants of the *)
(* results on general spaces (G) and on topological manifolds (M). Depends   *)
(* only on the HOL Light library and poincare_statement.ml                   *)
(* (locally_euclidean_space, simply_connected_space). The two statements     *)
(* specific to Part 4 (S1, S2) are in pc_top_smooth.ml.                      *)
(*                                                                           *)
(* Labels used in the comments of the pc_top files:                          *)
(*   G1 ATOP_RELATIVE_MV_STATEMENT                                           *)
(*   G2 ATOP_EUCLIDEAN_LOCAL_HOMOLOGY_STATEMENT                              *)
(*   G3 ATOP_DEGREE_ONE_LOCAL_STATEMENT                                      *)
(*   G4 ATOP_HUREWICZ2_STATEMENT                                             *)
(*   G5 ATOP_S3_HOMOLOGY_STATEMENT                                           *)
(*   G6 ATOP_MAYER_VIETORIS_STATEMENT                                        *)
(*   G7 ATOP_HUREWICZ1_STATEMENT                                             *)
(*   M1 ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT                                *)
(*   M2 ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT                               *)
(*   M3 ATOP_FUNDAMENTAL_CLASS_STATEMENT and                                 *)
(*      ATOP_TOP_HOMOLOGY_INJECTIVE_STATEMENT                                *)
(*   M4 ATOP_SC_ORIENTABLE_STATEMENT                                         *)
(*   M5 ATOP_PUNCTURED_SIMPLY_CONNECTED_STATEMENT                            *)
(*   M6 ATOP_NULL_SPHERE_STATEMENT                                           *)
(*   M7 ATOP_S3_FROM_NULL_SPHERE_STATEMENT                                   *)
(*   S1 ATOP_SWEEPOUT_SMOOTHING_STATEMENT                                    *)
(*   S2 ATOP_SUSPENSION_STATEMENT                                            *)
(* ========================================================================= *)

needs "src/poincare_statement.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

let homology_local_orientation = new_definition
 `homology_local_orientation n (top:A topology) x a <=>
    a IN group_carrier(relative_homology_group(&n,top,topspace top DELETE x)) /\
    subgroup_generated (relative_homology_group(&n,top,topspace top DELETE x)) {a} =
    relative_homology_group(&n,top,topspace top DELETE x)`;;

let homology_orientation = new_definition
 `homology_orientation n (top:A topology) mu <=>
    (!x. x IN topspace top ==> homology_local_orientation n top x (mu x)) /\
    (!x. x IN topspace top
         ==> ?w b. open_in top w /\ x IN w /\
                   b IN group_carrier
                          (relative_homology_group(&n,top,topspace top DIFF w)) /\
                   !y. y IN w
                       ==> hom_induced (&n) (top,topspace top DIFF w)
                                       (top,topspace top DELETE y) (\x. x) b = mu y)`;;

let homology_orientable = new_definition
 `homology_orientable n (top:A topology) <=> ?mu. homology_orientation n top mu`;;

(* ------------------------------------------------------------------------- *)
(* Statement constants (each argument only fixes a type).                    *)
(* ------------------------------------------------------------------------- *)

let ATOP_RELATIVE_MV_STATEMENT = new_definition
 `ATOP_RELATIVE_MV_STATEMENT (u:A->bool) <=>
    !p top s t:A->bool.
        open_in top s /\ open_in top t
        ==> (trivial_group(relative_homology_group(p + &1,top,s UNION t))
             ==> !a. a IN group_carrier(relative_homology_group(p,top,s INTER t)) /\
                     hom_induced p (top,s INTER t) (top,s) (\x. x) a =
                     group_id(relative_homology_group(p,top,s)) /\
                     hom_induced p (top,s INTER t) (top,t) (\x. x) a =
                     group_id(relative_homology_group(p,top,t))
                     ==> a = group_id(relative_homology_group(p,top,s INTER t))) /\
            (!a b. a IN group_carrier(relative_homology_group(p,top,s)) /\
                   b IN group_carrier(relative_homology_group(p,top,t)) /\
                   hom_induced p (top,s) (top,s UNION t) (\x. x) a =
                   hom_induced p (top,t) (top,s UNION t) (\x. x) b
                   ==> ?c. c IN group_carrier(relative_homology_group(p,top,s INTER t)) /\
                           hom_induced p (top,s INTER t) (top,s) (\x. x) c = a /\
                           hom_induced p (top,s INTER t) (top,t) (\x. x) c = b)`;;

let ATOP_EUCLIDEAN_LOCAL_HOMOLOGY_STATEMENT = new_definition
 `ATOP_EUCLIDEAN_LOCAL_HOMOLOGY_STATEMENT (v:N->bool) <=>
    (!p x:real^N.
        ~(p = &(dimindex(:N)))
        ==> trivial_group(relative_homology_group(p,euclidean,(:real^N) DELETE x))) /\
    (!x:real^N.
        relative_homology_group(&(dimindex(:N)),euclidean,(:real^N) DELETE x)
        isomorphic_group integer_group) /\
    (!p k x:real^N.
        compact k /\ convex k /\ x IN k
        ==> group_isomorphism
              (relative_homology_group(p,euclidean,(:real^N) DIFF k),
               relative_homology_group(p,euclidean,(:real^N) DELETE x))
              (hom_induced p (euclidean,(:real^N) DIFF k)
                             (euclidean,(:real^N) DELETE x) (\x. x)))`;;

let ATOP_DEGREE_ONE_LOCAL_STATEMENT = new_definition
 `ATOP_DEGREE_ONE_LOCAL_STATEMENT (u:A->bool) (v:B->bool) <=>
    !p top top' (f:A->B) w x.
        t1_space top /\ t1_space top' /\
        continuous_map (top,top') f /\
        open_in top w /\ open_in top' (IMAGE f w) /\
        homeomorphic_map (subtopology top w,subtopology top' (IMAGE f w)) f /\
        (!y. y IN topspace top /\ f y IN IMAGE f w ==> y IN w) /\ x IN w
        ==> group_isomorphism
              (relative_homology_group(p,top,topspace top DELETE x),
               relative_homology_group(p,top',topspace top' DELETE f x))
              (hom_induced p (top,topspace top DELETE x)
                             (top',topspace top' DELETE f x) f)`;;

let ATOP_HUREWICZ2_STATEMENT = new_definition
 `ATOP_HUREWICZ2_STATEMENT (u:A->bool) <=>
    !top:A topology f.
        simply_connected_space top /\
        continuous_map (subtopology euclidean (sphere(vec 0:real^3,&1)),top) f /\
        (!z. z IN group_carrier
                    (homology_group(&2,subtopology euclidean (sphere(vec 0:real^3,&1))))
             ==> hom_induced (&2) (subtopology euclidean (sphere(vec 0:real^3,&1)),{})
                                  (top,{}) f z =
                 group_id(homology_group(&2,top)))
        ==> ?a. homotopic_with (\h. T)
                  (subtopology euclidean (sphere(vec 0:real^3,&1)),top) f (\x. a)`;;

let ATOP_S3_HOMOLOGY_STATEMENT = new_definition
 `ATOP_S3_HOMOLOGY_STATEMENT <=>
    ~trivial_group(homology_group(&3,subtopology euclidean (sphere(vec 0:real^4,&1))))`;;

let ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT = new_definition
 `ATOP_LOCAL_HOMOLOGY_COMPACT_STATEMENT (u:A->bool) (v:N->bool) <=>
    !top:A topology k.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ compact_in top k
        ==> (!p. &(dimindex(:N)) < p
                 ==> trivial_group(relative_homology_group(p,top,topspace top DIFF k))) /\
            (!a. a IN group_carrier(relative_homology_group
                                      (&(dimindex(:N)),top,topspace top DIFF k)) /\
                 (!x. x IN k
                      ==> hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                                      (top,topspace top DELETE x) (\x. x) a =
                          group_id(relative_homology_group
                                     (&(dimindex(:N)),top,topspace top DELETE x)))
                 ==> a = group_id(relative_homology_group
                                    (&(dimindex(:N)),top,topspace top DIFF k))) /\
            (!mu. (!x. x IN k
                       ==> ?w b. open_in top w /\ x IN w /\
                                 b IN group_carrier(relative_homology_group
                                        (&(dimindex(:N)),top,topspace top DIFF w)) /\
                                 !y. y IN w INTER k
                                     ==> hom_induced (&(dimindex(:N)))
                                           (top,topspace top DIFF w)
                                           (top,topspace top DELETE y) (\x. x) b = mu y)
                  ==> ?a. a IN group_carrier(relative_homology_group
                                   (&(dimindex(:N)),top,topspace top DIFF k)) /\
                          !x. x IN k
                              ==> hom_induced (&(dimindex(:N))) (top,topspace top DIFF k)
                                     (top,topspace top DELETE x) (\x. x) a = mu x)`;;

let ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT = new_definition
 `ATOP_MANIFOLD_LOCAL_HOMOLOGY_STATEMENT (u:A->bool) (v:N->bool) <=>
    !top:A topology x.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ x IN topspace top
        ==> (!p. ~(p = &(dimindex(:N)))
                 ==> trivial_group(relative_homology_group(p,top,topspace top DELETE x))) /\
            relative_homology_group(&(dimindex(:N)),top,topspace top DELETE x)
            isomorphic_group integer_group /\
            ?w k. open_in top w /\ x IN w /\ w SUBSET k /\ compact_in top k /\
                  !p y. y IN k
                        ==> group_isomorphism
                              (relative_homology_group(p,top,topspace top DIFF k),
                               relative_homology_group(p,top,topspace top DELETE y))
                              (hom_induced p (top,topspace top DIFF k)
                                             (top,topspace top DELETE y) (\x. x))`;;

let ATOP_FUNDAMENTAL_CLASS_STATEMENT = new_definition
 `ATOP_FUNDAMENTAL_CLASS_STATEMENT (u:A->bool) (v:N->bool) <=>
    !top:A topology mu.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ compact_space top /\
        homology_orientation (dimindex(:N)) top mu
        ==> ?c. c IN group_carrier(homology_group(&(dimindex(:N)),top)) /\
                !x. x IN topspace top
                    ==> hom_induced (&(dimindex(:N))) (top,{})
                                    (top,topspace top DELETE x) (\x. x) c = mu x`;;

let ATOP_TOP_HOMOLOGY_INJECTIVE_STATEMENT = new_definition
 `ATOP_TOP_HOMOLOGY_INJECTIVE_STATEMENT (u:A->bool) (v:N->bool) <=>
    !top:A topology x.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\ compact_space top /\
        connected_space top /\ x IN topspace top
        ==> group_monomorphism
              (homology_group(&(dimindex(:N)),top),
               relative_homology_group(&(dimindex(:N)),top,topspace top DELETE x))
              (hom_induced (&(dimindex(:N))) (top,{})
                           (top,topspace top DELETE x) (\x. x))`;;

let ATOP_SC_ORIENTABLE_STATEMENT = new_definition
 `ATOP_SC_ORIENTABLE_STATEMENT (u:A->bool) (v:N->bool) <=>
    !top:A topology.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        simply_connected_space top
        ==> homology_orientable (dimindex(:N)) top`;;

let ATOP_PUNCTURED_SIMPLY_CONNECTED_STATEMENT = new_definition
 `ATOP_PUNCTURED_SIMPLY_CONNECTED_STATEMENT (u:A->bool) (v:N->bool) <=>
    !top:A topology x.
        hausdorff_space top /\ locally_euclidean_space (:N) top /\
        3 <= dimindex(:N) /\ simply_connected_space top /\ x IN topspace top
        ==> simply_connected_space (subtopology top (topspace top DELETE x))`;;

let ATOP_NULL_SPHERE_STATEMENT = new_definition
 `ATOP_NULL_SPHERE_STATEMENT (u:A->bool) <=>
    !top:A topology w (e:real^3->A).
        hausdorff_space top /\ locally_euclidean_space (:3) top /\ compact_space top /\
        simply_connected_space top /\ homology_orientable 3 top /\
        open_in top w /\ homeomorphic_map (euclidean,subtopology top w) e
        ==> ?a. homotopic_with (\h. T)
                  (subtopology euclidean (sphere(vec 0:real^3,&1)),
                   subtopology top (topspace top DIFF IMAGE e (ball(vec 0,&1))))
                  e (\x. a)`;;

let ATOP_S3_FROM_NULL_SPHERE_STATEMENT = new_definition
 `ATOP_S3_FROM_NULL_SPHERE_STATEMENT (u:A->bool) <=>
    !top:A topology w (e:real^3->A) a.
        hausdorff_space top /\
        open_in top w /\ homeomorphic_map (euclidean,subtopology top w) e /\
        homotopic_with (\h. T)
          (subtopology euclidean (sphere(vec 0:real^3,&1)),
           subtopology top (topspace top DIFF IMAGE e (ball(vec 0,&1))))
          e (\x. a)
        ==> ?f v. continuous_map
                    (subtopology euclidean (sphere(vec 0:real^4,&1)),top) f /\
                  open_in (subtopology euclidean (sphere(vec 0:real^4,&1))) v /\
                  ~(v = {}) /\ open_in top (IMAGE f v) /\
                  homeomorphic_map
                    (subtopology (subtopology euclidean (sphere(vec 0:real^4,&1))) v,
                     subtopology top (IMAGE f v)) f /\
                  !y. y IN sphere(vec 0,&1) /\ f y IN IMAGE f v ==> y IN v`;;

let ATOP_MAYER_VIETORIS_STATEMENT = new_definition
 `ATOP_MAYER_VIETORIS_STATEMENT (u:A->bool) <=>
    !p top s t:A->bool.
        open_in top s /\ open_in top t /\ topspace top = s UNION t
        ==> ?d. group_exactness
                  (homology_group(p,subtopology top (s INTER t)),
                   prod_group (homology_group(p,subtopology top s))
                              (homology_group(p,subtopology top t)),
                   homology_group(p,top))
                  ((\c. hom_induced p (subtopology top (s INTER t),{})
                                      (subtopology top s,{}) (\x. x) c,
                        hom_induced p (subtopology top (s INTER t),{})
                                      (subtopology top t,{}) (\x. x) c),
                   (\(a,b). group_div (homology_group(p,top))
                              (hom_induced p (subtopology top s,{}) (top,{}) (\x. x) a)
                              (hom_induced p (subtopology top t,{}) (top,{}) (\x. x) b))) /\
                group_exactness
                  (prod_group (homology_group(p,subtopology top s))
                              (homology_group(p,subtopology top t)),
                   homology_group(p,top),
                   homology_group(p - &1,subtopology top (s INTER t)))
                  ((\(a,b). group_div (homology_group(p,top))
                              (hom_induced p (subtopology top s,{}) (top,{}) (\x. x) a)
                              (hom_induced p (subtopology top t,{}) (top,{}) (\x. x) b)),
                   d) /\
                group_exactness
                  (homology_group(p,top),
                   homology_group(p - &1,subtopology top (s INTER t)),
                   prod_group (homology_group(p - &1,subtopology top s))
                              (homology_group(p - &1,subtopology top t)))
                  (d,
                   (\c. hom_induced (p - &1) (subtopology top (s INTER t),{})
                                    (subtopology top s,{}) (\x. x) c,
                        hom_induced (p - &1) (subtopology top (s INTER t),{})
                                    (subtopology top t,{}) (\x. x) c))`;;

let ATOP_HUREWICZ1_STATEMENT = new_definition
 `ATOP_HUREWICZ1_STATEMENT (u:A->bool) <=>
    !top a:A.
        path_connected_space top /\ a IN topspace top
        ==> (!z. z IN group_carrier(homology_group(&1,top))
                 ==> ?g. path_in top g /\ g(&0) = a /\ g(&1) = a /\
                         z = homologous_rel (1,top,{})
                               (frag_of (RESTRICTION (standard_simplex 1)
                                                     (\v:num->real. g(v 1))))) /\
            (!g. path_in top g /\ g(&0) = a /\ g(&1) = a /\
                 homotopic_with (\h. h(&0) = a /\ h(&1) = a)
                   (subtopology euclideanreal (real_interval[&0,&1]),top) g (\t. a)
                 ==> homologous_rel (1,top,{})
                       (frag_of (RESTRICTION (standard_simplex 1) (\v:num->real. g(v 1)))) =
                     group_id(homology_group(&1,top)))`;;


