(* ========================================================================= *)
(* pc_mfd_cut: cut-and-cap data for 3-manifolds (the data of the endgame     *)
(* sphere-system statement RFS_SPHERE_SYSTEM_STATEMENT).  mfd_cut_cap, with  *)
(* mfd_cut_spheres and mfd_cut_cores, consists of neck charts e i of X, ball *)
(* charts cp i (plus side) and cm i (minus side) of Z, a diffeomorphism ff   *)
(* of X minus the cut spheres onto Z minus the closed cap cores, and the     *)
(* radial collar equations.                                                  *)
(*                                                                           *)
(* The definitions, membership, compactness, and the empty cut.              *)
(* ========================================================================= *)

needs "src/pc_mfd_maps.ml";;

prioritize_real();;
type_invention_error := true;;

let mfd_cut_spheres = new_definition
 `mfd_cut_spheres (J:num->bool) (e:num->real^3->A) =
    UNIONS {IMAGE (e i) (sphere(vec 0,&1)) | i IN J}`;;

let mfd_cut_cores = new_definition
 `mfd_cut_cores (J:num->bool) (cp:num->real^3->A) (cm:num->real^3->A) =
    UNIONS {IMAGE (cp i) (cball(vec 0,&1)) UNION IMAGE (cm i) (cball(vec 0,&1)) |
            i IN J}`;;

let mfd_cut_cap = new_definition
 `mfd_cut_cap (topX:A topology) (atlasX:((A->bool)#(A->real^3))->bool)
              (topZ:B topology) (atlasZ:((B->bool)#(B->real^3))->bool)
              (J:num->bool) (e:num->real^3->A) (cp:num->real^3->B)
              (cm:num->real^3->B) (ff:A->B) (gg:B->A) <=>
    FINITE J /\
    (!i. i IN J
         ==> mfd_neck_chart topX atlasX (e i) /\
             mfd_ball_chart topZ atlasZ (cp i) /\
             mfd_ball_chart topZ atlasZ (cm i)) /\
    (!i j. i IN J /\ j IN J /\ ~(i = j)
           ==> DISJOINT (IMAGE (e i) (annulus (&1 / &2) (&2)))
                        (IMAGE (e j) (annulus (&1 / &2) (&2)))) /\
    (!i j. i IN J /\ j IN J
           ==> DISJOINT (IMAGE (cp i) (ball(vec 0,&2)))
                        (IMAGE (cm j) (ball(vec 0,&2))) /\
               (~(i = j)
                ==> DISJOINT (IMAGE (cp i) (ball(vec 0,&2)))
                             (IMAGE (cp j) (ball(vec 0,&2))) /\
                    DISJOINT (IMAGE (cm i) (ball(vec 0,&2)))
                             (IMAGE (cm j) (ball(vec 0,&2))))) /\
    mfd_diffeo topX atlasX (topspace topX DIFF mfd_cut_spheres J e)
               topZ atlasZ (topspace topZ DIFF mfd_cut_cores J cp cm) ff gg /\
    (!i x. i IN J /\ x IN annulus (&1) (&2) ==> ff(e i x) = cp i x) /\
    (!i x. i IN J /\ x IN annulus (&1 / &2) (&1)
           ==> ff(e i x) = cm i (inv(norm x pow 2) % x))`;;

let IN_MFD_CUT_SPHERES = prove
 (`!J (e:num->real^3->A) p.
        p IN mfd_cut_spheres J e <=> ?i x. i IN J /\ norm x = &1 /\ p = e i x`,
  REWRITE_TAC[mfd_cut_spheres; UNIONS_GSPEC; IN_ELIM_THM; IN_IMAGE; IN_SPHERE_0] THEN
  MESON_TAC[]);;

let IN_MFD_CUT_CORES = prove
 (`!J (cp:num->real^3->A) cm p.
        p IN mfd_cut_cores J cp cm <=>
        ?i x. i IN J /\ norm x <= &1 /\ (p = cp i x \/ p = cm i x)`,
  REWRITE_TAC[mfd_cut_cores; UNIONS_GSPEC; IN_ELIM_THM; IN_IMAGE; IN_UNION;
              IN_CBALL_0] THEN
  MESON_TAC[]);;

let MFD_CUT_SPHERES_EMPTY = prove
 (`!e:num->real^3->A. mfd_cut_spheres {} e = {}`,
  REWRITE_TAC[EXTENSION; IN_MFD_CUT_SPHERES; NOT_IN_EMPTY]);;

let MFD_CUT_CORES_EMPTY = prove
 (`!(cp:num->real^3->A) cm. mfd_cut_cores {} cp cm = {}`,
  REWRITE_TAC[EXTENSION; IN_MFD_CUT_CORES; NOT_IN_EMPTY]);;

(* The empty cut: mfd_cut_cap is then a diffeomorphism of the whole spaces  *)
(* (so the predicate is not vacuous: MFD_CUT_CAP_EMPTY_ID).                  *)

let MFD_CUT_CAP_EMPTY = prove
 (`!topX (atlasX:((A->bool)#(A->real^3))->bool)
    topZ (atlasZ:((B->bool)#(B->real^3))->bool) e cp cm ff gg.
        mfd_cut_cap topX atlasX topZ atlasZ {} e cp cm ff gg <=>
        mfd_diffeo topX atlasX (topspace topX) topZ atlasZ (topspace topZ) ff gg`,
  REWRITE_TAC[mfd_cut_cap; FINITE_EMPTY; NOT_IN_EMPTY; MFD_CUT_SPHERES_EMPTY;
              MFD_CUT_CORES_EMPTY; DIFF_EMPTY]);;

let MFD_CUT_CAP_EMPTY_ID = prove
 (`!top (atlas:((A->bool)#(A->real^3))->bool) e cp cm.
        smooth_manifold_atlas top atlas
        ==> mfd_cut_cap top atlas top atlas {} e cp cm (\x. x) (\x. x)`,
  SIMP_TAC[MFD_CUT_CAP_EMPTY; MFD_DIFFEO_ID; OPEN_IN_TOPSPACE]);;

