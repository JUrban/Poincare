(* ========================================================================= *)
(* pc_apx_ncreq: the relative end structure of the Appendix layer for MT     *)
(* Lemma 11.30: APX_A25_NC_ENDS_STATEMENT, level and component form.         *)
(* Statement only; the proof is pc_apx_ncends.  Loads only the Appendix      *)
(* vocabulary (pc_apx_defs).                                                 *)
(* ========================================================================= *)

needs "src/pc_apx_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* APX_A25_NC_ENDS_STATEMENT.  W a connected component of M, the scalar      *)
(* curvature R proper on W (sublevel sets in W compact), some point of W     *)
(* with R <= L, every point of W with R > L the centre of an NK-neck or a    *)
(* (C,eps)-cap core.  Then W is a compact set plus finitely many pairwise    *)
(* disjoint horn charts H j in W of the region beyond the unit sphere:       *)
(* parametrizations of 1/2 < |y|, proper on |y| >= 1, every horn point an    *)
(* NK-neck centre with R > C L, the inner sphere the central sphere of an    *)
(* NK-neck with R <= 2 C L there.  For Lemma 11.30 (pc_p2c_horns): C := 2C,  *)
(* eps := Kc eps, L := rho^-2 give horns off Omega_rho with inner spheres in *)
(* Omega_(rho/2C).                                                           *)
(* ------------------------------------------------------------------------- *)

let APX_A25_NC_ENDS_STATEMENT = new_definition
 `APX_A25_NC_ENDS_STATEMENT (u:A->bool) <=>
    ?eps0. &0 < eps0 /\
      !C eps top atlas g NK L W.
         &1 <= C /\ &0 < eps /\ eps <= eps0 /\ &0 < L /\ hausdorff_space top /\
         riemannian_metric atlas (g:A->real^3^3) /\ apx_sphere_sep top atlas /\
         W IN connected_components_of top /\
         (!c. compact_in top {x | x IN W /\ mfd_scalar atlas g x <= c}) /\
         (?x. x IN W /\ mfd_scalar atlas g x <= L) /\
         (!x e. NK x e ==> rfs_neck (top,atlas) g eps x (e:real^3->A)) /\
         (!x. x IN W /\ L < mfd_scalar atlas g x
              ==> (?e. NK x e) \/ (?U Y. rfs_cap (top,atlas) g C eps U Y /\ x IN Y))
         ==> ?(J:num->bool) (H:num->real^3->A) K.
               FINITE J /\ compact_in top K /\ K SUBSET W /\
               W = K UNION UNIONS {IMAGE (H j) {y | &1 <= norm y} | j IN J} /\
               (!j. j IN J
                    ==> mfd_param top atlas {y | &1 / &2 < norm y} (H j) /\
                        IMAGE (H j) {y | &1 / &2 < norm y} SUBSET W /\
                        (!K'. compact_in top K'
                              ==> bounded {y | &1 <= norm y /\ H j y IN K'}) /\
                        (!y. &1 <= norm y
                             ==> C * L < mfd_scalar atlas g (H j y) /\
                                 ?e. NK (H j y) e) /\
                        (!y. norm y = &1 ==> mfd_scalar atlas g (H j y) <= &2 * C * L) /\
                        (?x e. NK x e /\
                               IMAGE e (sphere(vec 0,&1)) = IMAGE (H j) (sphere(vec 0,&1)))) /\
               (!i j. i IN J /\ j IN J /\ ~(i = j)
                      ==> DISJOINT (IMAGE (H i) {y | &1 <= norm y})
                                   (IMAGE (H j) {y | &1 <= norm y}))`;;

