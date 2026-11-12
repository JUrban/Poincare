(* ========================================================================= *)
(* Unit pc_cmw_defs: the internal statements of the width unit pc_cm_width.  *)
(* Each is proved in a sub-unit from the CM and WAN statement constants of   *)
(* pc_cm_stmts:                                                              *)
(*   CMW_POS_STATEMENT  (pc_cmw_pos): sweepouts of small energy with C^1     *)
(*     slices are homotopic to sweepouts with constant slices;              *)
(*   CMW_P15_STATEMENT  (pc_cmw_p15): CM Prop 1.5 with footnote 8: a C^1     *)
(*     sweepout of a component gives an embedded energy sweepout with C^1   *)
(*     slices, energies below its sweep area plus e, no harmonic slices,    *)
(*     and the same essentiality;                                           *)
(*   CMW_REG_STATEMENT  (pc_cmw_reg): area at most energy for C^0 /\ W^{1,2} *)
(*     slices, and CM Lemma D.1: a jointly C^1 sweepout uniformly close in  *)
(*     C^0, energy, area and the trace of a given Q.                         *)
(* pc_cm_width proves the width chain statement from them.                  *)
(* ========================================================================= *)

needs "src/pc_cm_stmts.ml";;
needs "src/pc_cmw_top.ml";;

prioritize_real();;
type_invention_error := true;;

(* Embedded sweepouts with C^1 slices (through the radial extension) whose  *)
(* Jacobians are jointly continuous on S^2 x [0,1].                          *)

let cmw_c1sweep = new_definition
 `cmw_c1sweep (W:real^3->real->real^K) <=>
    (!t. t IN real_interval[&0,&1]
         ==> continuously_differentiable 1 {z:real^3 | ~(z = vec 0)}
               (wan_rext (\y. W y t))) /\
    (!i j. 1 <= i /\ i <= dimindex(:K) /\ 1 <= j /\ j <= 3
           ==> (\x:real^(3,1)finite_sum.
                   lift(jacobian (wan_rext (\y. W y (drop(sndcart x)))) (at (fstcart x))$i$j))
               continuous_on
               {x | fstcart x IN sphere(vec 0,&1) /\ drop(sndcart x) IN real_interval[&0,&1]})`;;

let CMW_POS_STATEMENT = new_definition
 `CMW_POS_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> ?e. &0 < e /\
               !W:real^3->real->real^K.
                  cm_sweep S W /\ cmw_c1sweep W /\
                  (!t. t IN real_interval[&0,&1] ==> cm_sen G (\y. W y t) < e)
                  ==> ?c:real->real^K. cm_shomotopic S W (\y t. c t)`;;

let CMW_P15_STATEMENT = new_definition
 `CMW_P15_STATEMENT (aa:A->bool) (kk:K->bool) <=>
    !top atlas (g:A->real^3^3) (f:A->real^K) G d U sigma e.
       cm_emb (top,atlas) g f G d /\ U IN connected_components_of top /\
       p4_sweepout_in (top,atlas) U sigma /\ &0 < e
       ==> ?W:real^3->real->real^K.
              cm_sweep (IMAGE f (topspace top)) W /\ cmw_c1sweep W /\
              (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                     ==> W y t IN IMAGE f U) /\
              (!t. t IN real_interval[&0,&1]
                   ==> cm_sen G (\y. W y t) < p4_sweep_area atlas g sigma + e /\
                       ~cm_sharmonic (IMAGE f (topspace top)) G (\y. W y t)) /\
              p4_essential (subtopology top U)
                (p4_susp (\y t. mfd_emb_inv top f (W y t)))`;;

let CMW_REG_STATEMENT = new_definition
 `CMW_REG_STATEMENT (kk:K->bool) <=>
    !S (G:real^K->real^K^K) d.
       cm_target S G d
       ==> (!u. cm_smap S u ==> cm_sarea G u <= cm_sen G u) /\
           !(Q:real^K->real^K^K) (W:real^3->real->real^K) mu.
              smooth_map_on (:real^K) ((vectorize:real^K^K->real^(K,K)finite_prod) o Q) /\
              (!z. transp(Q z) = Q z) /\ cm_sweep S W /\ &0 < mu
              ==> ?W':real^3->real->real^K.
                     continuously_differentiable 1
                       {x:real^(3,1)finite_sum |
                          ~(fstcart x = vec 0) /\ drop(sndcart x) IN real_interval[&0,&1]}
                       (\x. W' (inv(norm(fstcart x)) % fstcart x) (drop(sndcart x))) /\
                     (!y y'. y IN sphere(vec 0,&1) /\ y' IN sphere(vec 0,&1)
                             ==> W' y (&0) = W' y' (&0) /\ W' y (&1) = W' y' (&1)) /\
                     (!y t. y IN sphere(vec 0,&1) /\ t IN real_interval[&0,&1]
                            ==> W' y t IN S /\ norm(W' y t - W y t) < mu) /\
                     cm_shomotopic S W W' /\
                     !t. t IN real_interval[&0,&1]
                         ==> abs(cm_sen G (\y. W' y t) - cm_sen G (\y. W y t)) < mu /\
                             abs(cm_sarea G (\y. W' y t) - cm_sarea G (\y. W y t)) < mu /\
                             abs(cm_strace G Q (\y. W' y t) - cm_strace G Q (\y. W y t)) < mu`;;

