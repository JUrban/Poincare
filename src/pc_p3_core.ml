(* ========================================================================= *)
(* Unit pc_p3_core: the core statements of Part 3, the results that the    *)
(* assembly (pc_p3_assembly) uses: MT Claim 15.1 (start),                  *)
(* Prop 16.1, Prop 17.1, Lemma 15.11 with the surgery operation of Sec 15.4, *)
(* the extension of a slab by Ricci flow (MT p. 409), Lemma 17.12, Thm 15.9 *)
(* in continuation form, and the Part 4 interface P4_EXTINCTION_STATEMENT  *)
(* (MT Thm 18.1, simply connected case; Part 4 proves it from the          *)
(* FINITE_EXTINCTION and P4_PINCH_FROM_INV statements: P4_EXTINCTION_ALIGN). *)
(* Each argument u only fixes a carrier type.  S0, P2_NORMALIZE, is in      *)
(* pc_p3_iface.                                                             *)
(*                                                                          *)
(* Sections S0b and S1-S8.                                                  *)
(* ========================================================================= *)

needs "src/pc_p3_inv.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* S0b. The extra history invariant p3_extra dl hs, on the history carrier   *)
(* A + num#num#real^3, kept outside p3_struct; dl is the control of p3_struct *)
(* (p3_stepf dd under p3_inv).  (F) fresh points: stage k only uses INL      *)
(* points and INR(j,i,y) with j <= k, so INR(SUC n,i,y) are fresh for the    *)
(* cap cores of event SUC n (rfs_event_ok needs cores disjoint from the     *)
(* whole old stage).  (P1) the plus half of every surgery neck of event k is *)
(* discarded; (P2) plus halves of distinct necks of an event are disjoint   *)
(* (Lemma 17.12 needs both).  Identity events are excluded                  *)
(* inside the proof of Lemma 17.12 (slab maximality), not here.             *)
(* Extensions with the same events keep it (P3_EXTRA_EXTENDS_SAME).         *)
(* ------------------------------------------------------------------------- *)

let p3_extra = new_definition
 `p3_extra (dl:real->real) (hs:(A+num#num#real^3)rfs_history) <=>
    (!k. k <= hs_count hs
         ==> topspace(hs_top hs k) SUBSET
             IMAGE INL (:A) UNION {INR(j,i,y) | j,i,y | j <= k}) /\
    (!k. 1 <= k /\ k <= hs_count hs
         ==> (!i. i IN ev_index(hs_event hs k)
                  ==> DISJOINT (IMAGE (ev_neck(hs_event hs k) i)
                                      {y | y IN rfs_neck_dom (dl(hs_time hs k)) /\
                                           &1 < norm y})
                               (topspace(hs_top hs k))) /\
             (!i j. i IN ev_index(hs_event hs k) /\ j IN ev_index(hs_event hs k) /\
                    ~(i = j)
                    ==> DISJOINT (IMAGE (ev_neck(hs_event hs k) i)
                                        {y | y IN rfs_neck_dom (dl(hs_time hs k)) /\
                                             &1 < norm y})
                                 (IMAGE (ev_neck(hs_event hs k) j)
                                        {y | y IN rfs_neck_dom (dl(hs_time hs k)) /\
                                             &1 < norm y})))`;;

(* ------------------------------------------------------------------------- *)
(* S1. MT Claim 15.1 as the start of the construction (Cor 15.10's proof:   *)
(* the flow from a normalized metric on [0, T_1], no surgery):              *)
(* a controlled history with no event and horizon T_1 on A + num#num#real^3 *)
(* starting at a normalized closed orientable (top,atlas,g) with abs Rm <=  *)
(* b0 (MT's 2^-4 and 2 become the dimensional constants c, C                *)
(* of PDE_CURVATURE_TIME; b0 = min(1, c / T_1)).  kappa0: Prop 4.11 volume  *)
(* part; eps <= eps2 makes R < eps^-2 on [0,T_1], so the canonical          *)
(* neighbourhood assumption is void there.  The manifold is simply connected *)
(* (p3_struct records simply connected components of the initial stage,     *)
(* for stage separation).  The history also satisfies p3_extra (stage 0     *)
(* uses INL points only, no events).                                        *)
(* ------------------------------------------------------------------------- *)

let P3_START_STATEMENT = new_definition
 `P3_START_STATEMENT (u:A->bool) <=>
    ?kappa0 eps2 b0. &0 < kappa0 /\ &0 < eps2 /\ &0 < b0 /\
      !C eps hf md g0 A0 rs ks dd.
         &1 < C /\ &0 < eps /\ eps <= eps2 /\ p3_hfun C hf /\ p3_modulus md /\
         p3_std_initial g0 A0 /\
         p3_seq_ok rs /\ p3_seq_ok ks /\ p3_seq_ok dd /\ rs 0 = eps /\ ks 0 = kappa0
         ==> !top atlas g.
               hausdorff_space top /\
               smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
               compact_space top /\ simply_connected_space top /\
               mfd_orientable top atlas /\
               riemannian_metric atlas g /\ rfs_normalized (top,atlas) g /\
               (!x. x IN topspace top ==> mfd_rm_norm atlas g x <= b0)
               ==> ?(hs:(A+num#num#real^3)rfs_history) iota iota'.
                     hs_count hs = 0 /\ rfs_horizon hs = p3_T 1 /\
                     rfs_initial (top,atlas) g hs iota iota' /\
                     p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs /\
                     p3_extra (p3_stepf dd) hs`;;

(* ------------------------------------------------------------------------- *)
(* S2. MT Prop 16.1 (noncollapsing through surgery), step i >= 1 (i = 0 is   *)
(* Claim 15.1): for sequences known up to i there are kappa <= ks i and,    *)
(* for each r' <= rs i, a control bound dfun r' <= ds i such that every     *)
(* history satisfying the step hypotheses with dlt = dfun r' and the strong *)
(* canonical neighbourhood assumption with rs' (r' on I_(i+1)) is           *)
(* kappa-noncollapsed on scales <= eps.  The                                *)
(* canonical assumption carries KL's volume clause on C-components          *)
(* (p3_canonv_assumption) and the noncollapsing has no exemption            *)
(* (p3_noncoll_all, without the exemption of MT p. 360).  The               *)
(* thresholds eps16, d16 stand for MT's fixed eps and delta_0 (Sec 15.1.1,  *)
(* Def 15.7(iii)).                                                          *)
(* ------------------------------------------------------------------------- *)

let P3_PROP_16_1_STATEMENT = new_definition
 `P3_PROP_16_1_STATEMENT (u:A->bool) <=>
    ?eps16 d16. &0 < eps16 /\ &0 < d16 /\
      !C eps hf md g0 A0.
         &1 < C /\ &0 < eps /\ eps <= eps16 /\ p3_hfun C hf /\ p3_modulus md /\
         p3_std_initial g0 A0
         ==> !i rs ks ds.
               1 <= i /\ rs 0 = eps /\ ds 0 <= d16 /\
               p3_seq_upto i rs /\ p3_seq_upto i ks /\ p3_seq_upto i ds
               ==> ?kappa dfun.
                     &0 < kappa /\ kappa <= ks i /\
                     (!r'. &0 < r' /\ r' <= rs i ==> &0 < dfun r' /\ dfun r' <= ds i) /\
                     p3_noncoll_prop u (C,eps,hf,md,g0,A0) i (rs,ks,ds) kappa dfun`;;

(* ------------------------------------------------------------------------- *)
(* S3. MT Prop 17.1 (strong canonical neighbourhoods through surgery), step *)
(* i >= 1, relative to any (kappa, dfun) satisfying the conclusion of       *)
(* Prop 16.1 (MT: the constant delta(r_(i+1)) of Prop 16.1): there are      *)
(* r' <= rs i and dnew <= dfun r' such that every history satisfying the    *)
(* step hypotheses with dlt = dnew has strong (C,eps)-canonical             *)
(* neighbourhoods with parameter rs'.  eps <= eps17, C >= C17(eps) (MT Sec  *)
(* 15.1.1: C from Cor 9.94 and Thm 12.32).                                 *)
(* g0, A0 are quantified before C17 and d17 (the cap constant C' of        *)
(* P2_THM_12_32 depends on g0).                                             *)
(* With KL's volume clause on C-components                                  *)
(* (p3_canon_prop concludes p3_canonv_assumption).                          *)
(* ------------------------------------------------------------------------- *)

let P3_PROP_17_1_STATEMENT = new_definition
 `P3_PROP_17_1_STATEMENT (u:A->bool) <=>
    ?eps17. &0 < eps17 /\
      !eps g0 A0. &0 < eps /\ eps <= eps17 /\ p3_std_initial g0 A0
        ==> ?C17 d17. &1 < C17 /\ &0 < d17 /\
              !C hf md.
                C17 <= C /\ p3_hfun C hf /\ p3_modulus md
                ==> !i rs ks ds kappa dfun.
                      1 <= i /\ rs 0 = eps /\ ds 0 <= d17 /\
                      p3_seq_upto i rs /\ p3_seq_upto i ks /\ p3_seq_upto i ds /\
                      &0 < kappa /\ kappa <= ks i /\
                      (!r'. &0 < r' /\ r' <= rs i ==> &0 < dfun r' /\ dfun r' <= ds i) /\
                      p3_noncoll_prop u (C,eps,hf,md,g0,A0) i (rs,ks,ds) kappa dfun
                      ==> ?r' dnew. &0 < r' /\ r' <= rs i /\ &0 < dnew /\
                                    dnew <= dfun r' /\
                                    p3_canon_prop u (C,eps,hf,md,g0,A0) i (rs,ks,ds) r' dnew`;;

(* ------------------------------------------------------------------------- *)
(* S4. MT Lemma 15.11 with the surgery operation of Sec 15.4 / Def 15.8      *)
(* (Thm 11.19, Lemma 11.30, Thm 11.31, Thm 13.2, Lemma 14.11, Thm 4.32):    *)
(* there are a standard initial metric, a cap modulus, thresholds, and for  *)
(* (eps,C) the surgery scale function hf, such that a controlled history     *)
(* whose last slab is singular at its horizon T extends by one event at T    *)
(* (surgery with control dl(T), scale h(T), caps, Omega_rho retained) and a *)
(* new slab up to any later bound, keeping the structural invariant.        *)
(* On the history carrier A + num#num#real^3 (u fixes A), for               *)
(* histories with the extra invariant p3_extra dl, which it keeps; the cap  *)
(* cores of the new event are INR(SUC n,i,y).                               *)
(* The hypothesis rp t <= eps for t >= 0                                    *)
(* (MT: r_i <= eps, r_0 = eps); without it the surgery scale                *)
(* hf(dl(T) rp(T), dl(T)) need not be below the h0 of Thm 13.2.             *)
(* ------------------------------------------------------------------------- *)

let P3_LEMMA_15_11_STATEMENT = new_definition
 `P3_LEMMA_15_11_STATEMENT (u:A->bool) <=>
    ?g0 A0 md eps11 d11.
      p3_std_initial g0 A0 /\ p3_modulus md /\ &0 < eps11 /\ &0 < d11 /\
      !eps C. &0 < eps /\ eps <= eps11 /\ &1 < C
        ==> ?hf. p3_hfun C hf /\
              !rp dl kp (hs:(A+num#num#real^3)rfs_history) Tb.
                 p3_extra dl hs /\
                 p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
                 rfs_canonical_assumption (rfs_view hs) C eps rp /\
                 rfs_noncollapsed (rfs_view hs) kp eps /\
                 (!t. &0 <= t ==> &0 < kp t /\ dl t <= d11) /\
                 (!t. &0 <= t ==> rp t <= eps) /\
                 rfs_slab_maximal hs (hs_count hs) /\ rfs_horizon hs < Tb
                 ==> ?hs'. rfs_extends hs hs' /\
                           hs_count hs' = SUC(hs_count hs) /\
                           hs_time hs' (SUC(hs_count hs)) = rfs_horizon hs /\
                           rfs_horizon hs < rfs_horizon hs' /\ rfs_horizon hs' <= Tb /\
                           p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs' /\
                           p3_extra dl hs'`;;

(* ------------------------------------------------------------------------- *)
(* S5. Extension of the last slab by Ricci flow (MT p. 409: Prop 4.12, Thm   *)
(* 3.11 uniqueness, Thm 4.32): if the last slab is not singular at the      *)
(* horizon, the history extends with the same events either to the bound Tb *)
(* or to a later horizon at which its last slab is singular.                *)
(* ------------------------------------------------------------------------- *)

let P3_FLOW_EXTENSION_STATEMENT = new_definition
 `P3_FLOW_EXTENSION_STATEMENT (u:A->bool) <=>
    !C eps hf md g0 A0 rp dl (hs:(A)rfs_history) Tb.
       p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
       ~rfs_slab_maximal hs (hs_count hs) /\ rfs_horizon hs < Tb
       ==> ?hs'. rfs_extends hs hs' /\ hs_count hs' = hs_count hs /\
                 rfs_horizon hs < rfs_horizon hs' /\ rfs_horizon hs' <= Tb /\
                 (rfs_horizon hs' = Tb \/ rfs_slab_maximal hs' (hs_count hs')) /\
                 p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs'`;;

(* ------------------------------------------------------------------------- *)
(* S6. MT Lemma 17.12 (surgery times do not accumulate): for fixed initial  *)
(* data, a time bound Tb and lower bounds on rp, dl and the surgery scale   *)
(* on [0,Tb), the number of events of a structurally controlled history     *)
(* with horizon <= Tb is bounded (each sphere surgery removes volume about  *)
(* h^3 / delta, the volume grows at most like e^(6t), the normalized start  *)
(* bounds the number of components).  dl <= d1712 (MT: delta_0 < 1/K).     *)
(* On the history carrier A + num#num#real^3                               *)
(* (u fixes A), with the hypothesis p3_extra dl hs (its P1, P2 part: plus  *)
(* halves of the surgery necks discarded and disjoint).                     *)
(* ------------------------------------------------------------------------- *)

let P3_LEMMA_17_12_STATEMENT = new_definition
 `P3_LEMMA_17_12_STATEMENT (u:A->bool) <=>
    !C eps hf md g0 A0.
       &1 < C /\ &0 < eps /\ p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0
       ==> ?d1712. &0 < d1712 /\
             !top0 atlas0 g00 Tb rmin dmin hmin.
                &0 < rmin /\ &0 < dmin /\ &0 < hmin
                ==> ?N. !rp dl (hs:(A+num#num#real^3)rfs_history).
                          hs_top hs 0 = top0 /\ hs_atlas hs 0 = atlas0 /\
                          hs_metric hs 0 (&0) = g00 /\
                          p3_struct (C,eps,hf,md,g0,A0) (rp,dl) hs /\
                          p3_extra dl hs /\
                          rfs_horizon hs <= Tb /\
                          (!t. &0 <= t ==> dl t <= d1712) /\
                          (!t. &0 <= t /\ t < Tb
                               ==> rmin <= rp t /\ dmin <= dl t /\
                                   hmin <= p3_hscale hf rp dl t)
                          ==> hs_count hs <= N`;;

(* ------------------------------------------------------------------------- *)
(* S7. MT Thm 15.9 in continuation form (finite histories; step-function     *)
(* controls dd <= ds; histories reaching T_1): there are eps1 and, for      *)
(* eps <= eps1, constants C, hf, md, g0, A0 and for every kappa0 surgery    *)
(* parameter sequences (rs 0 = eps, ks 0 = kappa0) such that every history  *)
(* with the invariant extends, keeping the invariant, beyond any time.      *)
(* On the history carrier A + num#num#real^3 (u fixes A), for               *)
(* histories with p3_extra (p3_stepf dd), which the extension keeps.        *)
(* ------------------------------------------------------------------------- *)

let P3_THM_15_9_STATEMENT = new_definition
 `P3_THM_15_9_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !eps. &0 < eps /\ eps <= eps1
        ==> ?C hf md g0 A0.
              &1 < C /\ p3_hfun C hf /\ p3_modulus md /\ p3_std_initial g0 A0 /\
              !kappa0. &0 < kappa0
                ==> ?rs ks ds.
                      p3_seq_ok rs /\ p3_seq_ok ks /\ p3_seq_ok ds /\
                      rs 0 = eps /\ ks 0 = kappa0 /\
                      !dd (hs:(A+num#num#real^3)rfs_history).
                         p3_seq_ok dd /\ (!j. dd j <= ds j) /\
                         p3_extra (p3_stepf dd) hs /\
                         p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs /\
                         p3_T 1 <= rfs_horizon hs
                         ==> !Tb. ?hs'. rfs_extends hs hs' /\
                                        p3_extra (p3_stepf dd) hs' /\
                                        p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs' /\
                                        Tb <= rfs_horizon hs'`;;

(* ------------------------------------------------------------------------- *)
(* S8. The Part 4 interface (MT Thm 18.1, simply connected case): for       *)
(* every closed simply connected Riemannian 3-manifold there is a time Text *)
(* (MT Sec 18.3.2: from the width of the initial metric) such that every    *)
(* history with the invariant starting at it whose horizon exceeds Text is  *)
(* extinct.  Part 4 may use everything in p3_inv (pinching, the caps with   *)
(* their distance non-increasing collapse maps, the limit metrics).         *)
(* ------------------------------------------------------------------------- *)

let P4_EXTINCTION_STATEMENT = new_definition
 `P4_EXTINCTION_STATEMENT (u:A->bool) <=>
    !top atlas g.
       hausdorff_space top /\
       smooth_manifold_atlas top (atlas:((A->bool)#(A->real^3))->bool) /\
       compact_space top /\ ~(topspace top = {}) /\
       simply_connected_space top /\ riemannian_metric atlas g
       ==> ?Text. !C eps hf md g0 A0 rs ks dd
                   (hs:(A+num#num#real^3)rfs_history) iota iota'.
                 &1 < C /\ &0 < eps /\ p3_hfun C hf /\ p3_modulus md /\
                 p3_std_initial g0 A0 /\
                 p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs /\
                 rfs_initial (top,atlas) g hs iota iota' /\
                 Text < rfs_horizon hs
                 ==> rfs_extinct hs`;;

