(* ========================================================================= *)
(* Unit pc_p3_inv: the stronger invariant of a controlled history (what the *)
(* MT Ch 13-17 induction maintains; it implies rfs_controlled): surgery caps *)
(* in standard coordinates with a smooth radial collapse (p3_cap_param,    *)
(* p3_cap_ok), Omega_rho retained, p3_struct, p3_inv, the step hypotheses of *)
(* MT Props 16.1 / 17.1 and their conclusions, the closure of a step, and  *)
(* the setting of Props 16.1-16.5.  The cap clauses are F1-F3 of I1; stage *)
(* 0 has simply connected components, for the separation hypotheses of the *)
(* Part 2 statements.                                                      *)
(*                                                                         *)
(* Sections I1-I4 and p3_p16_setting.                                      *)
(* ========================================================================= *)

needs "src/pc_p3_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* I1. The surgery caps (MT Ch 13: Def 13.3, Thm 13.2, Claim 13.1 as        *)
(* transplanted by the surgery of Sec 15.4).  Model coordinates: s1(x) =    *)
(* A0 + 4 - d(0,x) on the standard initial metric; p3_std_nc sends x to the *)
(* neck point with the same direction and s = s1(x).  p3_cap_param: the     *)
(* model domain reaches s1 = A0 + 4 inside the neck ((A0 + 4) dl < 1);      *)
(* standard coordinates Phi of the capped neck in the new stage (Phi = the  *)
(* neck on s1 < 0, the closed cap = Phi of s1 >= 0 = the closed core of the *)
(* minus cap chart); the rescaled pullback of g by Phi is dd-close to g0 on *)
(* B(0,1/dd) whenever dl <= md dd (Thm 13.2(4)); positive sectional         *)
(* curvature where s1 >= 1 (Thm 13.2(2)); and a SMOOTH radial collapse xi   *)
(* of the neck annulus into the model domain, inverse to p3_std_nc where    *)
(* s <= 0 (so Phi o xi is the neck where s < 0), into the closed cap where  *)
(* s >= 0, the tip where s >= A0 + 4, with pointwise derivative bound 1     *)
(* from the limit metric on the neck to the new metric (Thm 13.2(3) and     *)
(* Claim 13.1 in a smoothed form; the kinked map of MT is only Lipschitz).   *)
(* It is the input of the pinch maps of MT Prop 15.12.  Pinching             *)
(* (Thm 13.2(1)) is part of rfs_pinched.  The collapse is tied to the model  *)
(* coordinates by p3_std_nc (xi y) = y (F1), with xi mapping s >= 0 into     *)
(* the closed cap (F2) and (A0 + 4) dl < 1 (F3); the form Phi(xi y) =        *)
(* neck(y) for s(y) <= 0 would put the cut sphere s = 0, which the new       *)
(* stage does not contain, into the new stage.                               *)
(* ------------------------------------------------------------------------- *)

let p3_cap_param = new_definition
 `p3_cap_param (md:real->real,g0:real^3->real^3^3,A0:real) (dl:real->real,h:real->real)
               (hs:(A)rfs_history) (k:num) (i:num) (Phi:real^3->A) (xi:real^3->real^3) <=>
      (A0 + &4) * dl(hs_time hs k) < &1 /\
      mfd_param (hs_top hs k) (hs_atlas hs k)
        {x | --(inv(dl(hs_time hs k))) < A0 + &4 - p3_std_dist g0 x} Phi /\
      (!x. --(inv(dl(hs_time hs k))) < A0 + &4 - p3_std_dist g0 x /\
           A0 + &4 - p3_std_dist g0 x < &0
           ==> Phi x = ev_neck (hs_event hs k) i (p3_std_nc g0 A0 x)) /\
      IMAGE Phi {x | &0 <= A0 + &4 - p3_std_dist g0 x} =
      IMAGE (ev_capm (hs_event hs k) i) (cball(vec 0,&1)) /\
      (!dd. &0 < dd /\ dl(hs_time hs k) <= md dd
            ==> rfs_close_on (rfs_kreg dd) dd
                  {x | p3_std_dist g0 x < inv dd /\
                       --(inv(dl(hs_time hs k))) < A0 + &4 - p3_std_dist g0 x}
                  g0
                  (\x. inv(h(hs_time hs k) pow 2) %%
                       rfs_pullback (hs_atlas hs k) Phi
                                    (hs_metric hs k (hs_time hs k)) x)) /\
      (!x u v. &1 <= A0 + &4 - p3_std_dist g0 x /\ ~collinear {vec 0,u,v}
               ==> &0 < mfd_sectional (hs_atlas hs k) (hs_metric hs k (hs_time hs k))
                                      (Phi x) u v) /\
      smooth_map_on (rfs_neck_dom (dl(hs_time hs k))) (xi:real^3->real^3) /\
      (!y. y IN rfs_neck_dom (dl(hs_time hs k))
           ==> --(inv(dl(hs_time hs k))) < A0 + &4 - p3_std_dist g0 (xi y) /\
               (sqrt(&2) * log(norm y) <= &0 ==> p3_std_nc g0 A0 (xi y) = y) /\
               (&0 <= sqrt(&2) * log(norm y)
                ==> &0 <= A0 + &4 - p3_std_dist g0 (xi y)) /\
               (A0 + &4 <= sqrt(&2) * log(norm y) ==> xi y = vec 0)) /\
      (!y v. y IN rfs_neck_dom (dl(hs_time hs k))
             ==> (jacobian xi (at y) ** v) dot
                 (rfs_pullback (hs_atlas hs k) Phi (hs_metric hs k (hs_time hs k))
                               (xi y) ** (jacobian xi (at y) ** v)) <=
                 v dot (rfs_pullback (rfs_vatlas (rfs_preview hs k) (hs_time hs k))
                                     (ev_neck (hs_event hs k) i)
                                     (rfs_vmetric (rfs_preview hs k) (hs_time hs k)) y ** v))`;;

let p3_cap_ok = new_definition
 `p3_cap_ok (md:real->real,g0:real^3->real^3^3,A0:real) (dl:real->real,h:real->real)
            (hs:(A)rfs_history) (k:num) (i:num) <=>
    ?Phi xi. p3_cap_param (md,g0,A0) (dl,h) hs k i Phi xi`;;

(* Omega_rho(T) is retained (MT Sec 15.4: C_T contains Omega_rho, rho =    *)
(* delta(T) r(T)).                                                           *)

let p3_omega_rho_ok = new_definition
 `p3_omega_rho_ok (hs:(A)rfs_history) (rp:real->real,dl:real->real) (k:num) <=>
    !x. x IN ev_omega(hs_event hs k) /\
        rfs_vscalar (rfs_preview hs k) (hs_time hs k) x <=
        inv((dl(hs_time hs k) * rp(hs_time hs k)) pow 2)
        ==> x IN topspace(hs_top hs k)`;;

(* The surgery necks evolve for rescaled time 2: MT Lemma 17.7               *)
(* (p. 405-406) re-centres the strong delta-neck of the                      *)
(* surgery at a point x of its continuing half, which needs backward time    *)
(* 1/R(x) > h^2 when R(x) < R(y); MT's proof of Thm 11.31 (p. 291: the       *)
(* limit is the round shrinking cylinder on (-infinity,0]) gives any fixed   *)
(* backward length.  Same centre y and scale as the rfs_surgery_ok clause.   *)

let p3_neck2_ok = new_definition
 `p3_neck2_ok (dl:real->real,h:real->real) (hs:(A)rfs_history) (k:num) <=>
    !i. i IN ev_index(hs_event hs k)
        ==> ?y. rfs_evolving_neck (rfs_preview hs k) (dl(hs_time hs k)) y
                                  (hs_time hs k) (&2) (ev_neck(hs_event hs k) i) /\
                rfs_vscalar (rfs_preview hs k) (hs_time hs k) y =
                inv(h(hs_time hs k) pow 2)`;;

(* ------------------------------------------------------------------------- *)
(* I2. The structural part (MT Assumptions (1)-(7), normalized start         *)
(* (Assumption (3)), surgery at scale h with control dl (Def 15.5), surgery  *)
(* caps (Ch 13), Omega_rho retained, pinching) for a canonical neighbourhood *)
(* parameter function rp and a control function dl; the full invariant      *)
(* adds the canonical neighbourhood assumption with the step function of rs *)
(* and noncollapsing with the step function of ks (MT Thm 15.9 (1)-(3)).    *)
(* The initial stage has simply connected components (the Poincare setting: *)
(* with RFS_CUTCAP_SC_STATEMENT all stages then do, RFS_HISTORY_SC, so      *)
(* every neck sphere separates, SMT_SC_SPHERE_SEP; the forms of MT Thm     *)
(* 11.8, Lemma 11.30 and Thm 11.31 used here assume this, apx_sphere_sep). *)
(* The surgery necks also evolve for rescaled time 2 (p3_neck2_ok).        *)
(* ------------------------------------------------------------------------- *)

let p3_struct = new_definition
 `p3_struct (C:real,eps:real,hf:real->real->real,md:real->real,
             g0:real^3->real^3^3,A0:real)
            (rp:real->real,dl:real->real) (hs:(A)rfs_history) <=>
    rfs_history_ok hs /\
    rfs_normalized (hs_top hs 0,hs_atlas hs 0) (hs_metric hs 0 (&0)) /\
    rfs_components_sc (hs_top hs 0) /\
    (!t. &0 <= t ==> &0 < rp t /\ &0 < dl t) /\
    (!s t. &0 <= s /\ s <= t ==> rp t <= rp s /\ dl t <= dl s) /\
    (!k. k <= hs_count hs ==> mfd_orientable (hs_top hs k) (hs_atlas hs k)) /\
    (!k. 1 <= k /\ k <= hs_count hs ==> p3_neck2_ok (dl,p3_hscale hf rp dl) hs k) /\
    (!k. 1 <= k /\ k <= hs_count hs
         ==> rfs_surgery_ok hs C eps dl (p3_hscale hf rp dl) k /\
             p3_omega_rho_ok hs (rp,dl) k /\
             (!i. i IN ev_index(hs_event hs k)
                  ==> p3_cap_ok (md,g0,A0) (dl,p3_hscale hf rp dl) hs k i)) /\
    (!k. k < hs_count hs ==> rfs_slab_maximal hs k) /\
    rfs_pinched (rfs_view hs)`;;

(* ------------------------------------------------------------------------- *)
(* Following Kleiner-Lott Def 69.1, p3_inv and p3_step_hyp carry, besides    *)
(* the plain canonical and noncollapsing                                     *)
(* conjuncts, the canonical assumption with the volume clause on             *)
(* C-components (p3_canonv_assumption) and noncollapsing without the         *)
(* positive-curvature exemption (p3_noncoll_all); Prop 16.1                  *)
(* (p3_noncoll_prop) assumes the former and concludes the latter, Prop 17.1  *)
(* (p3_canon_prop) concludes the former; p3_step_closed (I4) also assumes    *)
(* both for the truncation at T_i (threaded through pc_p3_assembly).         *)
(* ------------------------------------------------------------------------- *)

let p3_inv = new_definition
 `p3_inv (C:real,eps:real,hf:real->real->real,md:real->real,
          g0:real^3->real^3^3,A0:real)
         (rs:num->real,ks:num->real,dd:num->real) (hs:(A)rfs_history) <=>
    p3_seq_ok rs /\ p3_seq_ok ks /\ p3_seq_ok dd /\
    p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs,p3_stepf dd) hs /\
    rfs_canonical_assumption (rfs_view hs) C eps (p3_stepf rs) /\
    rfs_noncollapsed (rfs_view hs) (p3_stepf ks) eps /\
    p3_canonv_assumption (rfs_view hs) C eps (p3_stepf rs) /\
    p3_noncoll_all (rfs_view hs) (p3_stepf ks) eps`;;

(* ------------------------------------------------------------------------- *)
(* I3. The hypotheses of MT Prop 16.1 / Prop 17.1 at step i (i >= 1): the    *)
(* sequences (rs,ks,ds) are known up to index i; (rs',ks') are full          *)
(* sequences extending them (rs' (i+1) is the new canonical neighbourhood    *)
(* parameter); the control dd is below ds up to i and below dlt on           *)
(* I_i and I_(i+1) (MT: delta(t) <= delta(r_(i+1)) on [T_(i-1), T_(i+1))); *)
(* the history ends in (T_i, T_(i+1)], is structurally controlled with the  *)
(* new parameters, and has canonical neighbourhoods and noncollapsing on    *)
(* [0, T_i).  p3_noncoll_prop is the conclusion of Prop 16.1 for (kappa,    *)
(* dfun), in step form (ks' (i+1) = kappa on I_(i+1), the given ks' on      *)
(* [0,T_i)); p3_canon_prop the conclusion of Prop 17.1 for (r', dnew).      *)
(* The first argument u only fixes the carrier type.                        *)
(* ------------------------------------------------------------------------- *)

let p3_step_hyp = new_definition
 `p3_step_hyp (C:real,eps:real,hf:real->real->real,md:real->real,
               g0:real^3->real^3^3,A0:real)
              (i:num) (rs:num->real,ks:num->real,ds:num->real) (dlt:real)
              (rs':num->real,ks':num->real,dd:num->real) (hs:(A)rfs_history) <=>
    (!j. j <= i ==> rs' j = rs j /\ ks' j = ks j) /\
    p3_seq_ok rs' /\ p3_seq_ok ks' /\ p3_seq_ok dd /\
    (!j. j <= i ==> dd j <= ds j) /\ dd i <= dlt /\ dd (SUC i) <= dlt /\
    p3_T i < rfs_horizon hs /\ rfs_horizon hs <= p3_T (SUC i) /\
    p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs',p3_stepf dd) hs /\
    rfs_canonical_assumption (rfs_trunc (rfs_view hs) (p3_T i)) C eps (p3_stepf rs') /\
    rfs_noncollapsed (rfs_trunc (rfs_view hs) (p3_T i)) (p3_stepf ks') eps /\
    p3_canonv_assumption (rfs_trunc (rfs_view hs) (p3_T i)) C eps (p3_stepf rs') /\
    p3_noncoll_all (rfs_trunc (rfs_view hs) (p3_T i)) (p3_stepf ks') eps`;;

let p3_noncoll_prop = new_definition
 `p3_noncoll_prop (u:A->bool)
    (C:real,eps:real,hf:real->real->real,md:real->real,g0:real^3->real^3^3,A0:real)
    (i:num) (rs:num->real,ks:num->real,ds:num->real) (kappa:real) (dfun:real->real) <=>
    !r' rs' ks' dd (hs:(A)rfs_history).
       &0 < r' /\ r' <= rs i /\ rs' (SUC i) = r' /\ ks' (SUC i) = kappa /\
       p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) (dfun r') (rs',ks',dd) hs /\
       p3_canonv_assumption (rfs_view hs) C eps (p3_stepf rs')
       ==> p3_noncoll_all (rfs_view hs) (p3_stepf ks') eps`;;

let p3_canon_prop = new_definition
 `p3_canon_prop (u:A->bool)
    (C:real,eps:real,hf:real->real->real,md:real->real,g0:real^3->real^3^3,A0:real)
    (i:num) (rs:num->real,ks:num->real,ds:num->real) (r':real) (dnew:real) <=>
    !rs' ks' dd (hs:(A)rfs_history).
       rs' (SUC i) = r' /\
       p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dnew (rs',ks',dd) hs
       ==> p3_canonv_assumption (rfs_view hs) C eps (p3_stepf rs')`;;

(* ------------------------------------------------------------------------- *)
(* I4. Closure of step i (the combined conclusion of MT Props 16.1 and 17.1 *)
(* at step i for final sequences (rs,ks,dd)): every structurally controlled *)
(* history ending in (T_i, T_(i+1)] whose truncation at T_i has canonical   *)
(* neighbourhoods and is noncollapsed has the full invariant.  Used by the   *)
(* derivation of Thm 15.9 (unit pc_p3_assembly).                             *)
(* ------------------------------------------------------------------------- *)

let p3_step_closed = new_definition
 `p3_step_closed (u:A->bool)
    (C:real,eps:real,hf:real->real->real,md:real->real,g0:real^3->real^3^3,A0:real)
    (rs:num->real,ks:num->real,dd:num->real) (i:num) <=>
    !hs:(A)rfs_history.
       p3_struct (C,eps,hf,md,g0,A0) (p3_stepf rs,p3_stepf dd) hs /\
       p3_T i < rfs_horizon hs /\ rfs_horizon hs <= p3_T (SUC i) /\
       rfs_canonical_assumption (rfs_trunc (rfs_view hs) (p3_T i)) C eps (p3_stepf rs) /\
       rfs_noncollapsed (rfs_trunc (rfs_view hs) (p3_T i)) (p3_stepf ks) eps /\
       p3_canonv_assumption (rfs_trunc (rfs_view hs) (p3_T i)) C eps (p3_stepf rs) /\
       p3_noncoll_all (rfs_trunc (rfs_view hs) (p3_T i)) (p3_stepf ks) eps
       ==> p3_inv (C,eps,hf,md,g0,A0) (rs,ks,dd) hs`;;

let p3_p16_setting = new_definition
 `p3_p16_setting (C:real,eps:real,hf:real->real->real,md:real->real,
                  g0:real^3->real^3^3,A0:real)
                 (i:num) (rs:num->real,ks:num->real,ds:num->real) (r':real) (dlt:real)
                 (rs':num->real,ks':num->real,dd:num->real) (hs:(A)rfs_history) <=>
    rs' (SUC i) = r' /\
    p3_step_hyp (C,eps,hf,md,g0,A0) i (rs,ks,ds) dlt (rs',ks',dd) hs /\
    rfs_canonical_assumption (rfs_view hs) C eps (p3_stepf rs')`;;

