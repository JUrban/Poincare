(* ========================================================================= *)
(* Unit pc_p2b_kncapcreq (statement only): the statement                     *)
(* P2B_KNCL_CAPC_STATEMENT, the constant clauses of the soul cap in piece    *)
(* (d) of the statements of pc_p2b_c994req, case P.  It is used in           *)
(* pc_p2b_kncl4 and proved as P2BCC_KNCL_CAPC (pc_p2b_kncapc).               *)
(* ========================================================================= *)

(* The statement is a self-contained part of piece (d), case P (positive    *)
(* curvature at time 0): the constant clauses of the soul cap.  Given the   *)
(* cap structure produced by KNCL_SOUL_CAP (pc_p2b_kncl2) for a             *)
(* kappa0-solution with sec > 0 at time 0, the pinching of (b) on the ball  *)
(* B(p, Dst R(p)^(-1/2)), the factor-2 comparison of R on the neck e3 and   *)
(* the derivative bounds of COR_9_71 at time 0, the pair (U,Y) is a         *)
(* (C,eps)-cap at time 0 with C depending only on eps, K1, Dst, D1, kappa0  *)
(* and C71.  No inputs (all needed facts are hypotheses).  Needs:           *)
(* pc_p2b_kreq.ml (rfs_cap via pc_rfs_geom, p2b_kappa_solution).            *)

needs "src/pc_p2b_kreq.ml";;

prioritize_real();;
type_invention_error := true;;

let P2B_KNCL_CAPC_STATEMENT = new_definition
 `P2B_KNCL_CAPC_STATEMENT (w:B->bool) <=>
    !eps K1 Dst D1 kappa0 C71.
       &0 < eps /\ eps <= &1 / &100 /\ &4 <= K1 /\ &0 < Dst /\ &1 < D1 /\
       &0 < kappa0 /\ &0 < C71
       ==> ?C. &1 < C /\
             !top atlas (g:real->B->real^3^3) p U Y z3 (e3:real^3->B) w0.
               p2b_kappa_solution kappa0 (top,atlas) g /\ ~compact_space top /\
               (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                        ==> &0 < mfd_sectional atlas (g(&0)) x u v) /\
               (!x. x IN topspace top
                    ==> sqrt(rfs_scalar_grad2 atlas (g(&0)) x) <=
                        C71 * mfd_scalar atlas (g(&0)) x * sqrt(mfd_scalar atlas (g(&0)) x) /\
                        abs(rfs_scalar_lap atlas (g(&0)) x +
                            &2 * rfs_ric_norm2 atlas (g(&0)) x) <=
                        C71 * mfd_scalar atlas (g(&0)) x pow 2) /\
               p IN topspace top /\ &0 < mfd_scalar atlas (g(&0)) p /\
               (!x u v. x IN mfd_ball (top,atlas) (g(&0)) p
                               (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\
                        ~collinear {vec 0,u,v}
                        ==> inv D1 * mfd_scalar atlas (g(&0)) p <
                            mfd_sectional atlas (g(&0)) x u v /\
                            mfd_sectional atlas (g(&0)) x u v <
                            D1 * mfd_scalar atlas (g(&0)) p) /\
               (?b e e' z z' f f'.
                  mfd_ball_chart top atlas b /\ IMAGE b (ball(vec 0,&2)) SUBSET U /\
                  Y = IMAGE b (ball(vec 0,&1)) /\
                  rfs_neck (top,atlas) (g(&0)) eps z e /\
                  IMAGE e (rfs_neck_dom eps) = U DIFF IMAGE b (cball(vec 0,&1)) /\
                  rfs_neck (top,atlas) (g(&0)) eps z' e' /\
                  IMAGE e' (rfs_neck_dom eps) SUBSET U /\
                  IMAGE e' (sphere(vec 0,&1)) = IMAGE b (sphere(vec 0,&1)) /\
                  sphere_diffeo f f' /\
                  (!y. y IN annulus (&1) (&2) ==> b y = e'(radial_ext f y))) /\
               open_in top U /\ Y SUBSET U /\
               mfd_ball (top,atlas) (g(&0)) p (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p)))
                 SUBSET Y /\
               rfs_neck (top,atlas) (g(&0)) (eps / K1) z3 e3 /\
               U SUBSET mfd_ball (top,atlas) (g(&0)) p
                          (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p))) UNION
                        IMAGE e3 (apx_slab (--inv(eps / K1)) (&3 * inv eps)) /\
               IMAGE e3 (apx_slab (--inv(eps / K1)) (&3 * inv eps)) SUBSET U /\
               w0 IN apx_slab (--inv(eps / K1)) (&3 * inv eps) /\
               e3 w0 IN mfd_ball (top,atlas) (g(&0)) p
                          (Dst * inv(sqrt(mfd_scalar atlas (g(&0)) p))) /\
               (!y. y IN IMAGE e3 (rfs_neck_dom (eps / K1))
                    ==> mfd_scalar atlas (g(&0)) z3 / &2 <= mfd_scalar atlas (g(&0)) y /\
                        mfd_scalar atlas (g(&0)) y <= &3 / &2 * mfd_scalar atlas (g(&0)) z3) /\
               (!y q. y IN Y /\ q IN topspace top /\ ~(q IN U)
                      ==> ?s. s IN IMAGE e3 (rfs_neck_dom (eps / K1)) /\
                              mfd_joinable (top,atlas) y s /\
                              mfd_dist (top,atlas) (g(&0)) y s +
                              sqrt(&1 - eps / K1) * inv(sqrt(mfd_scalar atlas (g(&0)) z3)) *
                              (&2 * inv eps)
                              <= mfd_dist (top,atlas) (g(&0)) y q)
               ==> rfs_cap (top,atlas) (g(&0)) C eps U Y`;;

