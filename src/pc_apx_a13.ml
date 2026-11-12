(* ========================================================================= *)
(* pc_apx_a13: MT Lemma A.13 (with A.16) in corrected form, unconditional,   *)
(* and its core form: APX_A13 and APX_A13_CORE of pc_apx_engine with their   *)
(* hypothesis SMT_PRODUCT2_STATEMENT (M6b) discharged by SMT_PRODUCT2        *)
(* (pc_smt_product).  The corrected form assumes apx_sphere_sep (without it  *)
(* the sections clause fails, e.g. for a chain of two exact necks in         *)
(* S^2 x circle) and uses exact-end regions of length 1/(8 eps).  Kept       *)
(* apart from the engine so that the engine's closure does not contain       *)
(* pc_mfd_flow.                                                              *)
(* ========================================================================= *)

needs "src/pc_apx_engine.ml";;
needs "src/pc_smt_product.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The unconditional forms.                                                  *)
(* ------------------------------------------------------------------------- *)

let APX_A13_UNCOND = prove
 (`!u:A->bool.
     ?eps0. &0 < eps0 /\
       !top atlas g eps n x e.
          &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
          riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
          apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x
                    (e:int->real^3->A)
          ==> ?E L f f'.
                &0 <= L /\ sphere_diffeo f f' /\
                mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
                (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
                (!y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
                     ==> E y = e (&n) (radial_ext f (exp(--L / sqrt(&2)) % y))) /\
                IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
                apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e /\
                apx_tube (top,atlas) g eps E (exp(--inv eps / sqrt(&2)))
                         (exp((L + inv eps) / sqrt(&2)))`,
  GEN_TAC THEN ACCEPT_TAC(MATCH_MP APX_A13 (SPEC `u:A->bool` SMT_PRODUCT2)));;

let APX_A13_CORE_UNCOND = prove
 (`!u:A->bool.
     ?eps0. &0 < eps0 /\
       !top atlas g eps n x e.
          &0 < eps /\ eps <= eps0 /\ hausdorff_space top /\
          riemannian_metric atlas g /\
          apx_chain (top,atlas) g eps {i:int | &0 <= i /\ i <= &n} x
                    (e:int->real^3->A)
          ==> ?E L f f'.
                &0 <= L /\ sphere_diffeo f f' /\
                mfd_param top atlas (apx_slab (--inv eps) (L + inv eps)) E /\
                (!y. y IN apx_slab (--inv eps) (inv(&8 * eps)) ==> E y = e (&0) y) /\
                (!y. y IN apx_slab (L - inv(&8 * eps)) (L + inv eps)
                     ==> E y = e (&n) (radial_ext f (exp(--L / sqrt(&2)) % y))) /\
                IMAGE E (apx_slab (--inv eps) (L + inv eps)) =
                apx_chain_union eps {i:int | &0 <= i /\ i <= &n} e /\
                (!p. p IN IMAGE E (apx_slab (--inv eps) (L + inv eps))
                     ==> ?x e. rfs_neck (top,atlas) g eps x e /\
                               p IN IMAGE e (rfs_neck_dom eps) /\
                               IMAGE e (rfs_neck_dom eps) SUBSET
                               IMAGE E (apx_slab (--inv eps) (L + inv eps)))`,
  GEN_TAC THEN ACCEPT_TAC(MATCH_MP APX_A13_CORE (SPEC `u:A->bool` SMT_PRODUCT2)));;

(* ------------------------------------------------------------------------- *)
(* MT Lemma A.13 at the statement level: APX_A13_STATEMENT, in corrected     *)
(* form (hypothesis apx_sphere_sep, exact-end regions 1/(8 eps)), is the     *)
(* conclusion of APX_A13_UNCOND.                                             *)
(* ------------------------------------------------------------------------- *)

let APX_A13_THM = prove
 (`!u:A->bool. APX_A13_STATEMENT u`,
  REWRITE_TAC[APX_A13_STATEMENT; APX_A13_UNCOND]);;

