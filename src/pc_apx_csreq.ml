(* ========================================================================= *)
(* pc_apx_csreq: statement variants of the Appendix layer used in Ch 10: MT *)
(* Cor A.8 for constant-speed minimizers, and MT Lemma A.9 in a crude form  *)
(* for s-differences of at least 16/alpha.  Each is implied by the          *)
(* corresponding statement of pc_apx_defs (APX_A8_IMP_CS, APX_A9_IMP_CRUDE). *)
(* Statements and sanity theorems only.                                     *)
(* ========================================================================= *)

needs "src/pc_apx_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The statements and their implications from pc_apx_defs.                  *)
(* ------------------------------------------------------------------------- *)

(* MT Cor A.8 for constant-speed minimizers (MT: gamma is a minimal         *)
(* geodesic).  APX_A8_STATEMENT plus a < b and constant speed, as the       *)
(* constant-speed forms P2B_APX_A4_CS_STATEMENT etc. of pc_p2b_defs.        *)

let APX_A8_CS_STATEMENT = new_definition
 `APX_A8_CS_STATEMENT (u:A->bool) <=>
    ?eps1. &0 < eps1 /\
      !C top atlas g eps U Y x e gamma a b.
         &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
         riemannian_metric atlas g /\
         rfs_cap (top,atlas) g C eps U Y /\
         rfs_neck (top,atlas) g eps x (e:real^3->A) /\
         IMAGE e (rfs_neck_dom eps) = U DIFF top closure_of Y /\
         ~(top closure_of (IMAGE e (apx_slab (--inv eps) (&0))) INTER
           top closure_of Y = {}) /\
         apx_shortest (top,atlas) g gamma a b /\ a < b /\
         (!t. t IN real_interval[a,b]
              ==> mfd_speed atlas g gamma a b t = mfd_length atlas g gamma a b / (b - a)) /\
         (?t. a <= t /\ t <= b /\ gamma t IN Y)
         ==> ?c d. a <= c /\ c <= d /\ d <= b /\ (c = a \/ d = b) /\
                   !t. a <= t /\ t <= b
                       ==> (gamma t IN top closure_of Y UNION
                                       IMAGE e {y | y IN rfs_neck_dom eps /\ norm y <= &1}
                            <=> c <= t /\ t <= d)`;;

(* MT Lemma A.9, crude form: APX_A9_STATEMENT for s-differences of at least *)
(* 16/alpha (the additive error of the separating-sphere argument, about   *)
(* the diameter sqrt(2) pi of a neck sphere, is absorbed).  Enough for MT   *)
(* Claim 10.6, which integrates the quotients over whole necks.             *)

let APX_A9_CRUDE_STATEMENT = new_definition
 `APX_A9_CRUDE_STATEMENT (u:A->bool) <=>
    !alpha. &0 < alpha /\ alpha < &1
      ==> ?eps1. &0 < eps1 /\
            !top atlas g eps x e z w r1 r2.
               &0 < eps /\ eps <= eps1 /\ hausdorff_space top /\
               riemannian_metric atlas g /\ apx_sphere_sep top atlas /\
               rfs_neck (top,atlas) g eps x (e:real^3->A) /\
               apx_neg_side top e z /\
               ~(z IN IMAGE e (apx_slab (--(&2 / &3 * inv eps)) (&2 / &3 * inv eps))) /\
               w IN sphere(vec 0,&1) /\ r1 <= r2 /\
               r1 % w IN apx_slab (--inv(&2 * eps)) (inv(&2 * eps)) /\
               r2 % w IN rfs_neck_dom eps /\
               &16 / alpha <= apx_sval(r2 % w) - apx_sval(r1 % w) /\
               mfd_joinable (top,atlas) z (e(r1 % w))
               ==> (&1 - alpha) * inv(sqrt(mfd_scalar atlas g x)) *
                   (apx_sval(r2 % w) - apx_sval(r1 % w))
                   <= mfd_dist (top,atlas) g z (e(r2 % w)) -
                      mfd_dist (top,atlas) g z (e(r1 % w)) /\
                   mfd_dist (top,atlas) g z (e(r2 % w)) -
                   mfd_dist (top,atlas) g z (e(r1 % w))
                   <= (&1 + alpha) * inv(sqrt(mfd_scalar atlas g x)) *
                      (apx_sval(r2 % w) - apx_sval(r1 % w))`;;

(* Checks: the variants differ from the statements of pc_apx_defs exactly   *)
(* by the added hypotheses (the statements of pc_apx_defs imply them).      *)

let APX_A8_IMP_CS = prove
 (`!u:A->bool. APX_A8_STATEMENT u ==> APX_A8_CS_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A8_STATEMENT; APX_A8_CS_STATEMENT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "h" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let APX_A9_IMP_CRUDE = prove
 (`!u:A->bool. APX_A9_STATEMENT u ==> APX_A9_CRUDE_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[APX_A9_STATEMENT; APX_A9_CRUDE_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "h") THEN X_GEN_TAC `alpha:real` THEN DISCH_TAC THEN
  REMOVE_THEN "h" (MP_TAC o SPEC `alpha:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "h")) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN USE_THEN "h" MATCH_MP_TAC THEN
  EXISTS_TAC `eps:real` THEN ASM_REWRITE_TAC[]);;

