(* ========================================================================= *)
(* Unit pc_cmr_l312 (a unit of the replacement chain of pc_cm_replacement):  *)
(* CM 2008 Lemma 3.11, inequalities (3.12) and (3.13), in the G-weighted     *)
(* setting, for slices of energy above the type-X threshold.                 *)
(*                                                                           *)
(* The context, the one-cap energy decrease cmr_dec and its                  *)
(* basic facts, energy bounds for disjoint families.                        *)
(* ========================================================================= *)

needs "src/pc_cmr_pball.ml";;

prioritize_real();;
type_invention_error := true;;

(* The context: target, replacement threshold e with small-energy           *)
(* regularity and convexity available at energies up to e.                  *)

let cmr_ctx = new_definition
 `cmr_ctx S (G:real^K->real^K^K) d e <=>
    cm_target S G d /\ cmw_repex S G e /\ &0 < e /\
    (?e0 (C:num->real).
       e <= e0 /\ (!k. &0 < C k) /\
       !(a:real^2) r (u:real^2->real^K) l x.
          &0 < r /\ cm_harmonic S G (ball(a,r)) u /\ wan_w12 (ball(a,r)) u /\
          wan_gdir (ball(a,r)) G u <= e0 /\
          ALL (\i. 1 <= i /\ i <= 2) l /\ ~(l = []) /\ x IN ball(a,r / &2)
          ==> r pow (LENGTH l) * norm(iterated_partial l u x)
              <= C (LENGTH l) * sqrt(wan_gdir (ball(a,r)) G u)) /\
    (?ec cc.
       e <= ec /\ &0 < cc /\
       !(a:real^2) r (u:real^2->real^K) v.
          &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ cm_wmap S (ball(a,r)) v /\
          wan_gdir (ball(a,r)) G v <= ec /\ cm_wmap S (ball(a,r)) u /\
          wan_w120 (ball(a,r)) (\x. u x - v x)
          ==> cc * wan_dir (ball(a,r)) (\x. u x - v x)
              <= wan_gdir (ball(a,r)) G u - wan_gdir (ball(a,r)) G v)`;;

(* The energy decrease from replacement on one cap.                         *)

let cmr_dec = new_definition
 `cmr_dec S (G:real^K->real^K^K) (Q:real^3^3) (c:real^2) r (u:real^3->real^K) =
    cm_gen G (ball(c,r)) (\x. u(cm_capmap Q x)) -
    cm_gen G (ball(c,r)) (cmr_minw S G c r (\x. u(cm_capmap Q x)))`;;

let CMR_DEC_FACTS = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ orthogonal_matrix Q /\
     &0 < r /\ wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> &0 <= cmr_dec S G Q c r u /\
         cmr_dec S G Q c r u <= cm_gen G (ball(c,r)) (\x. u(cm_capmap Q x)) /\
         cm_sen G (cmr_rep1 S G Q c r u) = cm_sen G u - cmr_dec S G Q c r u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cmr_dec] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`;
                 `c:real^2`; `r:real`; `u:real^3->real^K`; `Lam:real`] CMR_REP1_SEN_LE) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Q:real^3^3`;
                 `c:real^2`; `r:real`; `u:real^3->real^K`; `Lam:real`] CMR_REP1_SEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> a - b <= a`) THEN
  REWRITE_TAC[cm_gen] THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x / &2`) THEN
  MP_TAC(ASSUME `CMR_GCOND (G:real^K->real^K^K) Lam`) THEN REWRITE_TAC[CMR_GCOND] THEN
  STRIP_TAC THEN MATCH_MP_TAC CMW_GDIR_POS THEN EXISTS_TAC `Lam:real` THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real^2`; `r:real`;
                 `\x. (u:real^3->real^K)(cm_capmap Q x)`] CMR_MINW_WORKS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[];
    SIMP_TAC[cm_cmap]]);;

(* Decreases are monotone in the radius.                                    *)

let CMR_DEC_MONO = prove
 (`!S (G:real^K->real^K^K) e Lam (Q:real^3^3) (c:real^2) r r' (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ orthogonal_matrix Q /\
     &0 < r' /\ r' <= r /\ wan_gdir (ball(c,r)) G (\x. u(cm_capmap Q x)) <= e
     ==> cmr_dec S G Q c r' u <= cmr_dec S G Q c r u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(c:real^2,r')) G (\x. (u:real^3->real^K)(cm_capmap Q x)) <= e`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball(c:real^2,r)) G (\x. (u:real^3->real^K)(cm_capmap Q x))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `Q:real^3^3`; `c:real^2`;
                     `r:real`] CMR_CHART_CMAP) THEN ASM_SIMP_TAC[cm_cmap]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r:real`; `r':real`; `u:real^3->real^K`] CMR_REP1_MONO) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r:real`; `u:real^3->real^K`] CMR_DEC_FACTS) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `r':real`; `u:real^3->real^K`] CMR_DEC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `cm_sen G (cmr_rep1 S G Q (c:real^2) r (u:real^3->real^K)) <=
               cm_sen G (cmr_rep1 S G Q c r' u)` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The energy formula for replacement on a disjoint family.                 *)

let CMR_REPN_DEC_SUM = prove
 (`!S (G:real^K->real^K^K) e Lam n Q (c:num->real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ cmr_dfam n Q c r /\
     (!k. 1 <= k /\ k <= n /\ &0 < r k
          ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) <= e)
     ==> cm_smap S (cmr_repn S G n Q c r u) /\
         cm_sen G (cmr_repn S G n Q c r u) =
         cm_sen G u -
         sum(1..n) (\k. if &0 < r k then cmr_dec S G (Q k) (c k) (r k) u else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u:real^3->real^K`]
                CMR_REPN_FACTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[cmr_dec]);;

(* The energy of one cap of a family is at most the energy on the union of *)
(* its open caps.                                                           *)

let CMR_FAM_CAP_BOUND = prove
 (`!(G:real^K->real^K^K) Lam (f:real^3->real^K) n Q (c:num->real^2) r k.
     CMR_GCOND G Lam /\ wan_s2_w12 f /\ cmr_dfam n Q c r /\ 1 <= k /\ k <= n
     ==> cm_gen G (ball(c k,r k)) (\x. f(cm_capmap (Q k) x)) <=
         cmr_sen_on G f (cmr_fop n Q c r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `f:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] CMR_SEN_FAM_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= n
        ==> &0 <= cm_gen G (ball((c:num->real^2) j,r j))
                       (\x. (f:real^3->real^K)(cm_capmap ((Q:num->real^3^3) j) x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `orthogonal_matrix((Q:num->real^3^3) j)` ASSUME_TAC THENL
     [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `f:real^3->real^K`; `(Q:num->real^3^3) j`;
                   `Lam:real`; `ball((c:num->real^2) j,r j)`] CMR_CAP_EN) THEN
    ASM_REWRITE_TAC[OPEN_BALL; GSYM cm_gen] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `f:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CMR_CONE_OPEN THEN
    ASM_SIMP_TAC[CMR_CAP_OPEN_IN; OPEN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{k:num}`; `1..n`;
                 `\j. cm_gen G (ball((c:num->real^2) j,r j))
                        (\x. (f:real^3->real^K)(cm_capmap ((Q:num->real^3^3) j) x))`]
                SUM_SUBSET_SIMPLE) THEN
  REWRITE_TAC[SUM_SING; FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SING_SUBSET; IN_NUMSEG; IN_DIFF] THEN ASM_MESON_TAC[]);;

(* The energy of H(u,F1) on the open caps of F2.                            *)

let CMR_REPN_FOP_BOUND = prove
 (`!S (G:real^K->real^K^K) e Lam n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
    (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ cmr_dfam n1 Q1 c1 r1 /\
     cmr_dfam n2 Q2 c2 r2 /\
     (!k. 1 <= k /\ k <= n1 /\ &0 < r1 k
          ==> wan_gdir (ball(c1 k,r1 k)) G (\x. u(cm_capmap (Q1 k) x)) <= e)
     ==> cmr_sen_on G (cmr_repn S G n1 Q1 c1 r1 u) (cmr_fop n2 Q2 c2 r2) <=
         cmr_sen_on G u (cmr_fop n2 Q2 c2 r2) + cmr_sen_on G u (cmr_fop n1 Q1 c1 r1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`] CMR_SEN_FAM_SUM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC CMR_REPN_SEN_ON_LE THEN
  MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CMR_FOP_OPEN_IN THEN ASM_MESON_TAC[cmr_dfam]);;


(* ========================================================================= *)
(* Summing the per-ball inequality (CMR_PBALL) over a set J of               *)
(* caps of a family.                                                        *)
(* ========================================================================= *)

let cmr_pbok = new_definition
 `cmr_pbok S (G:real^K->real^K^K) e Cp tau <=>
   !(c:real^2) R (v:real^2->real^K) v1.
     &0 < R /\ cm_cmap S (ball(c,R)) v /\ cm_cmap S (ball(c,R)) v1 /\
     wan_gdir (ball(c,R)) G v <= e /\ wan_gdir (ball(c,R)) G v1 <= e /\
     wan_dir (ball(c,R)) (\x. v1 x - v x) <= tau /\
     (!rho. R / &2 < rho /\ rho < R ==> ?x. x IN sphere(c,rho) /\ v x = v1 x)
     ==> ?rho. R / &2 < rho /\ rho < R /\
           cm_gen G (ball(c,rho)) v1 - cm_gen G (ball(c,rho)) (cmr_minw S G c rho v)
           <= (cm_gen G (ball(c,R)) v1 - cm_gen G (ball(c,R)) (cmr_minw S G c R v1)) +
              Cp * sqrt(wan_dir (ball(c,R)) v + wan_dir (ball(c,R)) v1) *
              sqrt(wan_dir (ball(c,R)) (\x. v1 x - v x))`;;

let CMR_PBOK_EXISTS = prove
 (`!S (G:real^K->real^K^K) d e.
     cm_target S G d /\ cmw_repex S G e
     ==> ?Cp tau. &0 < Cp /\ &0 < tau /\ cmr_pbok S G e Cp tau`,
  REWRITE_TAC[cmr_pbok] THEN MATCH_ACCEPT_TAC CMR_PBALL);;

(* One cap: the decrease of a on the half disc against the decrease of b   *)
(* on the disc.                                                             *)

let CMR_PBALL_ONE = prove
 (`!S (G:real^K->real^K^K) e Lam Cp tau (Q:real^3^3) (c:real^2) R (a:real^3->real^K) b.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cmr_pbok S G e Cp tau /\
     cm_smap S a /\ cm_smap S b /\ orthogonal_matrix Q /\ &0 < R /\
     wan_gdir (ball(c,R)) G (\x. a(cm_capmap Q x)) <= e /\
     wan_gdir (ball(c,R)) G (\x. b(cm_capmap Q x)) <= e /\
     wan_dir (ball(c,R)) (\x. b(cm_capmap Q x) - a(cm_capmap Q x)) <= tau /\
     (!rho. R / &2 < rho /\ rho < R
            ==> ?x. x IN sphere(c,rho) /\ a(cm_capmap Q x) = b(cm_capmap Q x))
     ==> ?rho. R / &2 < rho /\ rho < R /\
           cmr_dec S G Q c (R / &2) a
           <= cmr_dec S G Q c R b +
              (cm_gen G (ball(c,rho)) (\x. a(cm_capmap Q x)) -
               cm_gen G (ball(c,rho)) (\x. b(cm_capmap Q x))) +
              Cp * sqrt(wan_dir (ball(c,R)) (\x. a(cm_capmap Q x)) +
                        wan_dir (ball(c,R)) (\x. b(cm_capmap Q x))) *
              sqrt(wan_dir (ball(c,R)) (\x. b(cm_capmap Q x) - a(cm_capmap Q x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_pbok S (G:real^K->real^K^K) e Cp tau` THEN REWRITE_TAC[cmr_pbok] THEN
  DISCH_THEN(MP_TAC o SPECL [`c:real^2`; `R:real`; `\x. (a:real^3->real^K)(cm_capmap Q x)`;
                             `\x. (b:real^3->real^K)(cm_capmap Q x)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < rho /\ R / &2 <= rho /\ &0 < R / &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(c:real^2,rho)) G (\x. (a:real^3->real^K)(cm_capmap Q x)) <= e`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball(c:real^2,R)) G (\x. (a:real^3->real^K)(cm_capmap Q x))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`S:real^K->bool`; `a:real^3->real^K`; `Q:real^3^3`; `c:real^2`;
                     `R:real`] CMR_CHART_CMAP) THEN ASM_SIMP_TAC[cm_cmap]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Q:real^3^3`;
                 `c:real^2`; `rho:real`; `R / &2`; `a:real^3->real^K`] CMR_DEC_MONO) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `cm_gen G (ball(c:real^2,rho)) (\x. (b:real^3->real^K)(cm_capmap Q x)) -
    cm_gen G (ball(c,rho)) (cmr_minw S G c rho (\x. (a:real^3->real^K)(cm_capmap Q x)))
    <= (cm_gen G (ball(c,R)) (\x. b(cm_capmap Q x)) -
        cm_gen G (ball(c,R)) (cmr_minw S G c R (\x. b(cm_capmap Q x)))) +
       Cp * sqrt(wan_dir (ball(c,R)) (\x. a(cm_capmap Q x)) +
                 wan_dir (ball(c,R)) (\x. b(cm_capmap Q x))) *
       sqrt(wan_dir (ball(c,R)) (\x. b(cm_capmap Q x) - a(cm_capmap Q x)))` THEN
  REWRITE_TAC[cmr_dec] THEN REAL_ARITH_TAC);;

(* The sum over a set J of caps.                                             *)

let CMR_PBALL_SUM = prove
 (`!S (G:real^K->real^K^K) e Lam Cp tau n (Q:num->real^3^3) (c:num->real^2) R J
    (a:real^3->real^K) b.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cmr_pbok S G e Cp tau /\ &0 <= Cp /\
     cm_smap S a /\ cm_smap S b /\
     (!j. 1 <= j /\ j <= n ==> orthogonal_matrix(Q j)) /\
     (!j. 1 <= j /\ j <= n /\ J j
          ==> &0 < R j /\
              wan_gdir (ball(c j,R j)) G (\x. a(cm_capmap (Q j) x)) <= e /\
              wan_gdir (ball(c j,R j)) G (\x. b(cm_capmap (Q j) x)) <= e /\
              wan_dir (ball(c j,R j)) (\x. b(cm_capmap (Q j) x) - a(cm_capmap (Q j) x))
              <= tau /\
              (!rho. R j / &2 < rho /\ rho < R j
                     ==> ?x. x IN sphere(c j,rho) /\
                             a(cm_capmap (Q j) x) = b(cm_capmap (Q j) x)))
     ==> ?rho. (!j. 1 <= j /\ j <= n /\ J j ==> R j / &2 < rho j /\ rho j < R j) /\
           sum(1..n) (\j. if J j then cmr_dec S G (Q j) (c j) (R j / &2) a else &0)
           <= sum(1..n) (\j. if J j then cmr_dec S G (Q j) (c j) (R j) b else &0) +
              sum(1..n) (\j. if J j
                             then cm_gen G (ball(c j,rho j)) (\x. a(cm_capmap (Q j) x)) -
                                  cm_gen G (ball(c j,rho j)) (\x. b(cm_capmap (Q j) x))
                             else &0) +
              Cp * sqrt(sum(1..n) (\j. if J j
                                       then wan_dir (ball(c j,R j))
                                              (\x. a(cm_capmap (Q j) x)) +
                                            wan_dir (ball(c j,R j))
                                              (\x. b(cm_capmap (Q j) x))
                                       else &0)) *
                   sqrt(sum(1..n) (\j. if J j
                                       then wan_dir (ball(c j,R j))
                                              (\x. b(cm_capmap (Q j) x) -
                                                   a(cm_capmap (Q j) x))
                                       else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `XX = \j. wan_dir (ball((c:num->real^2) j,R j))
                         (\x. (a:real^3->real^K)(cm_capmap ((Q:num->real^3^3) j) x)) +
                       wan_dir (ball(c j,R j)) (\x. (b:real^3->real^K)(cm_capmap (Q j) x))` THEN
  ABBREV_TAC `YY = \j. wan_dir (ball((c:num->real^2) j,R j))
                         (\x. (b:real^3->real^K)(cm_capmap ((Q:num->real^3^3) j) x) -
                              (a:real^3->real^K)(cm_capmap (Q j) x))` THEN
  SUBGOAL_THEN
   `!j. ?r. 1 <= j /\ j <= n /\ J j
            ==> R j / &2 < r /\ r < R j /\
                cmr_dec S G ((Q:num->real^3^3) j) ((c:num->real^2) j) (R j / &2)
                  (a:real^3->real^K)
                <= cmr_dec S G (Q j) (c j) (R j) (b:real^3->real^K) +
                   (cm_gen G (ball(c j,r)) (\x. a(cm_capmap (Q j) x)) -
                    cm_gen G (ball(c j,r)) (\x. b(cm_capmap (Q j) x))) +
                   Cp * sqrt((XX:num->real) j) * sqrt((YY:num->real) j)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN ASM_CASES_TAC `1 <= j /\ j <= n /\ (J:num->bool) j` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["XX"; "YY"] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CMR_PBALL_ONE THEN EXISTS_TAC `e:real` THEN EXISTS_TAC `Lam:real` THEN
    EXISTS_TAC `tau:real` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `rho:num->real`) THEN
  EXISTS_TAC `rho:num->real` THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= n /\ J j ==> &0 <= (XX:num->real) j /\ &0 <= (YY:num->real) j`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["XX"; "YY"] THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (R:num->real) j /\ orthogonal_matrix((Q:num->real^3^3) j)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `a:real^3->real^K`; `(Q:num->real^3^3) j`;
                   `(c:num->real^2) j`; `(R:num->real) j`] CMR_CHART_CMAP) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `b:real^3->real^K`; `(Q:num->real^3^3) j`;
                   `(c:num->real^2) j`; `(R:num->real) j`] CMR_CHART_CMAP) THEN
    ASM_REWRITE_TAC[cm_cmap] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[WAN_DIR_POS; REAL_LE_ADD; WAN_W12_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(1..n) (\j. (if J j then cmr_dec S G ((Q:num->real^3^3) j) ((c:num->real^2) j) (R j)
                                 (b:real^3->real^K) else &0) +
                   (if J j
                    then cm_gen G (ball(c j,rho j)) (\x. (a:real^3->real^K)(cm_capmap (Q j) x)) -
                         cm_gen G (ball(c j,rho j)) (\x. b(cm_capmap (Q j) x))
                    else &0) +
                   Cp * (sqrt(if J j then (XX:num->real) j else &0) *
                         sqrt(if J j then (YY:num->real) j else &0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[SQRT_0; REAL_MUL_RZERO; REAL_ADD_RID; REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
      check (fun th -> is_forall(concl th) && free_in `rho:num->real` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `c <= d ==> a + b + c <= a + b + d`) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXPAND_TAC ["XX"; "YY"] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC CMR_SUM_SQRT_CS THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
    check (fun th -> is_forall(concl th) && free_in `XX:num->real` (concl th) &&
                     not (free_in `rho:num->real` (concl th)))) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["XX"; "YY"] THEN REWRITE_TAC[]);;

(* ========================================================================= *)
(* The hypotheses of Lemma 3.11 in our setting: two disjoint families with  *)
(* energy at most e/4 on their open caps, and total energy above e/2 (so    *)
(* that no cap of one family together with a disc of the other covers S^2). *)
(* ========================================================================= *)

let cmr_l3hyp = new_definition
 `cmr_l3hyp S (G:real^K->real^K^K) e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
            (u:real^3->real^K) <=>
    cm_smap S u /\ cmr_dfam n1 Q1 c1 r1 /\ cmr_dfam n2 Q2 c2 r2 /\
    cmr_sen_on G u (cmr_fop n1 Q1 c1 r1) <= e / &4 /\
    cmr_sen_on G u (cmr_fop n2 Q2 c2 r2) <= e / &4 /\
    e / &2 < cm_sen G u`;;

(* Per-cap energy bounds.                                                    *)

let CMR_L3_CAPS = prove
 (`!S (G:real^K->real^K^K) e Lam n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
    (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < e /\
     cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
     ==> (!k. 1 <= k /\ k <= n1
              ==> cm_gen G (ball(c1 k,r1 k)) (\x. u(cm_capmap (Q1 k) x)) <= e / &4 /\
                  wan_gdir (ball(c1 k,r1 k)) G (\x. u(cm_capmap (Q1 k) x)) <= e / &2) /\
         (!k. 1 <= k /\ k <= n2
              ==> cm_gen G (ball(c2 k,r2 k)) (\x. u(cm_capmap (Q2 k) x)) <= e / &4 /\
                  wan_gdir (ball(c2 k,r2 k)) G (\x. u(cm_capmap (Q2 k) x)) <= e / &2) /\
         cm_smap S (cmr_repn S G n1 Q1 c1 r1 u) /\
         cmr_sen_on G (cmr_repn S G n1 Q1 c1 r1 u) (cmr_fop n2 Q2 c2 r2) <= e / &2 /\
         (!k. 1 <= k /\ k <= n2
              ==> wan_gdir (ball(c2 k,r2 k)) G
                    (\x. cmr_repn S G n1 Q1 c1 r1 u (cm_capmap (Q2 k) x)) <= e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_s2_w12 (u:real^3->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (a ==> c /\ d /\ e) ==> a /\ b /\ c /\ d /\ e`) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop n1 Q1 (c1:num->real^2) r1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_FAM_CAP_BOUND THEN
      EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x / &2 <= e / &4 ==> x <= e / &2`) THEN
      REWRITE_TAC[GSYM cm_gen] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop n1 Q1 (c1:num->real^2) r1)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_FAM_CAP_BOUND THEN
      EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop n2 Q2 (c2:num->real^2) r2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_FAM_CAP_BOUND THEN
      EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x / &2 <= e / &4 ==> x <= e / &2`) THEN
      REWRITE_TAC[GSYM cm_gen] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop n2 Q2 (c2:num->real^2) r2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_FAM_CAP_BOUND THEN
      EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n1 /\ &0 < r1 k
        ==> wan_gdir (ball((c1:num->real^2) k,r1 k)) G
              (\x. (u:real^3->real^K)(cm_capmap ((Q1:num->real^3^3) k) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`]
                CMR_REPN_DEC_SUM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop n2 Q2 (c2:num->real^2) r2) +
                cmr_sen_on G u (cmr_fop n1 Q1 (c1:num->real^2) r1)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC CMR_REPN_FOP_BOUND THEN
    MAP_EVERY EXISTS_TAC [`e:real`; `Lam:real`] THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x / &2 <= e / &2 ==> x <= e`) THEN
    REWRITE_TAC[GSYM cm_gen] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cmr_sen_on G (cmr_repn S G n1 Q1 c1 r1 (u:real^3->real^K))
                  (cmr_fop n2 Q2 (c2:num->real^2) r2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CMR_FAM_CAP_BOUND THEN
    EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cm_smap]]);;

(* Circles around a cap of F2 that is not inside any open cap of F1 carry a *)
(* point where u and H(u,F1) agree (no type-X configuration: e/2 < E(u)).  *)

let CMR_L3_ZERO = prove
 (`!S (G:real^K->real^K^K) e Lam n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
    (u:real^3->real^K) j s rho.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < e /\
     cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u /\
     1 <= j /\ j <= n2 /\ &0 < s /\ s <= rho /\ rho <= r2 j /\
     (!k. 1 <= k /\ k <= n1 /\ &0 < r1 k
          ==> ~(IMAGE (cm_capmap (Q2 j)) (cball(c2 j,s)) SUBSET
                IMAGE (cm_capmap (Q1 k)) (ball(c1 k,r1 k))))
     ==> ?x. x IN sphere(c2 j,rho) /\
             u(cm_capmap (Q2 j) x) = cmr_repn S G n1 Q1 c1 r1 u (cm_capmap (Q2 j) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_l3hyp S G e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                 (u:real^3->real^K)` THEN
  REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `orthogonal_matrix((Q2:num->real^3^3) j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`;
                 `(Q2:num->real^3^3) j`; `(c2:num->real^2) j`; `s:real`; `rho:real`]
                CMR_CIRCLE_MEETS_OFF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`;
                   `(Q1:num->real^3^3) k`; `(c1:num->real^2) k`; `(r1:num->real) k`;
                   `(Q2:num->real^3^3) j`; `(c2:num->real^2) j`; `rho:real`]
                  CMR_TWO_CAPS_COVER) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap; cmr_dfam]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `e / &2 < s /\ a <= e / &4 /\ b <= e / &4 ==> s <= a + b ==> F`) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `cm_gen G (ball((c2:num->real^2) j,r2 j))
                  (\x. (u:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) j) x))` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[cm_gen] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> a / &2 <= b / &2`) THEN
    MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
    ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `(Q2:num->real^3^3) j`;
                     `(c2:num->real^2) j`; `(r2:num->real) j`] CMR_CHART_CMAP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[cm_cmap]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `y IN IMAGE (cm_capmap ((Q2:num->real^3^3) j)) (sphere((c2:num->real^2) j,rho))` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`]
                CMR_REPN_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n1:num`) THEN REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `~(y IN cmr_fop n1 Q1 (c1:num->real^2) r1)` THEN
  ASM_REWRITE_TAC[cmr_fop; IN_ELIM_THM] THEN MESON_TAC[]);;


(* ========================================================================= *)
(* The constants of the context (stability, convexity of the                 *)
(* change, per-ball inequality) and the bounds for the sums in Lemma 3.11.  *)
(* ========================================================================= *)

let cmr_stabok = new_definition
 `cmr_stabok S (G:real^K->real^K^K) e CS <=>
    !n (Q:num->real^3^3) (c:num->real^2) (r:num->real) (u:real^3->real^K) W.
      cm_smap S u /\
      (!k. 1 <= k /\ k <= n ==> orthogonal_matrix(Q k)) /\
      (!k l. 1 <= k /\ k < l /\ l <= n /\ &0 < r k /\ &0 < r l
             ==> DISJOINT (IMAGE (cm_capmap (Q k)) (cball(c k,r k)))
                          (IMAGE (cm_capmap (Q l)) (cball(c l,r l)))) /\
      (!k. 1 <= k /\ k <= n /\ &0 < r k
           ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) <= e) /\
      open_in (subtopology euclidean (sphere(vec 0,&1))) W
      ==> abs(cmr_sen_on G (cmr_repn S G n Q c r u) W - cmr_sen_on G u W)
          <= CS * sqrt(cm_sen G u - cm_sen G (cmr_repn S G n Q c r u)) *
             sqrt(sum(1..n) (\k. if &0 < r k
                                 then wan_gdir (ball(c k,r k)) G
                                        (\x. u(cm_capmap (Q k) x)) +
                                      wan_gdir (ball(c k,r k)) G
                                        (\x. u(cm_capmap (Q k) x)) pow 2
                                 else &0))`;;

let cmr_dirok = new_definition
 `cmr_dirok S (G:real^K->real^K^K) e cc <=>
    !n (Q:num->real^3^3) (c:num->real^2) (r:num->real) (u:real^3->real^K).
      cm_smap S u /\ cmr_dfam n Q c r /\
      (!k. 1 <= k /\ k <= n /\ &0 < r k
           ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) <= e)
      ==> cc * cm_sen (\y:real^K. mat 1) (\y. cmr_repn S G n Q c r u y - u y)
          <= cm_sen G u - cm_sen G (cmr_repn S G n Q c r u)`;;

let CMR_CTX_UNPACK = prove
 (`!S (G:real^K->real^K^K) d e.
     cmr_ctx S G d e
     ==> cm_target S G d /\ cmw_repex S G e /\ &0 < e /\
         ?lam Lam cc CS Cp tau.
           &0 < lam /\ CMR_GCOND G Lam /\ (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\
           &0 < cc /\ cmr_dirok S G e cc /\ &0 < CS /\ cmr_stabok S G e CS /\
           &0 < Cp /\ &0 < tau /\ cmr_pbok S G e Cp tau`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cmr_ctx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CMW_TARGET_FACTS) THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Lg:real` STRIP_ASSUME_TAC o MATCH_MP CMR_TARGET_GCOND) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e0:real`; `C:num->real`;
                 `e:real`; `ec:real`; `cc:real`] CMR_REPN_STAB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `CS:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `e:real`]
                CMR_PBOK_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cp:real` (X_CHOOSE_THEN `tau:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `Lg:real`; `cc:real`; `CS:real`; `Cp:real`; `tau:real`] THEN
  ASM_REWRITE_TAC[cmr_stabok] THEN REWRITE_TAC[cmr_dirok] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CMR_REPN_DIR_CHANGE THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `e:real`; `ec:real`; `lam:real`; `Lam:real`] THEN
  ASM_REWRITE_TAC[]);;

(* The Dirichlet energy of H(u,F1) - u on the caps of any disjoint family.  *)

let CMR_L3_SUMY = prove
 (`!S (G:real^K->real^K^K) e Lam cc n1 Q1 (c1:num->real^2) r1 n Q (c:num->real^2) R
    (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cmr_dirok S G e cc /\ &0 < cc /\
     cm_smap S u /\ cmr_dfam n1 Q1 c1 r1 /\
     (!k. 1 <= k /\ k <= n1 /\ &0 < r1 k
          ==> wan_gdir (ball(c1 k,r1 k)) G (\x. u(cm_capmap (Q1 k) x)) <= e) /\
     cmr_dfam n Q c R
     ==> cc * sum(1..n) (\j. wan_dir (ball(c j,R j))
                               (\x. cmr_repn S G n1 Q1 c1 r1 u (cm_capmap (Q j) x) -
                                    u(cm_capmap (Q j) x)))
         <= &2 * (cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`]
                CMR_REPN_DEC_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  UNDISCH_TAC `cmr_dirok S (G:real^K->real^K^K) e cc` THEN REWRITE_TAC[cmr_dirok] THEN
  DISCH_THEN(MP_TAC o SPECL [`n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`;
                             `r1:num->real`; `u:real^3->real^K`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `u1 = cmr_repn S G n1 Q1 (c1:num->real^2) r1 (u:real^3->real^K)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `wan_s2_w12 (\y. (u1:real^3->real^K) y - u y)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_S2_W12_SUB THEN ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `&1`; `\y. (u1:real^3->real^K) y - u y`;
                 `n:num`; `Q:num->real^3^3`; `c:num->real^2`; `R:num->real`]
                CMR_SEN_FAM_SUM) THEN
  REWRITE_TAC[CMR_GCOND_ID] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`\y:real^K. mat 1:real^K^K`; `\y. (u1:real^3->real^K) y - u y`; `&1`]
                CMR_SEN_ON_BASICS) THEN
  REWRITE_TAC[CMR_GCOND_ID] THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `sphere(vec 0:real^3,&1) DIFF cmr_fcl n Q (c:num->real^2) R` o
             CONJUNCT1 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CMR_CONE_OPEN THEN
    MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN REWRITE_TAC[CMR_FCL_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n) (\j. wan_dir (ball((c:num->real^2) j,R j))
                     (\x. (u1:real^3->real^K)(cm_capmap ((Q:num->real^3^3) j) x) -
                          u(cm_capmap (Q j) x))) =
    &2 * sum(1..n) (\j. cm_gen (\y:real^K. mat 1) (ball(c j,R j))
                          (\x. (\y. u1 y - u y) (cm_capmap (Q j) x)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; cm_gen; WAN_GDIR_ID] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `T0 = sum(1..n) (\k. cm_gen (\y:real^K. mat 1) (ball((c:num->real^2) k,R k))
                     (\x. (\y. (u1:real^3->real^K) y - u y) (cm_capmap ((Q:num->real^3^3) k) x)))` THEN
  ABBREV_TAC
   `T1 = cmr_sen_on (\y:real^K. mat 1) (\y. (u1:real^3->real^K) y - u y)
           (sphere(vec 0,&1) DIFF cmr_fcl n Q (c:num->real^2) R)` THEN
  ABBREV_TAC `T2 = cm_sen (\y:real^K. mat 1) (\y. (u1:real^3->real^K) y - u y)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `cc * T0 <= cc * T2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* The energy decrease from replacement on F1 is between 0 and e/4.        *)

let CMR_L3_DROP = prove
 (`!S (G:real^K->real^K^K) e Lam n Q (c:num->real^2) r (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ cm_smap S u /\ cmr_dfam n Q c r /\
     (!k. 1 <= k /\ k <= n /\ &0 < r k
          ==> wan_gdir (ball(c k,r k)) G (\x. u(cm_capmap (Q k) x)) <= e)
     ==> &0 <= cm_sen G u - cm_sen G (cmr_repn S G n Q c r u) /\
         cm_sen G u - cm_sen G (cmr_repn S G n Q c r u) <= cmr_sen_on G u (cmr_fop n Q c r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`; `u:real^3->real^K`]
                CMR_REPN_DEC_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  REWRITE_TAC[REAL_ARITH `u - (u - s) = s:real`] THEN
  MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `r:num->real`] CMR_SEN_FAM_SUM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                   `(Q:num->real^3^3) p`; `(c:num->real^2) p`; `(r:num->real) p`;
                   `u:real^3->real^K`] CMR_DEC_FACTS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[cmr_dfam]; SIMP_TAC[]];
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                     `(Q:num->real^3^3) k`; `(c:num->real^2) k`; `(r:num->real) k`;
                     `u:real^3->real^K`] CMR_DEC_FACTS) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[cmr_dfam]; SIMP_TAC[]];
      SUBGOAL_THEN `ball((c:num->real^2) k,r k) = {}` SUBST1_TAC THENL
       [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[CMR_CM_GEN_EMPTY; REAL_LE_REFL]]]]);;

(* The weight of the stability bound for F1.                                 *)

let CMR_L3_WDIFF = prove
 (`!S (G:real^K->real^K^K) e Lam CS n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
    (u:real^3->real^K) W.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < e /\ cmr_stabok S G e CS /\ &0 < CS /\
     cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u /\
     open_in (subtopology euclidean (sphere(vec 0,&1))) W
     ==> abs(cmr_sen_on G (cmr_repn S G n1 Q1 c1 r1 u) W - cmr_sen_on G u W)
         <= CS * sqrt(cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u)) *
            sqrt(e / &2 + e pow 2 / &4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_l3hyp S G e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                 (u:real^3->real^K)` THEN
  REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n1 /\ &0 < r1 k
        ==> wan_gdir (ball((c1:num->real^2) k,r1 k)) G
              (\x. (u:real^3->real^K)(cm_capmap ((Q1:num->real^3^3) k) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `cmr_stabok S (G:real^K->real^K^K) e CS` THEN REWRITE_TAC[cmr_stabok] THEN
  DISCH_THEN(MP_TAC o SPECL [`n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`;
                             `r1:num->real`; `u:real^3->real^K`; `W:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                   `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`]
                  CMR_L3_DROP) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + e / &2) *
              sum(1..n1) (\k. wan_gdir (ball((c1:num->real^2) k,r1 k)) G
                                (\x. (u:real^3->real^K)(cm_capmap ((Q1:num->real^3^3) k) x)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `&0 <= wan_gdir (ball((c1:num->real^2) k,r1 k)) G
              (\x. (u:real^3->real^K)(cm_capmap ((Q1:num->real^3^3) k) x)) /\
      wan_gdir (ball(c1 k,r1 k)) G (\x. u(cm_capmap (Q1 k) x)) <= e / &2`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `!k. 1 <= k /\ k <= n1
                       ==> cm_gen G (ball((c1:num->real^2) k,r1 k))
                             (\x. (u:real^3->real^K)(cm_capmap ((Q1:num->real^3^3) k) x))
                           <= e / &4 /\
                           wan_gdir (ball(c1 k,r1 k)) G (\x. u(cm_capmap (Q1 k) x))
                           <= e / &2` THEN
      DISCH_THEN(K ALL_TAC) THEN
      ASM_CASES_TAC `&0 < (r1:num->real) k` THENL
       [MP_TAC(ASSUME `CMR_GCOND (G:real^K->real^K^K) Lam`) THEN REWRITE_TAC[CMR_GCOND] THEN
        STRIP_TAC THEN MATCH_MP_TAC CMW_GDIR_POS THEN EXISTS_TAC `Lam:real` THEN
        ASM_REWRITE_TAC[OPEN_BALL] THEN
        MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `(Q1:num->real^3^3) k`;
                       `(c1:num->real^2) k`; `(r1:num->real) k`] CMR_CHART_CMAP) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[cmr_dfam]; SIMP_TAC[cm_cmap]];
        SUBGOAL_THEN `ball((c1:num->real^2) k,r1 k) = {}` SUBST1_TAC THENL
         [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[wan_gdir; INTEGRAL_EMPTY; DROP_VEC; SUM_0; REAL_LE_REFL]]];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [ALL_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN
     `wan_gdir (ball((c1:num->real^2) k,r1 k)) G
        (\x. (u:real^3->real^K)(cm_capmap ((Q1:num->real^3^3) k) x)) *
      wan_gdir (ball(c1 k,r1 k)) G (\x. u(cm_capmap (Q1 k) x)) <=
      (e / &2) * wan_gdir (ball(c1 k,r1 k)) G (\x. u(cm_capmap (Q1 k) x))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n1) (\k. wan_gdir (ball((c1:num->real^2) k,r1 k)) G
                      (\x. (u:real^3->real^K)(cm_capmap ((Q1:num->real^3^3) k) x))) =
    &2 * cmr_sen_on G u (cmr_fop n1 Q1 c1 r1)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`; `n1:num`;
                   `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`] CMR_SEN_FAM_SUM) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
    REWRITE_TAC[cm_gen; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cmr_sen_on G (u:real^3->real^K) (cmr_fop n1 Q1 (c1:num->real^2) r1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; ALL_TAC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    MATCH_MP_TAC CMR_CONE_OPEN THEN MATCH_MP_TAC CMR_FOP_OPEN_IN THEN
    ASM_MESON_TAC[cmr_dfam];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + e / &2) * (&2 * cmr_sen_on G (u:real^3->real^K) (cmr_fop n1 Q1 (c1:num->real^2) r1))
    <= (&1 + e / &2) * (&2 * e / &4)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* The sum of the Dirichlet energies of u and H(u,F1) on caps of F2 (on    *)
(* concentric discs of radii at most those of F2).                          *)

let CMR_L3_SUMX = prove
 (`!S (G:real^K->real^K^K) e lam Lam n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
    (u:real^3->real^K) (R:num->real) (J:num->bool).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < lam /\
     (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\ &0 < e /\
     cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u /\
     (!j. 1 <= j /\ j <= n2 ==> R j <= r2 j)
     ==> sum(1..n2) (\j. if J j
                         then wan_dir (ball(c2 j,R j)) (\x. u(cm_capmap (Q2 j) x)) +
                              wan_dir (ball(c2 j,R j))
                                (\x. cmr_repn S G n1 Q1 c1 r1 u (cm_capmap (Q2 j) x))
                         else &0)
         <= (&3 * e / &2) / lam`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u1 = cmr_repn S G n1 Q1 (c1:num->real^2) r1 (u:real^3->real^K)` THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_l3hyp S G e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                 (u:real^3->real^K)` THEN
  REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `CMR_GCOND (G:real^K->real^K^K) Lam`) THEN REWRITE_TAC[CMR_GCOND] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!f:real^3->real^K. cm_smap S f
      ==> !j. 1 <= j /\ j <= n2
              ==> &0 <= wan_gdir (ball((c2:num->real^2) j,r2 j)) G
                          (\x. f(cm_capmap ((Q2:num->real^3^3) j) x)) /\
                  wan_dir (ball(c2 j,R j)) (\x. f(cm_capmap (Q2 j) x)) <=
                  inv lam * wan_gdir (ball(c2 j,r2 j)) G (\x. f(cm_capmap (Q2 j) x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:real^3->real^K` THEN DISCH_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 < (r2:num->real) j` THENL
     [ALL_TAC;
      SUBGOAL_THEN `ball((c2:num->real^2) j,r2 j) = {} /\ ball(c2 j,R j) = {}`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[BALL_EQ_EMPTY] THEN
        SUBGOAL_THEN `(R:num->real) j <= r2 j` MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[wan_gdir; wan_dir; INTEGRAL_EMPTY; DROP_VEC; SUM_0; REAL_LE_REFL;
                    REAL_MUL_RZERO]]] THEN
    SUBGOAL_THEN `orthogonal_matrix((Q2:num->real^3^3) j)` ASSUME_TAC THENL
     [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `f:real^3->real^K`; `(Q2:num->real^3^3) j`;
                   `(c2:num->real^2) j`; `(r2:num->real) j`] CMR_CHART_CMAP) THEN
    ASM_REWRITE_TAC[cm_cmap] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ball((c2:num->real^2) j,r2 j)`; `G:real^K->real^K^K`;
                   `\x. (f:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) j) x)`;
                   `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
    ASM_SIMP_TAC[OPEN_BALL; REAL_LT_IMP_LE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_dir (ball((c2:num->real^2) j,r2 j))
                  (\x. (f:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) j) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_DIR_MONO_P THEN REWRITE_TAC[OPEN_BALL] THEN
      ASM_SIMP_TAC[SUBSET_BALL; CMR_W12_PARTIALS];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `inv lam * (sum(1..n2) (\j. wan_gdir (ball((c2:num->real^2) j,r2 j)) G
                                 (\x. (u:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) j) x))) +
               sum(1..n2) (\j. wan_gdir (ball(c2 j,r2 j)) G
                                 (\x. (u1:real^3->real^K)(cm_capmap (Q2 j) x))))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `j:num` (MATCH_MP th (ASSUME `cm_smap S (u:real^3->real^K)`))) THEN
      MP_TAC(SPEC `j:num` (MATCH_MP th (ASSUME `cm_smap S (u1:real^3->real^K)`)))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^3->real^K. cm_smap S f
      ==> sum(1..n2) (\j. wan_gdir (ball((c2:num->real^2) j,r2 j)) G
                            (\x. f(cm_capmap ((Q2:num->real^3^3) j) x))) =
          &2 * cmr_sen_on G f (cmr_fop n2 Q2 c2 r2)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `f:real^3->real^K`; `n2:num`;
                   `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`] CMR_SEN_FAM_SUM) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
    REWRITE_TAC[cm_gen; GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(&3 * e / &2) / lam = inv lam * (&3 * e / &2)` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  ASM_REAL_ARITH_TAC);;


(* ========================================================================= *)
(* CM (3.12).                                                                *)
(* ========================================================================= *)

(* The real arithmetic of the case analysis.                                *)

let CMR_L312_ARITH = prove
 (`!Dl P M a b C1 e cc tau kappa.
     &0 < e /\ &0 < cc /\ &0 < tau /\ &0 <= C1 /\ &0 <= a /\ &0 <= b /\
     &0 <= Dl /\ Dl <= e / &4 /\ Dl = P + M /\ P <= a /\
     (cc * tau / &2 < a \/ M <= b + C1 * sqrt a) /\
     kappa = min (min (&2 / e) ((cc * tau / &2) / (e / &4) pow 2))
                 (min (inv(&4 * (&1 + C1) pow 2)) (inv((e / &4) pow 2)))
     ==> kappa * Dl pow 2 <= a + b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= Dl pow 2 /\ Dl pow 2 <= (e / &4) pow 2 /\ Dl pow 2 <= (e / &4) * Dl`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (e / &4) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `Dl <= &2 * P` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 / e) * Dl pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 / e) * ((e / &4) * Dl)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&2 / e) * ((e / &4) * Dl) = Dl / &2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((cc * tau / &2) / (e / &4) pow 2) * Dl pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((cc * tau / &2) / (e / &4) pow 2) * (e / &4) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `d = a + b` THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt a <= sqrt d` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt d` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Dl / &2 <= d + C1 * sqrt d` ASSUME_TAC THENL
   [SUBGOAL_THEN `C1 * sqrt a <= C1 * sqrt d` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `d <= &1` THENL
   [SUBGOAL_THEN `d <= sqrt d` ASSUME_TAC THENL
     [SUBGOAL_THEN `sqrt d * sqrt d = d` (fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THENL
       [ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `Dl <= &2 * (&1 + C1) * sqrt d` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `Dl pow 2 <= (&4 * (&1 + C1) pow 2) * d` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&2 * (&1 + C1) * sqrt d) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &4 * (&1 + C1) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&4 * (&1 + C1) pow 2) * Dl pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&4 * (&1 + C1) pow 2) * ((&4 * (&1 + C1) pow 2) * d)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID;
                   REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((e / &4) pow 2) * Dl pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv((e / &4) pow 2) * (e / &4) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC]);;

(* A closed disc (in a chart) inside some open cap of a family.            *)

let cmr_inside = new_definition
 `cmr_inside n1 (Q1:num->real^3^3) (c1:num->real^2) (r1:num->real)
             (Qj:real^3^3) (cj:real^2) s <=>
    ?k. 1 <= k /\ k <= n1 /\ &0 < r1 k /\
        IMAGE (cm_capmap Qj) (cball(cj,s)) SUBSET IMAGE (cm_capmap (Q1 k)) (ball(c1 k,r1 k))`;;

(* Caps of F2 whose half lies in an open cap of F1: replacement on F1      *)
(* decreases the energy at least as much as replacement on those halves.   *)

let CMR_L312_PLUS = prove
 (`!S (G:real^K->real^K^K) e Lam n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
    (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < e /\
     cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
     ==> sum(1..n2) (\j. if &0 < r2 j /\ cmr_inside n1 Q1 c1 r1 (Q2 j) (c2 j) (r2 j / &2)
                         then cmr_dec S G (Q2 j) (c2 j) (r2 j / &2) u else &0)
         <= cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_l3hyp S G e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                 (u:real^3->real^K)` THEN
  REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  ABBREV_TAC `cnd = \j. &0 < (r2:num->real) j /\
                        cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                          ((c2:num->real^2) j) (r2 j / &2)` THEN
  ABBREV_TAC `rp = \j. if (cnd:num->bool) j then (r2:num->real) j / &2 else &0` THEN
  SUBGOAL_THEN `!j. &0 < (rp:num->real) j <=> (cnd:num->bool) j` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN EXPAND_TAC "rp" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    UNDISCH_TAC `(cnd:num->bool) j` THEN EXPAND_TAC "cnd" THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cmr_dfam n2 Q2 (c2:num->real^2) rp` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_DFAM_SHRINK THEN EXISTS_TAC `r2:num->real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    EXPAND_TAC "rp" THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(cnd:num->bool) j` THEN EXPAND_TAC "cnd" THEN REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= n2 /\ &0 < (rp:num->real) j
        ==> wan_gdir (ball((c2:num->real^2) j,rp j)) G
              (\x. (u:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) j) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(rp:num->real) j = r2 j / &2 /\ &0 < r2 j` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `&0 < (rp:num->real) j` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      EXPAND_TAC "rp" THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(cnd:num->bool) j` THEN EXPAND_TAC "cnd" THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball((c2:num->real^2) j,r2 j)) G
                  (\x. (u:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) j) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `(Q2:num->real^3^3) j`;
                       `(c2:num->real^2) j`; `(r2:num->real) j`] CMR_CHART_CMAP) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[cmr_dfam]; SIMP_TAC[cm_cmap]]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `rp:num->real`; `u:real^3->real^K`]
                CMR_REPN_DEC_SUM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`;
                 `cmr_repn S G n2 Q2 (c2:num->real^2) rp (u:real^3->real^K)`] CMR_REPN_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n2:num`;
                   `Q2:num->real^3^3`; `c2:num->real^2`; `rp:num->real`; `u:real^3->real^K`]
                  CMR_REPN_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `n2:num`) THEN REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(cnd:num->bool) k` THENL
     [ALL_TAC;
      SUBGOAL_THEN `ball((c2:num->real^2) k,rp k) = {}` SUBST1_TAC THENL
       [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_MESON_TAC[REAL_NOT_LT];
        REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY]]] THEN
    UNDISCH_TAC `(cnd:num->bool) k` THEN EXPAND_TAC "cnd" THEN
    REWRITE_TAC[cmr_inside] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(rp:num->real) k = r2 k / &2` SUBST1_TAC THENL
     [EXPAND_TAC "rp" THEN EXPAND_TAC "cnd" THEN REWRITE_TAC[cmr_inside] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~(y IN cmr_fop n1 Q1 (c1:num->real^2) r1)` THEN
    REWRITE_TAC[cmr_fop; IN_ELIM_THM] THEN EXISTS_TAC `l:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(c2:num->real^2) k`; `(r2:num->real) k / &2`] BALL_SUBSET_CBALL) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `cm_capmap ((Q2:num->real^3^3) k)` IMAGE_SUBSET)) THEN
    UNDISCH_TAC `y IN IMAGE (cm_capmap ((Q2:num->real^3^3) k)) (ball((c2:num->real^2) k,r2 k / &2))` THEN
    UNDISCH_TAC `IMAGE (cm_capmap ((Q2:num->real^3^3) k)) (cball((c2:num->real^2) k,r2 k / &2)) SUBSET
                 IMAGE (cm_capmap ((Q1:num->real^3^3) l)) (ball((c1:num->real^2) l,r1 l))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> e1 <= e0 - x ==> y <= e0 - e1`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(cnd:num->bool) j <=>
                &0 < (r2:num->real) j /\
                cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                  ((c2:num->real^2) j) (r2 j / &2)` (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "cnd" THEN REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "rp" THEN ASM_REWRITE_TAC[]);;

(* Dirichlet energies of differences of chart maps are nonnegative.          *)

let CMR_CHART_DIFF_DIR_POS = prove
 (`!S (Q:real^3^3) (c:real^2) r (f:real^3->real^K) g.
     cm_smap S f /\ cm_smap S g /\ orthogonal_matrix Q
     ==> &0 <= wan_dir (ball(c,r)) (\x. f(cm_capmap Q x) - g(cm_capmap Q x))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < r` THENL
   [MATCH_MP_TAC WAN_DIR_POS THEN MATCH_MP_TAC WAN_W12_SUB THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `f:real^3->real^K`; `Q:real^3^3`; `c:real^2`;
                   `r:real`] CMR_CHART_CMAP) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `g:real^3->real^K`; `Q:real^3^3`; `c:real^2`;
                   `r:real`] CMR_CHART_CMAP) THEN
    ASM_SIMP_TAC[cm_cmap];
    SUBGOAL_THEN `ball(c:real^2,r) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[wan_dir; INTEGRAL_EMPTY; DROP_VEC; SUM_0; REAL_LE_REFL]]]);;

(* Caps of F2 whose half lies in no open cap of F1 (CM's B2,-): either the *)
(* change made by H(u,F1) is large, or the per-ball inequalities sum up.   *)

let CMR_L312_MINUS = prove
 (`!S (G:real^K->real^K^K) e lam Lam cc CS Cp tau n1 Q1 (c1:num->real^2) r1 n2 Q2
    (c2:num->real^2) r2 (u:real^3->real^K).
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < e /\ &0 < lam /\
     (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\
     &0 < cc /\ cmr_dirok S G e cc /\ &0 < CS /\ cmr_stabok S G e CS /\
     &0 < Cp /\ &0 < tau /\ cmr_pbok S G e Cp tau /\
     cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
     ==> cc * tau / &2 < cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u) \/
         sum(1..n2) (\j. if &0 < r2 j /\ ~cmr_inside n1 Q1 c1 r1 (Q2 j) (c2 j) (r2 j / &2)
                         then cmr_dec S G (Q2 j) (c2 j) (r2 j / &2) u else &0)
         <= (cm_sen G (cmr_repn S G n1 Q1 c1 r1 u) -
             cm_sen G (cmr_repn S G n2 Q2 c2 r2 (cmr_repn S G n1 Q1 c1 r1 u))) +
            (CS * sqrt(e / &2 + e pow 2 / &4) +
             Cp * sqrt((&3 * e / &2) / lam) * sqrt(&2 / cc)) *
            sqrt(cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `CS:real`;
                 `n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_WDIFF) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `lam:real`; `Lam:real`;
                 `n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`;
                 `r2:num->real`;
                 `\j. &0 < (r2:num->real) j /\
                      ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                        ((c2:num->real^2) j) (r2 j / &2)`] CMR_L3_SUMX) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  UNDISCH_TAC `cmr_l3hyp S G e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                 (u:real^3->real^K)` THEN
  REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  ABBREV_TAC `u1 = cmr_repn S G n1 Q1 (c1:num->real^2) r1 (u:real^3->real^K)` THEN
  SUBGOAL_THEN `!j. 1 <= j /\ j <= n2 ==> orthogonal_matrix((Q2:num->real^3^3) j)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  (* the drops of energy *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`]
                CMR_L3_DROP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / &2` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u1:real^3->real^K`]
                CMR_REPN_DEC_SUM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  (* the Dirichlet energy of the change on the caps of F2 *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `cc:real`;
                 `n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_SUMY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / &2` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ABBREV_TAC `Y = \j. wan_dir (ball((c2:num->real^2) j,r2 j))
                        (\x. (u1:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) j) x) -
                             (u:real^3->real^K)(cm_capmap (Q2 j) x))` THEN
  SUBGOAL_THEN `!j. 1 <= j /\ j <= n2 ==> &0 <= (Y:num->real) j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Y" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CMR_CHART_DIFF_DIR_POS THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cc * sum(1..n2) (Y:num->real) <=
                &2 * (cm_sen (G:real^K->real^K^K) u - cm_sen G (u1:real^3->real^K))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC
   `?j. 1 <= j /\ j <= n2 /\
        (&0 < (r2:num->real) j /\
         ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
            ((c2:num->real^2) j) (r2 j / &2)) /\
        tau < (Y:num->real) j` THENL
   [DISJ1_TAC THEN FIRST_X_ASSUM(X_CHOOSE_THEN `j0:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(Y:num->real) j0 <= sum(1..n2) Y` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`{j0:num}`; `1..n2`; `Y:num->real`] SUM_SUBSET_SIMPLE) THEN
      REWRITE_TAC[SUM_SING; FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_NUMSEG; IN_DIFF] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `cc * tau < cc * (Y:num->real) j0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `cc * (Y:num->real) j0 <= cc * sum(1..n2) Y` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    UNDISCH_TAC `cc * sum(1..n2) (Y:num->real) <=
                 &2 * (cm_sen (G:real^K->real^K^K) u - cm_sen G (u1:real^3->real^K))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ2_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Cp:real`;
                 `tau:real`; `n2:num`; `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`;
                 `\j. &0 < (r2:num->real) j /\
                      ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                        ((c2:num->real^2) j) (r2 j / &2)`;
                 `u:real^3->real^K`; `u1:real^3->real^K`] CMR_PBALL_SUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(tau < (Y:num->real) j)` MP_TAC THENL
       [ASM_MESON_TAC[]; EXPAND_TAC "Y" THEN REWRITE_TAC[REAL_NOT_LT]];
      X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                     `n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`;
                     `n2:num`; `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`;
                     `u:real^3->real^K`; `j:num`; `(r2:num->real) j / &2`; `rho:real`]
                    CMR_L3_ZERO) THEN
      ASM_REWRITE_TAC[cmr_l3hyp] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
          UNDISCH_TAC `~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                          ((c2:num->real^2) j) (r2 j / &2)` THEN
          REWRITE_TAC[cmr_inside] THEN MESON_TAC[]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:num->real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ABBREV_TAC `EE = cm_sen G (u:real^3->real^K) - cm_sen G (u1:real^3->real^K)` THEN
  (* (a) the decreases of u1 on the caps of J- *)
  SUBGOAL_THEN
   `sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (r2 j / &2)
                    then cmr_dec S G (Q2 j) (c2 j) (r2 j) (u1:real^3->real^K) else &0) <=
    sum(1..n2) (\k. if &0 < r2 k then cmr_dec S G (Q2 k) (c2 k) (r2 k) u1 else &0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `&0 < (r2:num->real) j` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                   `(Q2:num->real^3^3) j`; `(c2:num->real^2) j`; `(r2:num->real) j`;
                   `u1:real^3->real^K`] CMR_DEC_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* (b) the energy differences on the good discs *)
  ABBREV_TAC `rr = \j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (r2 j / &2) then (rho:num->real) j else &0` THEN
  SUBGOAL_THEN `cmr_dfam n2 Q2 (c2:num->real^2) rr` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_DFAM_SHRINK THEN EXISTS_TAC `r2:num->real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN EXPAND_TAC "rr" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (r2 j / &2)
                    then cm_gen G (ball(c2 j,rho j)) (\x. (u:real^3->real^K)(cm_capmap (Q2 j) x)) -
                         cm_gen G (ball(c2 j,rho j)) (\x. (u1:real^3->real^K)(cm_capmap (Q2 j) x))
                    else &0) =
    cmr_sen_on G u (cmr_fop n2 Q2 c2 rr) - cmr_sen_on G u1 (cmr_fop n2 Q2 c2 rr)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`; `n2:num`;
                   `Q2:num->real^3^3`; `c2:num->real^2`; `rr:num->real`] CMR_SEN_FAM_SUM) THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u1:real^3->real^K`; `n2:num`;
                   `Q2:num->real^3^3`; `c2:num->real^2`; `rr:num->real`] CMR_SEN_FAM_SUM) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "rr" THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `ball((c2:num->real^2) j,&0) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[BALL_EQ_EMPTY; REAL_LE_REFL]; REWRITE_TAC[CMR_CM_GEN_EMPTY]] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (u:real^3->real^K) (cmr_fop n2 Q2 (c2:num->real^2) rr) -
    cmr_sen_on G (u1:real^3->real^K) (cmr_fop n2 Q2 c2 rr)
    <= CS * sqrt EE * sqrt(e / &2 + e pow 2 / &4)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(b - a) <= c ==> a - b <= c`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      free_in `CS:real` (concl th))) THEN
    MATCH_MP_TAC CMR_FOP_OPEN_IN THEN ASM_MESON_TAC[cmr_dfam];
    ALL_TAC] THEN
  (* (c) the error sums *)
  ABBREV_TAC
   `SX = sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (r2 j / &2)
                         then wan_dir (ball(c2 j,r2 j)) (\x. (u:real^3->real^K)(cm_capmap (Q2 j) x)) +
                              wan_dir (ball(c2 j,r2 j)) (\x. (u1:real^3->real^K)(cm_capmap (Q2 j) x))
                         else &0)` THEN
  ABBREV_TAC
   `SY = sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (r2 j / &2)
                         then wan_dir (ball(c2 j,r2 j))
                                (\x. (u1:real^3->real^K)(cm_capmap (Q2 j) x) -
                                     (u:real^3->real^K)(cm_capmap (Q2 j) x))
                         else &0)` THEN
  SUBGOAL_THEN `sqrt SX <= sqrt((&3 * e / &2) / lam)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= SY /\ SY <= sum(1..n2) (Y:num->real)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["SY"; "Y"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG; MATCH_MP_TAC SUM_LE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC CMR_CHART_DIFF_DIR_POS THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt SY <= sqrt(&2 / cc) * sqrt EE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..n2) (Y:num->real)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 / cc * EE = (&2 * EE) / cc` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= SX` ASSUME_TAC THENL
   [EXPAND_TAC "SX" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC WAN_DIR_POS THEN
    MATCH_MP_TAC(MESON[cm_cmap] `cm_cmap (S:real^K->bool) s (f:real^2->real^K) ==> wan_w12 s f`) THEN
    MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cp * sqrt SX * sqrt SY <= Cp * sqrt((&3 * e / &2) / lam) * (sqrt(&2 / cc) * sqrt EE)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  UNDISCH_TAC
   `cmr_sen_on G (u:real^3->real^K) (cmr_fop n2 Q2 (c2:num->real^2) rr) -
    cmr_sen_on G (u1:real^3->real^K) (cmr_fop n2 Q2 c2 rr)
    <= CS * sqrt EE * sqrt(e / &2 + e pow 2 / &4)` THEN
  UNDISCH_TAC
   `Cp * sqrt SX * sqrt SY <= Cp * sqrt((&3 * e / &2) / lam) * (sqrt(&2 / cc) * sqrt EE)` THEN
  UNDISCH_TAC
   `sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (r2 j / &2)
                    then cmr_dec S G (Q2 j) (c2 j) (r2 j) (u1:real^3->real^K) else &0) <=
    sum(1..n2) (\k. if &0 < r2 k then cmr_dec S G (Q2 k) (c2 k) (r2 k) u1 else &0)` THEN
  UNDISCH_TAC
   `sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (r2 j / &2)
                    then cm_gen G (ball(c2 j,rho j)) (\x. (u:real^3->real^K)(cm_capmap (Q2 j) x)) -
                         cm_gen G (ball(c2 j,rho j)) (\x. (u1:real^3->real^K)(cm_capmap (Q2 j) x))
                    else &0) =
    cmr_sen_on G u (cmr_fop n2 Q2 c2 rr) - cmr_sen_on G u1 (cmr_fop n2 Q2 c2 rr)` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN REAL_ARITH_TAC);;

(* Energy facts for the half family.                                          *)

let CMR_L3_HALF = prove
 (`!S (G:real^K->real^K^K) e Lam n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
    (u:real^3->real^K) mu.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < e /\ &0 < mu /\ mu <= &1 /\
     cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
     ==> cmr_dfam n2 Q2 c2 (\j. mu * r2 j) /\
         (!k. 1 <= k /\ k <= n2 /\ &0 < mu * r2 k
              ==> wan_gdir (ball(c2 k,mu * r2 k)) G (\x. u(cm_capmap (Q2 k) x)) <= e) /\
         &0 <= cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 c2 (\j. mu * r2 j) u) /\
         cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 c2 (\j. mu * r2 j) u) <= e / &4 /\
         cm_sen G (cmr_repn S G n2 Q2 c2 (\j. mu * r2 j) u) =
         cm_sen G u -
         sum(1..n2) (\k. if &0 < r2 k
                         then cmr_dec S G (Q2 k) (c2 k) (mu * r2 k) u else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_l3hyp S G e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                 (u:real^3->real^K)` THEN
  REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. &0 < mu * (r2:num->real) k <=> &0 < r2 k` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[REAL_LT_MUL_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `cmr_dfam n2 Q2 (c2:num->real^2) (\j. mu * r2 j)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_DFAM_SHRINK THEN EXISTS_TAC `r2:num->real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n2 /\ &0 < r2 k
        ==> wan_gdir (ball((c2:num->real^2) k,mu * r2 k)) G
              (\x. (u:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) k) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball((c2:num->real^2) k,r2 k)) G
                  (\x. (u:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) k) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_BALL THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`S:real^K->bool`; `u:real^3->real^K`; `(Q2:num->real^3^3) k`;
                       `(c2:num->real^2) k`; `(r2:num->real) k`] CMR_CHART_CMAP) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cmr_dfam];
          SIMP_TAC[cm_cmap]]];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (u:real^3->real^K) (cmr_fop n2 Q2 (c2:num->real^2) (\j. mu * r2 j)) <=
    cmr_sen_on G u (cmr_fop n2 Q2 c2 r2)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^K->real^K^K`; `u:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; STRIP_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CMR_CONE_OPEN THEN
      MATCH_MP_TAC CMR_FOP_OPEN_IN THEN ASM_MESON_TAC[cmr_dfam];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CMR_CONE_OPEN THEN
      MATCH_MP_TAC CMR_FOP_OPEN_IN THEN ASM_MESON_TAC[cmr_dfam];
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s SUBSET (t:real^3->bool)`) THEN
      REWRITE_TAC[cmr_fop; SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real^2` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `x IN ball((c2:num->real^2) k,mu * r2 k)` THEN
      REWRITE_TAC[IN_BALL] THEN
      ASM_CASES_TAC `&0 <= (r2:num->real) k` THENL
       [SUBGOAL_THEN `mu * (r2:num->real) k <= r2 k` MP_TAC THENL
         [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
          REAL_ARITH_TAC];
        SUBGOAL_THEN `mu * (r2:num->real) k <= &0` MP_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= mu * --r ==> mu * r <= &0`) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MP_TAC(ISPECL [`(c2:num->real^2) k`; `x:real^2`] DIST_POS_LE) THEN
          REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `\j. mu * (r2:num->real) j`;
                 `u:real^3->real^K`] CMR_L3_DROP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `\j. mu * (r2:num->real) j`;
                 `u:real^3->real^K`] CMR_REPN_DEC_SUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `cmr_sen_on G (u:real^3->real^K) (cmr_fop n2 Q2 (c2:num->real^2) r2) <= e / &4` THEN
  UNDISCH_TAC
   `cmr_sen_on G (u:real^3->real^K) (cmr_fop n2 Q2 (c2:num->real^2) (\j. mu * r2 j)) <=
    cmr_sen_on G u (cmr_fop n2 Q2 c2 r2)` THEN
  UNDISCH_TAC
   `cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 (c2:num->real^2) (\j. mu * r2 j) (u:real^3->real^K))
    <= cmr_sen_on G u (cmr_fop n2 Q2 c2 (\j. mu * r2 j))` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* CM Lemma 3.11, (3.12): replacement on F1 then F2 decreases the energy by *)
(* at least kappa times the square of the decrease from replacement on the  *)
(* half family of F2.                                                        *)

let CMR_L312 = prove
 (`!S (G:real^K->real^K^K) d e.
     cmr_ctx S G d e
     ==> ?kappa. &0 < kappa /\
           !n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2 (u:real^3->real^K).
             cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
             ==> kappa * (cm_sen G u -
                          cm_sen G (cmr_repn S G n2 Q2 c2 (\j. r2 j / &2) u)) pow 2
                 <= cm_sen G u -
                    cm_sen G (cmr_repn S G n2 Q2 c2 r2 (cmr_repn S G n1 Q1 c1 r1 u))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP CMR_CTX_UNPACK) THEN
  ABBREV_TAC `C1 = CS * sqrt(e / &2 + e pow 2 / &4) +
                   Cp * sqrt((&3 * e / &2) / lam) * sqrt(&2 / cc)` THEN
  SUBGOAL_THEN `&0 <= e / &2 + e pow 2 / &4 /\ &0 <= (&3 * e / &2) / lam /\ &0 <= &2 / cc`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C1` ASSUME_TAC THENL
   [EXPAND_TAC "C1" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  EXISTS_TAC `min (min (&2 / e) ((cc * tau / &2) / (e / &4) pow 2))
                  (min (inv(&4 * (&1 + C1) pow 2)) (inv((e / &4) pow 2)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
      REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN MATCH_MP_TAC REAL_POW_LT THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`;
                 `&1 / &2`] CMR_L3_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\j. &1 / &2 * (r2:num->real) j) = (\j. r2 j / &2)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&1 / &2 * x = x / &2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  DISCH_THEN(fun th ->
    SUBGOAL_THEN
     `sum(1..n2) (\j. if &0 < r2 j /\ cmr_inside n1 Q1 (c1:num->real^2) r1
                                       ((Q2:num->real^3^3) j) ((c2:num->real^2) j) (r2 j / &2)
                     then cmr_dec S G (Q2 j) (c2 j) (r2 j / &2) (u:real^3->real^K) else &0) +
      sum(1..n2) (\j. if &0 < r2 j /\ ~cmr_inside n1 Q1 (c1:num->real^2) r1
                                       ((Q2:num->real^3^3) j) ((c2:num->real^2) j) (r2 j / &2)
                     then cmr_dec S G (Q2 j) (c2 j) (r2 j / &2) (u:real^3->real^K) else &0) =
      cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 c2 (\j. r2 j / &2) u)`
    ASSUME_TAC THENL
     [REWRITE_TAC[th; REAL_ARITH `u - (u - s) = s:real`; GSYM SUM_ADD_NUMSEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      ASM_CASES_TAC `&0 < (r2:num->real) j` THEN ASM_REWRITE_TAC[REAL_ADD_LID] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID];
      ALL_TAC]) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `lam:real`; `Lam:real`;
                 `cc:real`; `CS:real`; `Cp:real`; `tau:real`; `n1:num`; `Q1:num->real^3^3`;
                 `c1:num->real^2`; `r1:num->real`; `n2:num`; `Q2:num->real^3^3`;
                 `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`] CMR_L312_MINUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L312_PLUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_l3hyp S G e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                 (u:real^3->real^K)` THEN
  REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`]
                CMR_L3_DROP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / &2` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`;
                 `cmr_repn S G n1 Q1 (c1:num->real^2) r1 (u:real^3->real^K)`] CMR_L3_DROP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `cm_sen G (u:real^3->real^K) -
    cm_sen G (cmr_repn S G n2 Q2 (c2:num->real^2) r2 (cmr_repn S G n1 Q1 (c1:num->real^2) r1 u)) =
    (cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u)) +
    (cm_sen G (cmr_repn S G n1 Q1 c1 r1 u) -
     cm_sen G (cmr_repn S G n2 Q2 c2 r2 (cmr_repn S G n1 Q1 c1 r1 u)))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CMR_L312_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`sum(1..n2) (\j. if &0 < r2 j /\ cmr_inside n1 Q1 (c1:num->real^2) r1
                                       ((Q2:num->real^3^3) j) ((c2:num->real^2) j) (r2 j / &2)
                     then cmr_dec S G (Q2 j) (c2 j) (r2 j / &2) (u:real^3->real^K) else &0)`;
    `sum(1..n2) (\j. if &0 < r2 j /\ ~cmr_inside n1 Q1 (c1:num->real^2) r1
                                       ((Q2:num->real^3^3) j) ((c2:num->real^2) j) (r2 j / &2)
                     then cmr_dec S G (Q2 j) (c2 j) (r2 j / &2) (u:real^3->real^K) else &0)`;
    `C1:real`; `e:real`; `cc:real`; `tau:real`] THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* CM (3.13).                                                                *)
(* ========================================================================= *)

(* Caps of F2 whose mu-scaled closed disc lies in an open cap of F1: H(u,F1) *)
(* is already minimizing there, so replacement on them does not decrease    *)
(* the energy of H(u,F1).                                                    *)

let CMR_L313_PLUS = prove
 (`!S (G:real^K->real^K^K) e Lam n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
    (u:real^3->real^K) mu.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < e /\ &0 < mu /\ mu <= &1 /\
     cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
     ==> sum(1..n2) (\j. if &0 < r2 j /\ cmr_inside n1 Q1 c1 r1 (Q2 j) (c2 j) (mu * r2 j)
                         then cmr_dec S G (Q2 j) (c2 j) (mu * r2 j)
                                (cmr_repn S G n1 Q1 c1 r1 u)
                         else &0) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `cmr_l3hyp S G e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                 (u:real^3->real^K)` THEN
  REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  ABBREV_TAC `u1 = cmr_repn S G n1 Q1 (c1:num->real^2) r1 (u:real^3->real^K)` THEN
  ABBREV_TAC `cnd = \j. &0 < (r2:num->real) j /\
                        cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                          ((c2:num->real^2) j) (mu * r2 j)` THEN
  ABBREV_TAC `rp = \j. if (cnd:num->bool) j then mu * (r2:num->real) j else &0` THEN
  SUBGOAL_THEN `!j. (cnd:num->bool) j ==> &0 < (r2:num->real) j` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN EXPAND_TAC "cnd" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. &0 < (rp:num->real) j <=> (cnd:num->bool) j` ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN EXPAND_TAC "rp" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. (cnd:num->bool) j ==> mu * (r2:num->real) j <= r2 j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `cmr_dfam n2 Q2 (c2:num->real^2) rp` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_DFAM_SHRINK THEN EXISTS_TAC `r2:num->real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN EXPAND_TAC "rp" THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 1 <= j /\ j <= n2 /\ &0 < (rp:num->real) j
        ==> wan_gdir (ball((c2:num->real^2) j,rp j)) G
              (\x. (u1:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) j) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(rp:num->real) j = mu * r2 j` SUBST1_TAC THENL
     [EXPAND_TAC "rp" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball((c2:num->real^2) j,r2 j)) G
                  (\x. (u1:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) j) x))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
    ASM_SIMP_TAC[OPEN_BALL; SUBSET_BALL] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `u1:real^3->real^K`; `(Q2:num->real^3^3) j`;
                   `(c2:num->real^2) j`; `(r2:num->real) j`] CMR_CHART_CMAP) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[cmr_dfam]; SIMP_TAC[cm_cmap]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `rp:num->real`; `u1:real^3->real^K`]
                CMR_REPN_DEC_SUM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`;
                 `cmr_repn S G n2 Q2 (c2:num->real^2) rp (u1:real^3->real^K)`] CMR_REPN_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n2:num`;
                   `Q2:num->real^3^3`; `c2:num->real^2`; `rp:num->real`; `u1:real^3->real^K`]
                  CMR_REPN_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `n2:num`) THEN REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(u1:real^3->real^K) y` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `(cnd:num->bool) k` THENL
       [ALL_TAC;
        SUBGOAL_THEN `ball((c2:num->real^2) k,rp k) = {}` SUBST1_TAC THENL
         [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_MESON_TAC[REAL_NOT_LT];
          REWRITE_TAC[IMAGE_CLAUSES; NOT_IN_EMPTY]]] THEN
      UNDISCH_TAC `(cnd:num->bool) k` THEN EXPAND_TAC "cnd" THEN
      REWRITE_TAC[cmr_inside] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(rp:num->real) k = mu * r2 k` SUBST1_TAC THENL
       [EXPAND_TAC "rp" THEN EXPAND_TAC "cnd" THEN REWRITE_TAC[cmr_inside] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN
      UNDISCH_TAC `~(y IN cmr_fop n1 Q1 (c1:num->real^2) r1)` THEN
      REWRITE_TAC[cmr_fop; IN_ELIM_THM] THEN EXISTS_TAC `l:num` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(c2:num->real^2) k`; `mu * (r2:num->real) k`] BALL_SUBSET_CBALL) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `cm_capmap ((Q2:num->real^3^3) k)` IMAGE_SUBSET)) THEN
      UNDISCH_TAC `y IN IMAGE (cm_capmap ((Q2:num->real^3^3) k)) (ball((c2:num->real^2) k,mu * r2 k))` THEN
      UNDISCH_TAC `IMAGE (cm_capmap ((Q2:num->real^3^3) k)) (cball((c2:num->real^2) k,mu * r2 k)) SUBSET
                   IMAGE (cm_capmap ((Q1:num->real^3^3) l)) (ball((c1:num->real^2) l,r1 l))` THEN
      SET_TAC[];
      MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                     `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`]
                    CMR_REPN_FACTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / &2` THEN
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPEC `n1:num`) THEN ASM_REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `~(y IN cmr_fop n1 Q1 (c1:num->real^2) r1)` THEN
      REWRITE_TAC[cmr_fop; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> e1 <= e1 - x ==> y <= &0`) THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(cnd:num->bool) j <=>
                &0 < (r2:num->real) j /\
                cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                  ((c2:num->real^2) j) (mu * r2 j)` (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "cnd" THEN REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "rp" THEN ASM_REWRITE_TAC[]);;

(* The final real arithmetic of (3.13).                                      *)

let CMR_L313_ARITH0 = prove
 (`!L B x C1 e cc tau kappa.
     &0 < e /\ &0 < cc /\ &0 < tau /\ &0 < C1 /\ &0 <= x /\ &0 <= B /\ L <= e / &2 /\
     (cc * tau / &2 < x \/ L <= B + C1 * sqrt x) /\
     kappa = min (inv C1) (sqrt(cc * tau / &2) / (e / &2))
     ==> L <= sqrt x / kappa + B`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sqrt(cc * tau / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < kappa /\ kappa <= inv C1 /\ kappa <= sqrt(cc * tau / &2) / (e / &2)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `kappa = min (inv C1) (sqrt(cc * tau / &2) / (e / &2))` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `&0 <= sqrt x` ASSUME_TAC THENL [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [SUBGOAL_THEN `sqrt(cc * tau / &2) <= sqrt x` ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `e / &2 <= sqrt x / kappa` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `e / &2 * sqrt(cc * tau / &2) / (e / &2)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `e / &2 * sqrt(cc * tau / &2) / (e / &2) = sqrt(cc * tau / &2)`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD; ASM_REWRITE_TAC[]]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `C1 * sqrt x <= sqrt x / kappa` MP_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let CMR_L313_ARITH = prove
 (`!L Sp Sm B x C1 e cc tau kappa.
     &0 < e /\ &0 < cc /\ &0 < tau /\ &0 < C1 /\ &0 <= x /\ &0 <= B /\ L <= e / &2 /\
     Sp + Sm = L /\ Sp <= &0 /\
     (cc * tau / &2 < x \/ Sm <= B + C1 * sqrt x) /\
     kappa = min (inv C1) (sqrt(cc * tau / &2) / (e / &2))
     ==> L <= sqrt x / kappa + B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMR_L313_ARITH0 THEN
  MAP_EVERY EXISTS_TAC [`C1:real`; `e:real`; `cc:real`; `tau:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Symmetry and monotonicity of the Dirichlet energy of a difference of two *)
(* maps read in a chart.                                                    *)

let CMR_CHART_DIFF_DIR_MONO = prove
 (`!S (Q:real^3^3) (c:real^2) r r' (f:real^3->real^K) g.
     cm_smap S f /\ cm_smap S g /\ orthogonal_matrix Q /\ r' <= r
     ==> wan_dir (ball(c,r')) (\x. f(cm_capmap Q x) - g(cm_capmap Q x))
         <= wan_dir (ball(c,r)) (\x. g(cm_capmap Q x) - f(cm_capmap Q x))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 < r` THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `f:real^3->real^K`; `Q:real^3^3`; `c:real^2`;
                   `r:real`] CMR_CHART_CMAP) THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `g:real^3->real^K`; `Q:real^3^3`; `c:real^2`;
                   `r:real`] CMR_CHART_CMAP) THEN
    ASM_REWRITE_TAC[cm_cmap] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_dir (ball(c:real^2,r))
                  (\x. (f:real^3->real^K)(cm_capmap Q x) - g(cm_capmap Q x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_DIR_MONO_P THEN REWRITE_TAC[OPEN_BALL] THEN
      ASM_SIMP_TAC[SUBSET_BALL] THEN MATCH_MP_TAC CMR_W12_PARTIALS THEN
      MATCH_MP_TAC WAN_W12_SUB THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`ball(c:real^2,r)`; `\x. (f:real^3->real^K)(cm_capmap Q x)`;
                     `\x. (g:real^3->real^K)(cm_capmap Q x)`] CMW_DIR_SUB_SYM) THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[REAL_LE_REFL]];
    SUBGOAL_THEN `ball(c:real^2,r') = {}` SUBST1_TAC THENL
     [REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `wan_dir ({}:real^2->bool)
                    (\x. (f:real^3->real^K)(cm_capmap Q x) - g(cm_capmap Q x)) = &0`
    SUBST1_TAC THENL
     [REWRITE_TAC[wan_dir; INTEGRAL_EMPTY; DROP_VEC; SUM_0]; ALL_TAC] THEN
    MATCH_MP_TAC CMR_CHART_DIFF_DIR_POS THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* Shrinking a family of caps by a factor 0 < mu <= 1: energy facts.         *)

let CMR_FAM_SCALE = prove
 (`!S (G:real^K->real^K^K) e Lam n Q (c:num->real^2) r (f:real^3->real^K) B mu.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < mu /\ mu <= &1 /\
     cm_smap S f /\ cmr_dfam n Q c r /\
     (!k. 1 <= k /\ k <= n /\ &0 < r k
          ==> wan_gdir (ball(c k,r k)) G (\x. f(cm_capmap (Q k) x)) <= e) /\
     cmr_sen_on G f (cmr_fop n Q c r) <= B
     ==> cmr_dfam n Q c (\j. mu * r j) /\
         (!k. 1 <= k /\ k <= n /\ &0 < mu * r k
              ==> wan_gdir (ball(c k,mu * r k)) G (\x. f(cm_capmap (Q k) x)) <= e) /\
         &0 <= cm_sen G f - cm_sen G (cmr_repn S G n Q c (\j. mu * r j) f) /\
         cm_sen G f - cm_sen G (cmr_repn S G n Q c (\j. mu * r j) f) <= B /\
         cm_sen G (cmr_repn S G n Q c (\j. mu * r j) f) =
         cm_sen G f -
         sum(1..n) (\k. if &0 < r k then cmr_dec S G (Q k) (c k) (mu * r k) f else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. &0 < mu * (r:num->real) k <=> &0 < r k` ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[REAL_LT_MUL_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. 1 <= k /\ k <= n ==> orthogonal_matrix((Q:num->real^3^3) k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  SUBGOAL_THEN `cmr_dfam n Q (c:num->real^2) (\j. mu * r j)` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_DFAM_SHRINK THEN EXISTS_TAC `r:num->real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n /\ &0 < r k
        ==> wan_gdir (ball((c:num->real^2) k,mu * r k)) G
              (\x. (f:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball((c:num->real^2) k,r k)) G
                  (\x. (f:real^3->real^K)(cm_capmap ((Q:num->real^3^3) k) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_BALL THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`S:real^K->bool`; `f:real^3->real^K`; `(Q:num->real^3^3) k`;
                       `(c:num->real^2) k`; `(r:num->real) k`] CMR_CHART_CMAP) THEN
        ASM_SIMP_TAC[cm_cmap]];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (f:real^3->real^K) (cmr_fop n Q (c:num->real^2) (\j. mu * r j)) <=
    cmr_sen_on G f (cmr_fop n Q c r)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^K->real^K^K`; `f:real^3->real^K`; `Lam:real`] CMR_SEN_ON_BASICS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; STRIP_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CMR_CONE_OPEN THEN
      MATCH_MP_TAC CMR_FOP_OPEN_IN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN MATCH_MP_TAC CMR_CONE_OPEN THEN
      MATCH_MP_TAC CMR_FOP_OPEN_IN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[cmr_fop; SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real^2` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `x IN ball((c:num->real^2) k,mu * r k)` THEN
      REWRITE_TAC[IN_BALL] THEN
      ASM_CASES_TAC `&0 <= (r:num->real) k` THENL
       [SUBGOAL_THEN `mu * (r:num->real) k <= r k` MP_TAC THENL
         [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
          REAL_ARITH_TAC];
        SUBGOAL_THEN `mu * (r:num->real) k <= &0` MP_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= mu * --r ==> mu * r <= &0`) THEN
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MP_TAC(ISPECL [`(c:num->real^2) k`; `x:real^2`] DIST_POS_LE) THEN
          REAL_ARITH_TAC]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `\j. mu * (r:num->real) j`;
                 `f:real^3->real^K`] CMR_L3_DROP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n:num`;
                 `Q:num->real^3^3`; `c:num->real^2`; `\j. mu * (r:num->real) j`;
                 `f:real^3->real^K`] CMR_REPN_DEC_SUM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `cmr_sen_on G (f:real^3->real^K) (cmr_fop n Q (c:num->real^2) r) <= B` THEN
  UNDISCH_TAC
   `cmr_sen_on G (f:real^3->real^K) (cmr_fop n Q (c:num->real^2) (\j. mu * r j)) <=
    cmr_sen_on G f (cmr_fop n Q c r)` THEN
  UNDISCH_TAC
   `cm_sen G f - cm_sen G (cmr_repn S G n Q (c:num->real^2) (\j. mu * r j) (f:real^3->real^K))
    <= cmr_sen_on G f (cmr_fop n Q c (\j. mu * r j))` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Caps of F2 whose mu-scaled closed disc lies in no open cap of F1: either *)
(* the change made by H(u,F1) is large, or the per-ball inequalities (with  *)
(* the roles of u and H(u,F1) switched, on the discs of radius 2 mu r) sum  *)
(* up, CM (3.31)-(3.32).                                                    *)

let CMR_L313_MINUS = prove
 (`!S (G:real^K->real^K^K) e lam Lam cc CS Cp tau n1 Q1 (c1:num->real^2) r1 n2 Q2
    (c2:num->real^2) r2 (u:real^3->real^K) mu.
     cmw_repex S G e /\ CMR_GCOND G Lam /\ &0 < e /\ &0 < lam /\
     (!z w. lam * norm w pow 2 <= w dot (G z ** w)) /\
     &0 < cc /\ cmr_dirok S G e cc /\ &0 < CS /\ cmr_stabok S G e CS /\
     &0 < Cp /\ &0 < tau /\ cmr_pbok S G e Cp tau /\ &0 < mu /\ mu <= &1 / &2 /\
     cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
     ==> cc * tau / &2 < cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u) \/
         sum(1..n2) (\j. if &0 < r2 j /\ ~cmr_inside n1 Q1 c1 r1 (Q2 j) (c2 j) (mu * r2 j)
                         then cmr_dec S G (Q2 j) (c2 j) (mu * r2 j)
                                (cmr_repn S G n1 Q1 c1 r1 u)
                         else &0)
         <= (cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 c2 (\j. (&2 * mu) * r2 j) u)) +
            (CS * sqrt(e / &2 + e pow 2 / &4) +
             Cp * sqrt((&3 * e / &2) / lam) * sqrt(&2 / cc)) *
            sqrt(cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * mu /\ &2 * mu <= &1 /\ &0 <= Cp` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. &0 < (r2:num->real) j
        ==> &0 < (&2 * mu) * r2 j /\ (&2 * mu) * r2 j <= r2 j /\ &0 < mu * r2 j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`&2 * mu`; `&1`; `(r2:num->real) j`] REAL_LE_RMUL) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_LID];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `CS:real`;
                 `n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_WDIFF) THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  MP_TAC(ASSUME `cmr_l3hyp S G e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                   (u:real^3->real^K)`) THEN
  REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. 1 <= j /\ j <= n2 ==> orthogonal_matrix((Q2:num->real^3^3) j)`
  ASSUME_TAC THENL [ASM_MESON_TAC[cmr_dfam]; ALL_TAC] THEN
  ABBREV_TAC `u1 = cmr_repn S G n1 Q1 (c1:num->real^2) r1 (u:real^3->real^K)` THEN
  (* (a) the decreases of u on the discs of radius 2 mu r *)
  SUBGOAL_THEN
   `(!k. 1 <= k /\ k <= n2 /\ &0 < (&2 * mu) * r2 k
         ==> wan_gdir (ball((c2:num->real^2) k,(&2 * mu) * r2 k)) G
               (\x. (u:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) k) x)) <= e) /\
    sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                       ~cmr_inside n1 Q1 (c1:num->real^2) r1 (Q2 j) (c2 j) (mu * r2 j)
                    then cmr_dec S G (Q2 j) (c2 j) ((&2 * mu) * r2 j) u else &0)
    <= cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 c2 (\j. (&2 * mu) * r2 j) u)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                   `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                   `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`;
                   `&2 * mu`] CMR_L3_HALF) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_ARITH `a - (a - b) = b:real`] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `&0 < (r2:num->real) j` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                   `(Q2:num->real^3^3) j`; `(c2:num->real^2) j`;
                   `(&2 * mu) * (r2:num->real) j`; `u:real^3->real^K`] CMR_DEC_FACTS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* the energies of H(u,F1) on the discs of radius 2 mu r *)
  SUBGOAL_THEN
   `!k. 1 <= k /\ k <= n2 /\ &0 < r2 k
        ==> wan_gdir (ball((c2:num->real^2) k,(&2 * mu) * r2 k)) G
              (\x. (u1:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) k) x)) <= e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `wan_gdir (ball((c2:num->real^2) k,r2 k)) G
                  (\x. (u1:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) k) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CMR_GDIR_MONO_W12 THEN EXISTS_TAC `Lam:real` THEN
      ASM_SIMP_TAC[OPEN_BALL; SUBSET_BALL] THEN
      MP_TAC(ISPECL [`S:real^K->bool`; `u1:real^3->real^K`; `(Q2:num->real^3^3) k`;
                     `(c2:num->real^2) k`; `(r2:num->real) k`] CMR_CHART_CMAP) THEN
      ASM_SIMP_TAC[cm_cmap; SUBSET_BALL];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the Dirichlet energy of the change on the caps of F2 *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `cc:real`;
                 `n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_SUMY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / &2` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  ABBREV_TAC `Y = \j. wan_dir (ball((c2:num->real^2) j,r2 j))
                        (\x. (u1:real^3->real^K)(cm_capmap ((Q2:num->real^3^3) j) x) -
                             (u:real^3->real^K)(cm_capmap (Q2 j) x))` THEN
  SUBGOAL_THEN `!j. 1 <= j /\ j <= n2 ==> &0 <= (Y:num->real) j` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Y" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CMR_CHART_DIFF_DIR_POS THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cc * sum(1..n2) (Y:num->real) <=
                &2 * (cm_sen (G:real^K->real^K^K) u - cm_sen G (u1:real^3->real^K))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC
   `?j. 1 <= j /\ j <= n2 /\
        (&0 < (r2:num->real) j /\
         ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
            ((c2:num->real^2) j) (mu * r2 j)) /\
        tau < (Y:num->real) j` THENL
   [DISJ1_TAC THEN FIRST_X_ASSUM(X_CHOOSE_THEN `j0:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(Y:num->real) j0 <= sum(1..n2) Y` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`{j0:num}`; `1..n2`; `Y:num->real`] SUM_SUBSET_SIMPLE) THEN
      REWRITE_TAC[SUM_SING; FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_NUMSEG; IN_DIFF] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `cc * tau < cc * (Y:num->real) j0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `cc * (Y:num->real) j0 <= cc * sum(1..n2) Y` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    UNDISCH_TAC `cc * sum(1..n2) (Y:num->real) <=
                 &2 * (cm_sen (G:real^K->real^K^K) u - cm_sen G (u1:real^3->real^K))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ2_TAC THEN
  (* (b) the per-ball inequalities on the discs of radius 2 mu r *)
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `Cp:real`;
                 `tau:real`; `n2:num`; `Q2:num->real^3^3`; `c2:num->real^2`;
                 `\j. (&2 * mu) * (r2:num->real) j`;
                 `\j. &0 < (r2:num->real) j /\
                      ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                        ((c2:num->real^2) j) (mu * r2 j)`;
                 `u1:real^3->real^K`; `u:real^3->real^K`] CMR_PBALL_SUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < (&2 * mu) * (r2:num->real) j /\ (&2 * mu) * r2 j <= r2 j /\
                  &0 < mu * r2 j` STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Y:num->real) j` THEN CONJ_TAC THENL
       [EXPAND_TAC "Y" THEN REWRITE_TAC[] THEN MATCH_MP_TAC CMR_CHART_DIFF_DIR_MONO THEN
        EXISTS_TAC `S:real^K->bool` THEN ASM_SIMP_TAC[];
        SUBGOAL_THEN `~(tau < (Y:num->real) j)` MP_TAC THENL
         [ASM_MESON_TAC[]; REAL_ARITH_TAC]];
      ALL_TAC] THEN
    X_GEN_TAC `rho:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`;
                   `n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`;
                   `n2:num`; `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`;
                   `u:real^3->real^K`; `j:num`; `mu * (r2:num->real) j`; `rho:real`]
                  CMR_L3_ZERO) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                        ((c2:num->real^2) j) (mu * r2 j)` THEN
        REWRITE_TAC[cmr_inside] THEN MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:num->real` (CONJUNCTS_THEN2
    (ASSUME_TAC o REWRITE_RULE[REAL_ARITH `!m r. ((&2 * m) * r) / &2 = m * r`]) MP_TAC)) THEN
  REWRITE_TAC[REAL_ARITH `!m r. ((&2 * m) * r) / &2 = m * r`] THEN
  (* (c) the error sums, before abbreviating them *)
  SUBGOAL_THEN
   `sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (mu * r2 j)
                    then wan_dir (ball(c2 j,(&2 * mu) * r2 j))
                           (\x. (u1:real^3->real^K)(cm_capmap (Q2 j) x)) +
                         wan_dir (ball(c2 j,(&2 * mu) * r2 j))
                           (\x. (u:real^3->real^K)(cm_capmap (Q2 j) x))
                    else &0) <= (&3 * e / &2) / lam`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `lam:real`; `Lam:real`;
                   `n1:num`; `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                   `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`;
                   `\j. if &0 < (r2:num->real) j then (&2 * mu) * r2 j else r2 j`;
                   `\j. &0 < (r2:num->real) j /\
                        ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                          ((c2:num->real^2) j) (mu * r2 j)`] CMR_L3_SUMX) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `j:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= c ==> b <= c`) THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `&0 < (r2:num->real) j` THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (mu * r2 j)
                         then wan_dir (ball(c2 j,(&2 * mu) * r2 j))
                                (\x. (u:real^3->real^K)(cm_capmap (Q2 j) x) -
                                     (u1:real^3->real^K)(cm_capmap (Q2 j) x))
                         else &0) /\
    sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (mu * r2 j)
                         then wan_dir (ball(c2 j,(&2 * mu) * r2 j))
                                (\x. (u:real^3->real^K)(cm_capmap (Q2 j) x) -
                                     (u1:real^3->real^K)(cm_capmap (Q2 j) x))
                         else &0) <= sum(1..n2) (Y:num->real)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE_NUMSEG; MATCH_MP_TAC SUM_LE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    (MATCH_MP_TAC CMR_CHART_DIFF_DIR_POS ORELSE MATCH_MP_TAC CMR_CHART_DIFF_DIR_MONO) THEN
    EXISTS_TAC `S:real^K->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `EE = cm_sen G (u:real^3->real^K) - cm_sen G (u1:real^3->real^K)` THEN
  (* (d) the energy differences on the good discs *)
  ABBREV_TAC `rr = \j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (mu * r2 j) then (rho:num->real) j else &0` THEN
  SUBGOAL_THEN `cmr_dfam n2 Q2 (c2:num->real^2) rr` ASSUME_TAC THENL
   [MATCH_MP_TAC CMR_DFAM_SHRINK THEN EXISTS_TAC `r2:num->real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN EXPAND_TAC "rr" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LT_REFL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mu * (r2:num->real) j < rho j /\ rho j < (&2 * mu) * r2 j` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * mu) * (r2:num->real) j <= r2 j` MP_TAC THENL
     [ASM_MESON_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (mu * r2 j)
                    then cm_gen G (ball(c2 j,rho j))
                           (\x. (u1:real^3->real^K)(cm_capmap (Q2 j) x)) -
                         cm_gen G (ball(c2 j,rho j))
                           (\x. (u:real^3->real^K)(cm_capmap (Q2 j) x))
                    else &0) =
    cmr_sen_on G u1 (cmr_fop n2 Q2 c2 rr) - cmr_sen_on G u (cmr_fop n2 Q2 c2 rr)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u:real^3->real^K`; `n2:num`;
                   `Q2:num->real^3^3`; `c2:num->real^2`; `rr:num->real`] CMR_SEN_FAM_SUM) THEN
    MP_TAC(ISPECL [`G:real^K->real^K^K`; `Lam:real`; `u1:real^3->real^K`; `n2:num`;
                   `Q2:num->real^3^3`; `c2:num->real^2`; `rr:num->real`] CMR_SEN_FAM_SUM) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[cm_smap]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
    REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "rr" THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `ball((c2:num->real^2) j,&0) = {}` SUBST1_TAC THENL
     [REWRITE_TAC[BALL_EQ_EMPTY; REAL_LE_REFL]; REWRITE_TAC[CMR_CM_GEN_EMPTY]] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cmr_sen_on G (u1:real^3->real^K) (cmr_fop n2 Q2 (c2:num->real^2) rr) -
    cmr_sen_on G (u:real^3->real^K) (cmr_fop n2 Q2 c2 rr)
    <= CS * sqrt EE * sqrt(e / &2 + e pow 2 / &4)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(a - b) <= c ==> a - b <= c`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      free_in `CS:real` (concl th))) THEN
    MATCH_MP_TAC CMR_FOP_OPEN_IN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* (e) Cauchy-Schwarz for the error term *)
  ABBREV_TAC
   `SX = sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (mu * r2 j)
                    then wan_dir (ball(c2 j,(&2 * mu) * r2 j))
                           (\x. (u1:real^3->real^K)(cm_capmap (Q2 j) x)) +
                         wan_dir (ball(c2 j,(&2 * mu) * r2 j))
                           (\x. (u:real^3->real^K)(cm_capmap (Q2 j) x))
                    else &0)` THEN
  ABBREV_TAC
   `SY = sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (mu * r2 j)
                         then wan_dir (ball(c2 j,(&2 * mu) * r2 j))
                                (\x. (u:real^3->real^K)(cm_capmap (Q2 j) x) -
                                     (u1:real^3->real^K)(cm_capmap (Q2 j) x))
                         else &0)` THEN
  SUBGOAL_THEN `&0 <= SX` ASSUME_TAC THENL
   [EXPAND_TAC "SX" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC WAN_DIR_POS THEN
    MATCH_MP_TAC(MESON[cm_cmap]
      `cm_cmap (S:real^K->bool) s (f:real^2->real^K) ==> wan_w12 s f`) THEN
    MATCH_MP_TAC CMR_CHART_CMAP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt SX <= sqrt((&3 * e / &2) / lam)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt SY <= sqrt(&2 / cc) * sqrt EE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SQRT_MUL] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(1..n2) (Y:num->real)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 / cc * EE = (&2 * EE) / cc` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cp * sqrt SX * sqrt SY <= Cp * sqrt((&3 * e / &2) / lam) * (sqrt(&2 / cc) * sqrt EE)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[SQRT_POS_LE];
    ALL_TAC] THEN
  UNDISCH_TAC
   `cmr_sen_on G (u1:real^3->real^K) (cmr_fop n2 Q2 (c2:num->real^2) rr) -
    cmr_sen_on G (u:real^3->real^K) (cmr_fop n2 Q2 c2 rr)
    <= CS * sqrt EE * sqrt(e / &2 + e pow 2 / &4)` THEN
  UNDISCH_TAC
   `Cp * sqrt SX * sqrt SY <= Cp * sqrt((&3 * e / &2) / lam) * (sqrt(&2 / cc) * sqrt EE)` THEN
  UNDISCH_TAC
   `sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                       ~cmr_inside n1 Q1 (c1:num->real^2) r1 (Q2 j) (c2 j) (mu * r2 j)
                    then cmr_dec S G (Q2 j) (c2 j) ((&2 * mu) * r2 j) (u:real^3->real^K)
                    else &0)
    <= cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 c2 (\j. (&2 * mu) * r2 j) u)` THEN
  UNDISCH_TAC
   `sum(1..n2) (\j. if &0 < (r2:num->real) j /\
                   ~cmr_inside n1 Q1 (c1:num->real^2) r1 ((Q2:num->real^3^3) j)
                     ((c2:num->real^2) j) (mu * r2 j)
                    then cm_gen G (ball(c2 j,rho j))
                           (\x. (u1:real^3->real^K)(cm_capmap (Q2 j) x)) -
                         cm_gen G (ball(c2 j,rho j))
                           (\x. (u:real^3->real^K)(cm_capmap (Q2 j) x))
                    else &0) =
    cmr_sen_on G u1 (cmr_fop n2 Q2 c2 rr) - cmr_sen_on G u (cmr_fop n2 Q2 c2 rr)` THEN
  REPEAT(POP_ASSUM(K ALL_TAC)) THEN REAL_ARITH_TAC);;

(* CM Lemma 3.11, (3.13): for 0 < mu <= 1/2 (CM: 1/8 <= mu <= 1/2), the     *)
(* decrease from replacement on the mu-scaled family after H(u,F1) is       *)
(* bounded by sqrt(E(u) - E(H(u,F1)))/kappa plus the decrease from          *)
(* replacement on the 2 mu-scaled family applied to u.                      *)

let CMR_L313 = prove
 (`!S (G:real^K->real^K^K) d e.
     cmr_ctx S G d e
     ==> ?kappa. &0 < kappa /\
           !mu n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2 (u:real^3->real^K).
             &0 < mu /\ mu <= &1 / &2 /\ cmr_l3hyp S G e n1 Q1 c1 r1 n2 Q2 c2 r2 u
             ==> cm_sen G (cmr_repn S G n1 Q1 c1 r1 u) -
                 cm_sen G (cmr_repn S G n2 Q2 c2 (\j. mu * r2 j)
                             (cmr_repn S G n1 Q1 c1 r1 u))
                 <= sqrt(cm_sen G u - cm_sen G (cmr_repn S G n1 Q1 c1 r1 u)) / kappa +
                    (cm_sen G u - cm_sen G (cmr_repn S G n2 Q2 c2 (\j. (&2 * mu) * r2 j) u))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP CMR_CTX_UNPACK) THEN
  ABBREV_TAC `C1 = CS * sqrt(e / &2 + e pow 2 / &4) +
                   Cp * sqrt((&3 * e / &2) / lam) * sqrt(&2 / cc)` THEN
  SUBGOAL_THEN `&0 < e / &2 + e pow 2 / &4 /\ &0 <= (&3 * e / &2) / lam /\ &0 <= &2 / cc`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < C1` ASSUME_TAC THENL
   [EXPAND_TAC "C1" THEN MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[SQRT_POS_LT];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LE] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[SQRT_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(cc * tau / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `min (inv C1) (sqrt(cc * tau / &2) / (e / &2))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `lam:real`; `Lam:real`;
                 `cc:real`; `CS:real`; `Cp:real`; `tau:real`; `n1:num`; `Q1:num->real^3^3`;
                 `c1:num->real^2`; `r1:num->real`; `n2:num`; `Q2:num->real^3^3`;
                 `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`; `mu:real`]
                CMR_L313_MINUS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`;
                 `mu:real`] CMR_L313_PLUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`]
                CMR_L3_CAPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`; `u:real^3->real^K`;
                 `&2 * mu`] CMR_L3_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(ASSUME `cmr_l3hyp S G e n1 Q1 (c1:num->real^2) r1 n2 Q2 (c2:num->real^2) r2
                   (u:real^3->real^K)`) THEN
  REWRITE_TAC[cmr_l3hyp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n1:num`;
                 `Q1:num->real^3^3`; `c1:num->real^2`; `r1:num->real`; `u:real^3->real^K`]
                CMR_L3_DROP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e / &2` THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `Lam:real`; `n2:num`;
                 `Q2:num->real^3^3`; `c2:num->real^2`; `r2:num->real`;
                 `cmr_repn S G n1 Q1 (c1:num->real^2) r1 (u:real^3->real^K)`; `e / &2`;
                 `mu:real`] CMR_FAM_SCALE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  DISCH_THEN(fun th ->
    SUBGOAL_THEN
     `sum(1..n2) (\j. if &0 < r2 j /\ cmr_inside n1 Q1 (c1:num->real^2) r1
                                       ((Q2:num->real^3^3) j) ((c2:num->real^2) j) (mu * r2 j)
                     then cmr_dec S G (Q2 j) (c2 j) (mu * r2 j)
                            (cmr_repn S G n1 Q1 c1 r1 (u:real^3->real^K)) else &0) +
      sum(1..n2) (\j. if &0 < r2 j /\ ~cmr_inside n1 Q1 c1 r1 (Q2 j) (c2 j) (mu * r2 j)
                     then cmr_dec S G (Q2 j) (c2 j) (mu * r2 j)
                            (cmr_repn S G n1 Q1 c1 r1 u) else &0) =
      cm_sen G (cmr_repn S G n1 Q1 c1 r1 u) -
      cm_sen G (cmr_repn S G n2 Q2 c2 (\j. mu * r2 j) (cmr_repn S G n1 Q1 c1 r1 u))`
    ASSUME_TAC THENL
     [REWRITE_TAC[th; REAL_ARITH `u - (u - s) = s:real`; GSYM SUM_ADD_NUMSEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      ASM_CASES_TAC `&0 < (r2:num->real) j` THEN ASM_REWRITE_TAC[REAL_ADD_LID] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID];
      ALL_TAC]) THEN
  MATCH_MP_TAC CMR_L313_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`sum(1..n2) (\j. if &0 < r2 j /\ cmr_inside n1 Q1 (c1:num->real^2) r1
                                       ((Q2:num->real^3^3) j) ((c2:num->real^2) j) (mu * r2 j)
                     then cmr_dec S G (Q2 j) (c2 j) (mu * r2 j)
                            (cmr_repn S G n1 Q1 c1 r1 (u:real^3->real^K)) else &0)`;
    `sum(1..n2) (\j. if &0 < r2 j /\ ~cmr_inside n1 Q1 (c1:num->real^2) r1
                                       ((Q2:num->real^3^3) j) ((c2:num->real^2) j) (mu * r2 j)
                     then cmr_dec S G (Q2 j) (c2 j) (mu * r2 j)
                            (cmr_repn S G n1 Q1 c1 r1 (u:real^3->real^K)) else &0)`;
    `C1:real`; `e:real`; `cc:real`; `tau:real`] THEN
  ASM_REWRITE_TAC[]);;

