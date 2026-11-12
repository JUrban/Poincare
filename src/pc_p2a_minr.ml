(* ========================================================================= *)
(* pc_p2a_minr: restrictions of minimizers are minimizers (L3,               *)
(* P2A_MIN_RESTRICT_STATEMENT).  A competitor on [0,b'] is glued to the      *)
(* minimizer on [b',b], and the L-length splits additively at b'.  Contents: *)
(* locality of the velocity, the speed and the L-integrand (at interior      *)
(* times they see only the curve near that time), restriction of admissible  *)
(* curves, gluing of admissible curves, and L3.                              *)
(* ========================================================================= *)

needs "src/pc_p2a_defs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Locality.  At an interior time the velocity within [a,b] is the two-     *)
(* sided derivative, so it does not depend on the interval; it depends only *)
(* on the curve on a closed interval around that time (GRGD_VELOCITY_EQ).   *)
(* ------------------------------------------------------------------------- *)

let P2A_VELOCITY_INTERIOR = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (gamma:real->A) a b a' b' t.
        a < t /\ t < b /\ a' < t /\ t < b'
        ==> mfd_velocity atlas gamma a b t = mfd_velocity atlas gamma a' b' t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_velocity] THEN
  SUBGOAL_THEN `lift t IN interior(interval[lift a,lift b]) /\
                lift t IN interior(interval[lift a',lift b'])`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; IN_INTERVAL_1; LIFT_DROP];
    ASM_SIMP_TAC[VECTOR_DERIVATIVE_WITHIN_INTERIOR]]);;

let P2A_SPEED_INTERIOR = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (gamma:real->A)
     a b a' b' t.
        a < t /\ t < b /\ a' < t /\ t < b'
        ==> mfd_speed atlas g gamma a b t = mfd_speed atlas g gamma a' b' t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_speed] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `gamma:real->A`;
                 `a:real`; `b:real`; `a':real`; `b':real`; `t:real`]
         P2A_VELOCITY_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let P2A_SPEED_EQ = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (gamma:real->A)
     gamma' a b t.
        (!s. s IN real_interval[a,b] ==> gamma s = gamma' s) /\
        t IN real_interval[a,b]
        ==> mfd_speed atlas g gamma a b t = mfd_speed atlas g gamma' a b t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mfd_speed] THEN
  MP_TAC(ISPECL [`atlas:((A->bool)#(A->real^N))->bool`; `gamma:real->A`;
                 `gamma':real->A`; `a:real`; `b:real`; `t:real`]
         GRGD_VELOCITY_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(gamma:real->A) t = gamma' t` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; REFL_TAC]);;

let P2A_SPEED_LOCAL = prove
 (`!(atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N) (gamma1:real->A)
     gamma2 a1 b1 a2 b2 a c t.
        a1 <= a /\ a2 <= a /\ a < t /\ t < c /\ c <= b1 /\ c <= b2 /\
        (!s. s IN real_interval[a,c] ==> gamma1 s = gamma2 s)
        ==> mfd_speed atlas g gamma1 a1 b1 t = mfd_speed atlas g gamma2 a2 b2 t`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `mfd_speed (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
              (gamma1:real->A) a c t` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_SPEED_INTERIOR THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `mfd_speed (atlas:((A->bool)#(A->real^N))->bool) (g:A->real^N^N)
              (gamma2:real->A) a c t` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_SPEED_EQ THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC P2A_SPEED_INTERIOR THEN ASM_REAL_ARITH_TAC]);;

(* The L-integrand at an interior time of [a,c] depends only on the curve   *)
(* on [a,c], not on the end b of the parameter interval.                   *)

let P2A_LINT_LOCAL = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt (gamma1:real->A) gamma2 b1 b2 a c tau.
        &0 <= a /\ a < tau /\ tau < c /\ c <= b1 /\ c <= b2 /\
        (!s. s IN real_interval[a,c] ==> gamma1 s = gamma2 s)
        ==> p2a_L_integrand V tt gamma1 b1 tau =
            p2a_L_integrand V tt gamma2 b2 tau`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2a_L_integrand] THEN
  SUBGOAL_THEN `(gamma1:real->A) tau = gamma2 tau` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC P2A_SPEED_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `c:real`] THEN ASM_REWRITE_TAC[]);;

(* Integrals over [a,c] only see the integrand on the open interval.       *)

let P2A_REAL_INTEGRAL_OPEN_EQ = prove
 (`!f g a c.
        (!t. a < t /\ t < c ==> f t = g t)
        ==> (f real_integrable_on real_interval[a,c] <=>
             g real_integrable_on real_interval[a,c]) /\
            real_integral (real_interval[a,c]) f =
            real_integral (real_interval[a,c]) g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_INTEGRABLE_ON_OPEN_INTERVAL;
              GSYM REAL_INTEGRAL_OPEN_INTERVAL] THEN
  SUBGOAL_THEN `!t. t IN real_interval(a,c) ==> (f:real->real) t = g t`
  ASSUME_TAC THENL [ASM_SIMP_TAC[IN_REAL_INTERVAL]; ALL_TAC] THEN
  CONJ_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_EQ THENL
     [EXISTS_TAC `f:real->real`; EXISTS_TAC `g:real->real`] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_INTEGRAL_EQ THEN ASM_REWRITE_TAC[]]);;

(* Transfer of a chart-level C^1 property to a smaller set on which the    *)
(* curve agrees with another one.                                          *)

let P2A_CD_TRANSFER = prove
 (`!(c:(A->bool)#(A->real^N)) (gamma1:real->A) S1.
        continuously_differentiable 1 S1 (\s. SND c (gamma1(drop s)))
        ==> !gg S2. (!s. s IN S2 ==> s IN S1 /\ gg(drop s) = gamma1(drop s))
                    ==> continuously_differentiable 1 S2
                          (\s. SND c (gg(drop s)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MFDM_CONTINUOUSLY_DIFFERENTIABLE_EQ THEN
  EXISTS_TAC `\s:real^1. SND (c:(A->bool)#(A->real^N)) ((gamma1:real->A)(drop s))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CONTINUOUSLY_DIFFERENTIABLE_SUBSET THEN
    EXISTS_TAC `S1:real^1->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Restriction of admissible curves from [0,b] to [0,b'].                   *)
(* ------------------------------------------------------------------------- *)

let P2A_PC1_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt (gamma:real->A) a b b' P.
        p2a_pc1 V tt gamma a b P /\ b' <= b ==> p2a_pc1 V tt gamma a b' P`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_pc1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G"))
                             ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  USE_THEN "G" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "R") (LABEL_TAC "T")))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "R" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    USE_THEN "T" (MP_TAC o C MP (ASSUME `~((s0:real) IN P)`)) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let P2A_ADM_RESTRICT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x b b' (gamma:real->A).
        p2a_adm V tt x b gamma /\ &0 < b' /\ b' <= b
        ==> p2a_adm V tt x b' gamma`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`tau0:real`; `O:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `P:real->bool` THEN MATCH_MP_TAC P2A_PC1_RESTRICT THEN
    EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL
     [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt (gamma:real->A) b`;
      `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                          (real->A->real^N^N)) tt (gamma:real->A) b'`;
      `&0`; `b':real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `b':real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]);;

(* The L-length splits at b'.                                               *)

let P2A_LENGTH_SPLIT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x (gamma:real->A) b b'.
        p2a_adm V tt x b gamma /\ &0 < b' /\ b' <= b
        ==> p2a_L_length V tt gamma b =
            p2a_L_length V tt gamma b' +
            real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_adm] THEN STRIP_TAC THEN
  REWRITE_TAC[p2a_L_length] THEN
  MP_TAC(ISPECL
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b`;
    `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b'`;
    `&0`; `b':real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b':real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Gluing: gg is gamma' up to b' and gamma from b' on (they agree at b').   *)
(* ------------------------------------------------------------------------- *)

let P2A_GLUE_CONT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt (gamma:real->A) gamma' gg b b'.
        (!tau0 O. &0 <= tau0 /\ tau0 <= b /\ open_in (p2a_vtop V (tt - tau0)) O /\
                  gamma tau0 IN O
                  ==> ?d. &0 < d /\
                          !tau. &0 <= tau /\ tau <= b /\ abs(tau - tau0) < d
                                ==> gamma tau IN O) /\
        (!tau0 O. &0 <= tau0 /\ tau0 <= b' /\ open_in (p2a_vtop V (tt - tau0)) O /\
                  gamma' tau0 IN O
                  ==> ?d. &0 < d /\
                          !tau. &0 <= tau /\ tau <= b' /\ abs(tau - tau0) < d
                                ==> gamma' tau IN O) /\
        b' < b /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> !tau0 O. &0 <= tau0 /\ tau0 <= b /\
                     open_in (p2a_vtop V (tt - tau0)) O /\ gg tau0 IN O
                     ==> ?d. &0 < d /\
                             !tau. &0 <= tau /\ tau <= b /\ abs(tau - tau0) < d
                                   ==> gg tau IN O`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C") (CONJUNCTS_THEN2 (LABEL_TAC "C'")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "E1")
     (LABEL_TAC "E2"))))) THEN
  MAP_EVERY X_GEN_TAC [`tau0:real`; `O:A->bool`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `tau0 < b'` THENL
   [SUBGOAL_THEN `(gamma':real->A) tau0 IN O` ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) tau0 = gamma' tau0`
        (fun th -> ASM_MESON_TAC[th]) THEN
      USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "C'" (MP_TAC o SPECL [`tau0:real`; `O:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "D1"))) THEN
    MP_TAC(SPECL [`d1:real`; `b' - tau0`] REAL_DOWN2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
     [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "D1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `tau0:real = b'` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(gamma':real->A) b' IN O /\ (gamma:real->A) b' IN O`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) b' = gamma' b' /\ (gg:real->A) b' = gamma b'`
        (fun th -> ASM_MESON_TAC[th]) THEN
      CONJ_TAC THENL [USE_THEN "E1" MATCH_MP_TAC; USE_THEN "E2" MATCH_MP_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "C'" (MP_TAC o SPECL [`b':real`; `O:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "D1"))) THEN
    USE_THEN "C" (MP_TAC o SPECL [`b':real`; `O:A->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "D2"))) THEN
    MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `tau <= b'` THENL
     [SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "D1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "D2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `b' < tau0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) tau0 IN O` ASSUME_TAC THENL
   [SUBGOAL_THEN `(gg:real->A) tau0 = gamma tau0`
      (fun th -> ASM_MESON_TAC[th]) THEN
    USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "C" (MP_TAC o SPECL [`tau0:real`; `O:A->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "D1"))) THEN
  MP_TAC(SPECL [`d1:real`; `tau0 - b'`] REAL_DOWN2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `tau:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
   [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "D1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let P2A_GLUE_PC1 = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt (gamma:real->A) gamma' gg b b' P P'.
        p2a_pc1 V tt gamma (&0) b P /\ p2a_pc1 V tt gamma' (&0) b' P' /\
        &0 < b' /\ b' < b /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> p2a_pc1 V tt gg (&0) b (b' INSERT (P UNION P'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_pc1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G"))
   (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G'"))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "E1") (LABEL_TAC "E2")))))) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_UNION] THEN
  MAP_EVERY X_GEN_TAC [`s0:real`; `c:(A->bool)#(A->real^N)`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT; IN_UNION; DE_MORGAN_THM] THEN
  ASM_CASES_TAC `s0 < b'` THENL
   [SUBGOAL_THEN `(gamma':real->A) s0 IN FST(c:(A->bool)#(A->real^N))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) s0 = gamma' s0` (fun th -> ASM_MESON_TAC[th]) THEN
      USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "G'" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "R1")
      (LABEL_TAC "T1"))))) THEN
    MP_TAC(SPECL [`d1:real`; `(b' - s0) / &2`] REAL_DOWN2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "L1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
      USE_THEN "R1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
      STRIP_TAC THEN
      USE_THEN "T1" (MP_TAC o C MP (ASSUME `~((s0:real) IN P')`)) THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER)] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `(gg:real->A)(drop s) = gamma'(drop s)` SUBST_ALL_TAC THENL
      [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `s0:real = b'` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(gamma':real->A) b' IN FST(c:(A->bool)#(A->real^N)) /\
                  (gamma:real->A) b' IN FST c` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(gg:real->A) b' = gamma' b' /\ (gg:real->A) b' = gamma b'`
        (fun th -> ASM_MESON_TAC[th]) THEN
      CONJ_TAC THENL [USE_THEN "E1" MATCH_MP_TAC; USE_THEN "E2" MATCH_MP_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "G'" (MP_TAC o SPECL [`b':real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "L1") (K ALL_TAC)))) THEN
    USE_THEN "G" (MP_TAC o SPECL [`b':real`; `c:(A->bool)#(A->real^N)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "R2")
      (K ALL_TAC))))) THEN
    MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "L1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gg:real->A)(drop s) = gamma'(drop s)` SUBST_ALL_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "R2" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(gg:real->A)(drop s) = gamma(drop s)` SUBST_ALL_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `b' < s0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(gamma:real->A) s0 IN FST(c:(A->bool)#(A->real^N))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(gg:real->A) s0 = gamma s0` (fun th -> ASM_MESON_TAC[th]) THEN
    USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "G" (MP_TAC o SPECL [`s0:real`; `c:(A->bool)#(A->real^N)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "L1") (CONJUNCTS_THEN2 (LABEL_TAC "R1")
    (LABEL_TAC "T1"))))) THEN
  MP_TAC(SPECL [`d1:real`; `(s0 - b') / &2`] REAL_DOWN2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "L1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
    USE_THEN "R1" (MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER);
    STRIP_TAC THEN
    USE_THEN "T1" (MP_TAC o C MP (ASSUME `~((s0:real) IN P)`)) THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP P2A_CD_TRANSFER)] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^1` THEN STRIP_TAC THEN
  (SUBGOAL_THEN `(gg:real->A)(drop s) = gamma(drop s)` SUBST_ALL_TAC THENL
    [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let P2A_GLUE_LINT = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt (gamma:real->A) gamma' gg b b'.
        p2a_L_integrand V tt gamma b real_integrable_on real_interval[&0,b] /\
        p2a_L_integrand V tt gamma' b' real_integrable_on real_interval[&0,b'] /\
        &0 < b' /\ b' < b /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> p2a_L_integrand V tt gg b real_integrable_on real_interval[&0,b] /\
            p2a_L_length V tt gg b =
            p2a_L_length V tt gamma' b' +
            real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "E1") (LABEL_TAC "E2")))))) THEN
  SUBGOAL_THEN `&0 <= b' /\ b' <= b` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gg:real->A) b`;
    `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma':real->A) b'`;
    `&0`; `b':real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b':real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I1") (LABEL_TAC "J1")) THEN
  MP_TAC(ISPECL
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gg:real->A) b`;
    `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gamma:real->A) b`;
    `b':real`; `b:real`] P2A_REAL_INTEGRAL_OPEN_EQ) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN MATCH_MP_TAC P2A_LINT_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`b':real`; `b:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN USE_THEN "E2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I2") (LABEL_TAC "J2")) THEN
  SUBGOAL_THEN
   `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)) tt (gg:real->A) b
      real_integrable_on real_interval[&0,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `b':real` THEN
    REMOVE_THEN "I1" (fun th -> REWRITE_TAC[th]) THEN
    REMOVE_THEN "I2" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`&0`; `b:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[p2a_L_length] THEN
  MP_TAC(ISPECL
   [`p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                        (real->A->real^N^N)) tt (gg:real->A) b`;
    `&0`; `b:real`; `b':real`] REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REMOVE_THEN "J1" SUBST1_TAC THEN REMOVE_THEN "J2" SUBST1_TAC THEN REFL_TAC);;

let P2A_GLUE = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x (gamma:real->A) gamma' gg b b'.
        p2a_adm V tt x b gamma /\ p2a_adm V tt x b' gamma' /\ b' < b /\
        (!tau. tau <= b' ==> gg tau = gamma' tau) /\
        (!tau. b' <= tau ==> gg tau = gamma tau)
        ==> p2a_adm V tt x b gg /\
            p2a_L_length V tt gg b =
            p2a_L_length V tt gamma' b' +
            real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2a_adm] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "E1")
    (LABEL_TAC "E2"))))) THEN
  SUBGOAL_THEN
   `p2a_L_integrand (V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                       (real->A->real^N^N)) tt (gg:real->A) b
      real_integrable_on real_interval[&0,b] /\
    p2a_L_length V tt gg b =
    p2a_L_length V tt gamma' b' +
    real_integral (real_interval[b',b]) (p2a_L_integrand V tt gamma b)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC P2A_GLUE_LINT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [TRANS_TAC EQ_TRANS `(gamma':real->A)(&0)` THEN CONJ_TAC THENL
     [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau <= b'` THENL
     [SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC P2A_GLUE_CONT THEN
    MAP_EVERY EXISTS_TAC [`gamma:real->A`; `gamma':real->A`; `b':real`] THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `b' INSERT ((P:real->bool) UNION P')` THEN
    MATCH_MP_TAC P2A_GLUE_PC1 THEN
    MAP_EVERY EXISTS_TAC [`gamma:real->A`; `gamma':real->A`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `tau:real` THEN STRIP_TAC THEN ASM_CASES_TAC `tau <= b'` THENL
     [SUBGOAL_THEN `(gg:real->A) tau = gamma' tau` SUBST1_TAC THENL
       [USE_THEN "E1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(gg:real->A) tau = gamma tau` SUBST1_TAC THENL
       [USE_THEN "E2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* L3: restrictions of minimizers are minimizers (generic in N; the slice   *)
(* hypotheses p2a_svs and p2a_bsmooth of the statement are not needed).     *)
(* ------------------------------------------------------------------------- *)

let P2A_MIN_RESTRICT_GEN = prove
 (`!(V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
       (real->A->real^N^N)) tt x b b' (gamma:real->A).
        p2a_min V tt x b gamma /\ &0 < b' /\ b' <= b
        ==> p2a_min V tt x b' gamma`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `b':real = b` THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[p2a_min] THEN STRIP_TAC THEN
  SUBGOAL_THEN `b' < b /\ ~(b <= b')` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2A_ADM_RESTRICT THEN EXISTS_TAC `b:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `gamma':real->A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`;
                 `b:real`; `b':real`] P2A_LENGTH_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`V:(real->A topology)#(real->((A->bool)#(A->real^N))->bool)#
                    (real->A->real^N^N)`; `tt:real`; `x:A`; `gamma:real->A`;
                 `gamma':real->A`;
                 `\tau. if tau <= b' then (gamma':real->A) tau else gamma tau`;
                 `b:real`; `b':real`] P2A_GLUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SIMP_TAC[];
      X_GEN_TAC `tau:real` THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [SUBGOAL_THEN `tau:real = b'` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
        REFL_TAC]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `\tau. if tau <= b' then (gamma':real->A) tau else gamma tau`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let P2A_MIN_RESTRICT = prove
 (`!u:A->bool. P2A_MIN_RESTRICT_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[P2A_MIN_RESTRICT_STATEMENT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC P2A_MIN_RESTRICT_GEN THEN
  EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[]);;

