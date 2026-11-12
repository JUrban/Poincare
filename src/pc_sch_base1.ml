(* ========================================================================= *)
(* Unit pc_sch_base1: the one-saddle base case of the smooth Schoenflies     *)
(* induction, SCH_BASE1 |- SCH_BASE1_STATEMENT, part H4 of that case (H1     *)
(* pc_sch_b1cls, H2 pc_sch_b1chart, H3 pc_sch_b1canc, H4 this unit).         *)
(*                                                                           *)
(* Route.  pc_sch_b1cls reduces SCH_BASE1_STATEMENT to the cancellation step *)
(* SCHY_CANCEL_STATEMENT (given the saddle-free base case of pc_sch_base0,   *)
(* the level necks of pc_sch_level2 and the single cut of pc_sch_surg).      *)
(* Here the cancellation step is assembled: the level neck of the innermost  *)
(* component C (pc_sch_level2), the chart near C with explicit facts near    *)
(* the left branch point (pc_sch_b1chart), the cut along the slab            *)
(* (pc_sch_surg, through pc_sch_b1cut), and the shear of pc_sch_b1canc that  *)
(* removes the critical points of the lower piece S1 near its saddle.  The   *)
(* sheared S1 is a Morse sphere without saddles, hence bounds a ball         *)
(* (pc_sch_base0), so S1 does; the upper piece S2 has no saddle              *)
(* (pc_sch_base0); the gluing of pc_sch_glue gives the ball for S.           *)
(* ========================================================================= *)

needs "src/pc_sch_b1canc.ml";;
needs "src/pc_sch_b1cut.ml";;
needs "src/pc_sch_level2.ml";;
needs "src/pc_sch_base0.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The two pieces of a slab configuration are disjoint; an                   *)
(* ambient diffeomorphism Phi that is the identity off a compact set L maps  *)
(* L onto itself and does not move a sphere off L; for a Morse neck g1      *)
(* whose saddles lie in L, and whose critical points for Phi o g1 are those *)
(* of g1 off L, Phi o g1 is a Morse neck without saddles.                   *)
(* ------------------------------------------------------------------------- *)

let SCHB1_SLAB_DISJOINT = prove
 (`!S S1 S2 (Theta:real^3->real^3).
     sch_slab_config S S1 S2 Theta ==> DISJOINT S1 S2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_slab_config] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:real^3->bool` (X_CHOOSE_THEN `TN:real^3->real^3`
    (X_CHOOSE_THEN `E1:real^3->bool` (X_CHOOSE_THEN `E2:real^3->bool`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  SUBGOAL_THEN `sch_cap1 SUBSET (N:real^3->bool) /\ sch_cap2 SUBSET N` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `sch_slab_nbhd` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; sch_cap1; sch_cap2; sch_slab_nbhd; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(SPEC `--((x:real^3)$3)` SCHY_PROFILE_LE1) THEN
    MP_TAC(SPEC `(x:real^3)$3` SCHY_PROFILE_LE1) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN N ==> (TN:real^3->real^3)((Theta:real^3->real^3) y) = y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on N (IMAGE (Theta:real^3->real^3) N) Theta TN` THEN
    REWRITE_TAC[diffeomorphism_on] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y:real^3. y IN sch_cap1 ==> y$3 <= --(&1 / &2)) /\
                (!y:real^3. y IN sch_cap2 ==> &1 / &2 <= y$3)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[sch_cap1; sch_cap2; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sch_cap2 ==> ~((Theta:real^3->real^3) y IN E1)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN N /\ &1 / &2 <= y$3` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN sch_cap1 ==> ~((Theta:real^3->real^3) y IN E2)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN N /\ y$3 <= --(&1 / &2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y1 y2. y1 IN sch_cap1 /\ y2 IN sch_cap2
                        ==> ~((Theta:real^3->real^3) y1 = Theta y2)` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y1:real^3`; `y2:real^3`] THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y1:real^3) IN N /\ (y2:real^3) IN N` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(y1:real^3) = y2` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y1:real^3)$3 <= --(&1 / &2) /\ &1 / &2 <= (y2:real^3)$3` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION; IN_IMAGE; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[IN_DISJOINT]);;

let SCHB1_PHI_INTO = prove
 (`!(Phi:real^3->real^3) Phi' L.
     diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\ (!x. ~(x IN L) ==> Phi x = x)
     ==> !x. Phi x IN L <=> x IN L`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on; IN_UNIV] THEN STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let SCHB1_IMAGE_OFF = prove
 (`!(Phi:real^3->real^3) Phi' L (g1:real^3->real^3) s.
     diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\ (!x. ~(x IN L) ==> Phi x = x)
     ==> IMAGE (Phi o g1) s INTER ((:real^3) DIFF L) =
         IMAGE g1 s INTER ((:real^3) DIFF L)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHB1_PHI_INTO) THEN
  FIRST_X_ASSUM(ASSUME_TAC o CONJUNCT2) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNIV; IN_IMAGE; o_THM] THEN
  ASM_MESON_TAC[]);;

let SCHB1_PHI_NECK = prove
 (`!(Phi:real^3->real^3) Phi' (g1:real^3->real^3) g1'.
     diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\ sch_neck g1 g1'
     ==> sch_neck (Phi o g1) (g1' o Phi')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_neck] THEN STRIP_TAC THEN
  REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
  EXISTS_TAC `IMAGE (g1:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `diffeomorphism_on (annulus (&1 / &2) (&2))
                 (IMAGE (g1:real^3->real^3) (annulus (&1 / &2) (&2))) g1 g1'` THEN
  SIMP_TAC[diffeomorphism_on]);;

let SCHB1_PHI_MORSE = prove
 (`!(Phi:real^3->real^3) Phi' L (g1:real^3->real^3).
     diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\ sch_morse g1 /\
     compact L /\ (!x. ~(x IN L) ==> Phi x = x) /\
     (!t. sch_crit (Phi o g1) t <=> sch_crit g1 t /\ ~(g1 t IN L)) /\
     (!t. t IN sch_saddles g1 ==> g1 t IN L)
     ==> sch_morse (Phi o g1) /\ sch_saddles (Phi o g1) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open ((:real^3) DIFF L)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^3->real^3`; `Phi':real^3->real^3`; `L:real^3->bool`;
                 `g1:real^3->real^3`; `sphere(vec 0:real^3,&1)`] SCHB1_IMAGE_OFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!t. sch_crit ((Phi:real^3->real^3) o g1) t
                    ==> (Phi o g1) t = (g1:real^3->real^3) t /\ ~(g1 t IN L)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[o_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `sch_morse (g1:real^3->real^3)` THEN REWRITE_TAC[sch_morse] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "INJ") (LABEL_TAC "HC"))) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{t | sch_crit (g1:real^3->real^3) t}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real^3`; `t':real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `sch_crit (g1:real^3->real^3) t /\ sch_crit g1 t' /\
                  ((Phi:real^3->real^3) o g1) t = g1 t /\ (Phi o g1) t' = g1 t'`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(((Phi:real^3->real^3) o (g1:real^3->real^3)) t)$3 = ((Phi o g1) t')$3` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `sch_crit (g1:real^3->real^3) t /\ ((Phi:real^3->real^3) o g1) t = g1 t /\
                  ~(g1 t IN L)` STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "HC" (fun th -> MP_TAC(MP (SPEC `t:real^3` th)
      (ASSUME `sch_crit (g1:real^3->real^3) t`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `k1:real` (X_CHOOSE_TAC `k2:real`)) THEN
    MAP_EVERY EXISTS_TAC [`k1:real`; `k2:real`] THEN
    MATCH_MP_TAC SCH3_HCHART_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (g1:real^3->real^3) (sphere(vec 0,&1))`; `(:real^3) DIFF L`] THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; sch_saddles; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `sch_crit (g1:real^3->real^3) t /\ ((Phi:real^3->real^3) o g1) t = g1 t /\
                  ~(g1 t IN L)` STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `sch_hchart (IMAGE ((Phi:real^3->real^3) o (g1:real^3->real^3)) (sphere(vec 0,&1)))
                   ((Phi o g1) t) (&1) (-- &1)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(t:real^3) IN sch_saddles g1` (fun th -> ASM_MESON_TAC[th]) THEN
    REWRITE_TAC[sch_saddles; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCH3_HCHART_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`IMAGE ((Phi:real^3->real^3) o (g1:real^3->real^3)) (sphere(vec 0,&1))`;
                          `(:real^3) DIFF L`] THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV]]);;

(* ------------------------------------------------------------------------- *)
(* The cancellation step SCHY_CANCEL_STATEMENT and the                       *)
(* one-saddle base case SCH_BASE1.                                           *)
(* ------------------------------------------------------------------------- *)

(* The slab thickness lam avoids the finitely many critical heights.        *)

let SCHB1_LAM_CHOICE = prove
 (`!(g:real^3->real^3) e a.
     sch_morse g /\ &0 < a
     ==> ?lam. &0 < lam /\ lam < a /\
               (!t. sch_crit g t ==> ~((g t)$3 = e + lam / &2) /\ ~((g t)$3 = e - lam / &2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (\t. &2 * (((g:real^3->real^3) t)$3 - e)) {t | sch_crit g t} UNION
                  IMAGE (\t. &2 * (e - ((g:real^3->real^3) t)$3)) {t | sch_crit g t}`;
                 `a:real`] SCHY_AVOID_FINITE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN MATCH_MP_TAC FINITE_IMAGE THEN
    ASM_MESON_TAC[sch_morse];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `lam:real` THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NB"))) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^3` THEN DISCH_TAC THEN
  CONJ_TAC THEN DISCH_TAC THEN USE_THEN "NB" MP_TAC THEN REWRITE_TAC[] THENL
   [DISJ1_TAC; DISJ2_TAC] THEN EXISTS_TAC `t:real^3` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

(* The end of the argument: the sheared lower piece and the upper piece     *)
(* bound balls (pc_sch_base0), hence so does S (pc_sch_glue).               *)

let SCHB1_FINISH = prove
 (`!(g:real^3->real^3) g' g1 g1' g2 g2' (Theta:real^3->real^3) e0 (Phi:real^3->real^3) Phi'
    L t0.
     sch_neck g g' /\ sch_morse g /\ CARD(sch_saddles g) = 1 /\
     t0 IN sch_saddles g /\ g t0 = vec 0 /\
     sch_neck g1 g1' /\ sch_morse g1 /\ sch_neck g2 g2' /\ sch_morse g2 /\
     sch_slab_config (IMAGE g (sphere(vec 0,&1))) (IMAGE g1 (sphere(vec 0,&1)))
                     (IMAGE g2 (sphere(vec 0,&1))) Theta /\
     &0 < e0 /\ e0 <= &1 / &16 /\
     (!x. x IN sch_capcone
          ==> g1 x = Theta(sch_cap_collar e0 x) /\
              g2(sch_flip3 x) = Theta(sch_flip3(sch_cap_collar e0 x))) /\
     CARD(sch_saddles g1) + CARD(sch_saddles g2) = CARD(sch_saddles g) /\
     IMAGE g1 (sch_saddles g1) UNION IMAGE g2 (sch_saddles g2) = IMAGE g (sch_saddles g) /\
     diffeomorphism_on (:real^3) (:real^3) Phi Phi' /\ compact L /\
     (!x. ~(x IN L) ==> Phi x = x) /\ vec 0 IN L /\
     vec 0 IN IMAGE g1 (sphere(vec 0,&1)) /\
     (!t. sch_crit (Phi o g1) t <=> sch_crit g1 t /\ ~(g1 t IN L))
     ==> sch_bounds_ball (IMAGE g (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(vec 0:real^3 IN IMAGE (g2:real^3->real^3) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP SCHB1_SLAB_DISJOINT) THEN
    UNDISCH_TAC `vec 0:real^3 IN IMAGE (g1:real^3->real^3) (sphere(vec 0,&1))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `g1:real^3->real^3`; `g2:real^3->real^3`; `t0:real^3`]
    SCHY_SADDLE_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t1:real^3` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `!t. t IN sch_saddles g1 ==> (g1:real^3->real^3) t IN L` ASSUME_TAC THENL
   [SUBGOAL_THEN `{t1:real^3} = sch_saddles g1` (fun th -> REWRITE_TAC[GSYM th; IN_SING]) THENL
     [MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_SIMP_TAC[SCHY_SADDLES_FINITE; SING_SUBSET; CARD_SING];
      GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^3->real^3`; `Phi':real^3->real^3`; `L:real^3->bool`;
                 `g1:real^3->real^3`] SCHB1_PHI_MORSE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^3->real^3`; `Phi':real^3->real^3`; `g1:real^3->real^3`;
                 `g1':real^3->real^3`] SCHB1_PHI_NECK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `sch_bounds_ball (IMAGE (g1:real^3->real^3) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH_BOUNDS_BALL_DIFFEO THEN
    MAP_EVERY EXISTS_TAC [`Phi:real^3->real^3`; `Phi':real^3->real^3`] THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(REWRITE_RULE[SCH_BASE0_STATEMENT] SCH_BASE0) THEN
    EXISTS_TAC `(g1':real^3->real^3) o (Phi':real^3->real^3)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sch_bounds_ball (IMAGE (g2:real^3->real^3) (sphere(vec 0,&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SCH_BASE0_STATEMENT] SCH_BASE0) THEN
    EXISTS_TAC `g2':real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[SCH_SLAB_GLUE_STATEMENT] SCH6_SLAB_GLUE) THEN
  MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `g1:real^3->real^3`; `g1':real^3->real^3`;
                        `g2:real^3->real^3`; `g2':real^3->real^3`; `Theta:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `e0:real` THEN ASM_REWRITE_TAC[]);;

(* The context schy_ctx of pc_sch_b1canc from the facts of the chart.       *)

let SCHB1_CTX = prove
 (`!(g:real^3->real^3) r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H
    (Theta:real^3->real^3) Theta'.
     schy_chart (IMAGE g (sphere(vec 0,&1))) r /\ &0 < e /\ &16 * e < r pow 2 /\
     C IN components(sch_level g e) /\ schy_lpt e IN C /\ ~(schy_rpt e IN C) /\
     (!x:real^2. x IN inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C)
                 ==> ~((vector[x$1; x$2; e]:real^3) IN IMAGE g (sphere(vec 0,&1)))) /\
     sch_ball c c' /\ C = IMAGE (\z. sch5v_at e (c z)) (sphere(vec 0,&1)) /\
     IMAGE c (ball(vec 0,&1)) = inside(IMAGE (\y:real^3. vector[y$1; y$2]:real^2) C) /\
     c(--basis 1) = vector[--(sqrt e); &0] /\
     smooth_map_on (:real^3) v /\ (!y. ode_vf_maxint v (:real^3) y = (:real^1)) /\
     (!y. norm(v y) <= B) /\ (!y. (v y)$3 = &1) /\
     &0 < rho0 /\ (!x. dist(x,schy_lpt e) < rho0 ==> v x = schy_v0 x /\ x$1 < &0) /\
     &0 < delta1 /\
     (!z. dist(z,--basis 1) < delta1
          ==> z IN ball(vec 0,&2) /\ dist(c z,vector[--(sqrt e); &0]) < rho0 / &2 /\
              ?h. z dot h < &0 /\ frechet_derivative c (at z) h = schy_hf2(c z)) /\
     &0 < lam /\ &64 * lam < e /\ &5 <= H /\ B * lam * H < rho0 / &2 /\
     (!y. Theta y = ode_vf_flow v (:real^3) (lift(lam * y$3)) (sch5v_at e (c(sch5v_pr y)))) /\
     diffeomorphism_on (sch5v_slab H) (IMAGE Theta (sch5v_slab H)) Theta Theta' /\
     (!y. y IN sch5v_slab H ==> (Theta y)$3 = e + lam * y$3) /\
     (!y. y IN sch5v_slab H
          ==> (Theta y IN IMAGE g (sphere(vec 0,&1)) <=> y$1 pow 2 + y$2 pow 2 = &1))
     ==> schy_ctx g r e C c c' v B rho0 delta1 lam H Theta Theta'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `smooth_map_on (ball(vec 0,&2)) (c:real^2->real^2)` ASSUME_TAC THENL
   [UNDISCH_TAC `sch_ball (c:real^2->real^2) c'` THEN SIMP_TAC[sch_ball; diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\z. sch5v_at e ((c:real^2->real^2) z)) (sphere(vec 0,&1)) = C`
  ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `C:real^3->bool`));
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= H` ASSUME_TAC THENL
   [UNDISCH_TAC `&5 <= H` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[schy_ctx; schy_cd] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The cancellation step.                                                    *)

let SCHB1_CANCEL = prove
 (`SCHY_CANCEL_STATEMENT`,
  REWRITE_TAC[SCHY_CANCEL_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`g:real^3->real^3`; `g':real^3->real^3`; `r:real`; `e:real`;
                       `C:real^3->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(components(sch_level (g:real^3->real^3) e))` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SCH_LEVEL_FINITE_STATEMENT] SCH_LEVEL_FINITE) THEN
    EXISTS_TAC `g':real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `e:real`; `C:real^3->bool`]
    (REWRITE_RULE[SCH_LEVEL_NECK_STATEMENT] SCH4L_LEVEL_NECK)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fn:real^2->real^2` (X_CHOOSE_THEN `Fn':real^2->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "FC")))) THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`;
                `Fn:real^2->real^2`; `Fn':real^2->real^2`; `&1`] SCHY_CANCEL_CHART) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE REWRITE_TAC[REAL_LT_01]); ALL_TAC] THEN
  REMOVE_THEN "FC" (K ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `gt:real^3->real^3` (X_CHOOSE_THEN `gt':real^3->real^3`
    (X_CHOOSE_THEN `c:real^2->real^2` (X_CHOOSE_THEN `c':real^2->real^2`
      (X_CHOOSE_THEN `v:real^3->real^3` (X_CHOOSE_THEN `B:real`
        (X_CHOOSE_THEN `rho0:real` (X_CHOOSE_THEN `delta1:real`
          (fun th -> let ths = CONJUNCTS th in
                     MAP_EVERY ASSUME_TAC (butlast ths) THEN
                     LABEL_TAC "LAM" (last ths)))))))))) THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `r:real`; `e:real`; `C:real^3->bool`; `c:real^2->real^2`;
                `c':real^2->real^2`; `v:real^3->real^3`; `B:real`; `rho0:real`; `delta1:real`]
    SCHY_CANCEL_SHEAR_THM) THEN
  DISCH_THEN(X_CHOOSE_THEN `H0:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `H0:real`))) THEN
  REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "SH"))) THEN
  USE_THEN "LAM" (MP_TAC o SPEC `H0:real`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&5 <= H0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TH"))) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `e:real`; `min (min lam0 lam1) (e / &64)`]
    SCHB1_LAM_CHOICE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `lam < lam0 /\ lam < lam1 /\ &64 * lam < e` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `lam < min (min lam0 lam1) (e / &64)` THEN REWRITE_TAC[REAL_LT_MIN] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "TH" (MP_TAC o SPEC `lam:real`) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `Theta:real^3->real^3`
    (X_CHOOSE_THEN `Theta':real^3->real^3` (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))) THEN
  SUBGOAL_THEN `&3 / &2 <= H0` ASSUME_TAC THENL
   [UNDISCH_TAC `&5 <= H0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`g:real^3->real^3`; `g':real^3->real^3`; `e:real`; `C:real^3->bool`;
                `c:real^2->real^2`; `c':real^2->real^2`; `Theta:real^3->real^3`;
                `Theta':real^3->real^3`; `H0:real`; `lam:real`]
    (REWRITE_RULE[SCHY_CUT_STATEMENT] SCHY_CUT_FROM_SURG)) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:real^3->real^3` (X_CHOOSE_THEN `g1':real^3->real^3`
    (X_CHOOSE_THEN `g2:real^3->real^3` (X_CHOOSE_THEN `g2':real^3->real^3`
      (X_CHOOSE_THEN `e0:real` (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))))) THEN
  SUBGOAL_THEN `closed(IMAGE (g1:real^3->real^3) (sphere(vec 0,&1))) /\
                closed(IMAGE (g2:real^3->real^3) (sphere(vec 0,&1)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC SCHY_NECK_COMPACT THENL
     [EXISTS_TAC `g1':real^3->real^3`; EXISTS_TAC `g2':real^3->real^3`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `schy_ctx g r e C (c:real^2->real^2) c' (v:real^3->real^3) B rho0 delta1 lam H0
                         (Theta:real^3->real^3) Theta'` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHB1_CTX THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  USE_THEN "SH" (MP_TAC o SPECL [`lam:real`; `Theta:real^3->real^3`; `Theta':real^3->real^3`;
                                 `IMAGE (g1:real^3->real^3) (sphere(vec 0,&1))`;
                                 `IMAGE (g2:real^3->real^3) (sphere(vec 0,&1))`;
                                 `g1:real^3->real^3`; `g1':real^3->real^3`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3` (X_CHOOSE_THEN `Phi':real^3->real^3`
    (X_CHOOSE_THEN `L:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC SCHB1_FINISH THEN
  MAP_EVERY EXISTS_TAC [`g':real^3->real^3`; `g1:real^3->real^3`; `g1':real^3->real^3`;
                        `g2:real^3->real^3`; `g2':real^3->real^3`; `Theta:real^3->real^3`;
                        `e0:real`; `Phi:real^3->real^3`; `Phi':real^3->real^3`;
                        `L:real^3->bool`; `t0:real^3`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The one-saddle base case of the smooth Schoenflies induction.            *)

let SCH_BASE1 = prove
 (`SCH_BASE1_STATEMENT`,
  MATCH_MP_TAC SCHY_REDUCE_U4U7A THEN
  REWRITE_TAC[SCH_BASE0; SCH4L_LEVEL_NECK; SCH4L_LEVEL_INNERMOST; SCHB1_CANCEL]);;

