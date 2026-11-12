(* ========================================================================= *)
(* Unit pc_hm_dexist: part 1 of the chain unit for                           *)
(* CM_CHAIN_HM_DIRICHLET_STATEMENT (Colding-Minicozzi 2008, Cor 3.3-3.4).    *)
(* Energy minimizers with W^{1,2} boundary values exist (direct method:      *)
(* WAN_RELLICH0 and WAN_GDIR_LSC), are unique up to null sets for small      *)
(* energy (CM Thm 3.1, the hypothesis CM_CONVEXITY, and the theorem          *)
(* WAN_POINCARE0) and have a smooth harmonic representative                  *)
(* (CM_MINIMIZER_SMOOTH).  Also: almost-everywhere invariance of the W^{1,2} *)
(* vocabulary.                                                               *)
(* ========================================================================= *)

needs "src/pc_hm_convexity.ml";;
needs "src/pc_wan_sob2p.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Almost-everywhere invariance of the W^{1,2} vocabulary.  Changing a       *)
(* map on a null set changes neither its weak partials (the predicate under  *)
(* the selection operator in wan_wd is literally the same), nor W^{1,2},     *)
(* the Dirichlet integrals, W_0, the map class, the energy or the minimizer *)
(* property.                                                                 *)
(* ------------------------------------------------------------------------- *)

let HMD_NULL_SYM = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u'.
     negligible {x | x IN s /\ ~(u x = u' x)}
     ==> negligible {x | x IN s /\ ~(u' x = u x)}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

let HMD_NULL_TRANS = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u' u''.
     negligible {x | x IN s /\ ~(u x = u' x)} /\
     negligible {x | x IN s /\ ~(u' x = u'' x)}
     ==> negligible {x | x IN s /\ ~(u x = u'' x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x | x IN s /\ ~((u:real^N->real^K) x = u' x)} UNION
              {x | x IN s /\ ~((u':real^N->real^K) x = u'' x)}` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

let HMD_LLOC_AE = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u'.
     negligible {x | x IN s /\ ~(u x = u' x)} /\ wan_lloc s u ==> wan_lloc s u'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_lloc] THEN STRIP_TAC THEN
  X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
  MAP_EVERY EXISTS_TAC
   [`u:real^N->real^K`; `{x | x IN s /\ ~((u:real^N->real^K) x = u' x)}`] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN ASM SET_TAC[]);;

let HMD_WPD_AE = prove
 (`!(s:real^N->bool) i (u:real^N->real^K) u' v.
     negligible {x | x IN s /\ ~(u x = u' x)} /\ wan_wpd s i u v ==> wan_wpd s i u' v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_wpd] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HMD_LLOC_AE]; ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `phi:real^N->real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `phi:real^N->real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN s /\ ~((u:real^N->real^K) x = u' x)}` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N->real^K) x = u' x` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let HMD_WD_AE = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u' i.
     negligible {x | x IN s /\ ~(u x = u' x)} ==> wan_wd s i u = wan_wd s i u'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `negligible {x | x IN s /\ ~((u':real^N->real^K) x = u x)}` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_NULL_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[wan_wd] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `v:real^N->real^K` THEN AP_TERM_TAC THEN ASM_MESON_TAC[HMD_WPD_AE]);;

let HMD_W12_AE = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u'.
     negligible {x | x IN s /\ ~(u x = u' x)} /\ wan_w12 s u ==> wan_w12 s u'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_w12] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HMC_LSPACE_SPIKE THEN
    MAP_EVERY EXISTS_TAC
     [`u:real^N->real^K`; `{x | x IN s /\ ~((u:real^N->real^K) x = u' x)}`] THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[HMD_WPD_AE]]);;

let HMD_W12_AE_EQ = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u'.
     negligible {x | x IN s /\ ~(u x = u' x)} ==> (wan_w12 s u <=> wan_w12 s u')`,
  MESON_TAC[HMD_W12_AE; HMD_NULL_SYM]);;

let HMD_DIR_AE = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u'.
     negligible {x | x IN s /\ ~(u x = u' x)} ==> wan_dir s u = wan_dir s u'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_dir] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HMD_WD_AE th]));;

let HMD_GDIR_AE = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) (u:real^N->real^K) u'.
     negligible {x | x IN s /\ ~(u x = u' x)} ==> wan_gdir s G u = wan_gdir s G u'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wan_gdir] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HMD_WD_AE th]) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN s /\ ~((u:real^N->real^K) x = u' x)}` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N->real^K) x = u' x` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

let HMD_LNORM_AE = prove
 (`!(s:real^M->bool) p (f:real^M->real^N) g.
     negligible {x | x IN s /\ ~(f x = g x)} ==> lnorm s p f = lnorm s p g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnorm] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{x | x IN s /\ ~((f:real^M->real^N) x = g x)}` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) x = g x` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

(* The difference of a fixed map with two a.e. equal maps.                   *)

let HMD_NULL_SUB = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u' (f:real^N->real^K).
     negligible {x | x IN s /\ ~(u x = u' x)}
     ==> negligible {x | x IN s /\ ~(f x - u x = f x - u' x)} /\
         negligible {x | x IN s /\ ~(u x - f x = u' x - f x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x | x IN s /\ ~((u:real^N->real^K) x = u' x)}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  MESON_TAC[VECTOR_ARITH `(a:real^N) - b = a - c <=> b = c`;
            VECTOR_ARITH `(b:real^N) - a = c - a <=> b = c`]);;

let HMD_W120_AE = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u'.
     negligible {x | x IN s /\ ~(u x = u' x)} /\ wan_w120 s u ==> wan_w120 s u'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wan_w120] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HMD_W12_AE]; ALL_TAC] THEN
  EXISTS_TAC `f:num->real^N->real^K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!n. lnorm s (&2) (\x. (f:num->real^N->real^K) n x - u' x) =
        lnorm s (&2) (\x. f n x - u x) /\
        wan_dir s (\x. f n x - u' x) = wan_dir s (\x. f n x - u x)`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `u':real^N->real^K`; `u:real^N->real^K`;
                 `(f:num->real^N->real^K) n`] HMD_NULL_SUB) THEN
  ANTS_TAC THENL [MATCH_MP_TAC HMD_NULL_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN CONJ_TAC THENL
   [MATCH_MP_TAC HMD_LNORM_AE; MATCH_MP_TAC HMD_DIR_AE] THEN
  ASM_REWRITE_TAC[]);;

let HMD_WMAP_AE = prove
 (`!(S:real^K->bool) (s:real^2->bool) (u:real^2->real^K) u'.
     negligible {x | x IN s /\ ~(u x = u' x)} /\ cm_wmap S s u ==> cm_wmap S s u'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_wmap] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HMD_W12_AE]; ALL_TAC] THEN
  EXISTS_TAC `(Z:real^2->bool) UNION {x | x IN s /\ ~((u:real^2->real^K) x = u' x)}` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
  ASM_MESON_TAC[IN_DIFF]);;

let HMD_GEN_AE = prove
 (`!(G:real^K->real^K^K) (s:real^2->bool) (u:real^2->real^K) u'.
     negligible {x | x IN s /\ ~(u x = u' x)} ==> cm_gen G s u = cm_gen G s u'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cm_gen] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC HMD_GDIR_AE THEN ASM_REWRITE_TAC[]);;

let HMD_MINIMIZER_AE = prove
 (`!(S:real^K->bool) (G:real^K->real^K^K) (s:real^2->bool) (u:real^2->real^K) u'.
     negligible {x | x IN s /\ ~(u x = u' x)} /\ cm_minimizer S G s u
     ==> cm_minimizer S G s u'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_minimizer] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HMD_WMAP_AE]; ALL_TAC] THEN
  X_GEN_TAC `w:real^2->real^K` THEN STRIP_TAC THEN
  SUBGOAL_THEN `cm_gen G s (u':real^2->real^K) = cm_gen G s u` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC HMD_GEN_AE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HMD_W120_AE THEN EXISTS_TAC `\x. (w:real^2->real^K) x - u' x` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `u':real^2->real^K`; `u:real^2->real^K`;
                 `w:real^2->real^K`] HMD_NULL_SUB) THEN
  ANTS_TAC THENL [MATCH_MP_TAC HMD_NULL_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SIMP_TAC[]);;

(* Congruence (equality on the set itself).                                  *)

let HMD_EQ_IMP_NULL = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u'.
     (!x. x IN s ==> u x = u' x) ==> negligible {x | x IN s /\ ~(u x = u' x)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x | x IN s /\ ~((u:real^N->real^K) x = u' x)} = {}`
  (fun th -> REWRITE_TAC[th; NEGLIGIBLE_EMPTY]) THEN
  ASM SET_TAC[]);;

let HMD_HARMONIC_CONG = prove
 (`!(S:real^K->bool) (G:real^K->real^K^K) (s:real^2->bool) (u:real^2->real^K) u'.
     (!x. x IN s ==> u x = u' x) /\ cm_harmonic S G s u ==> cm_harmonic S G s u'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_harmonic] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `u:real^2->real^K` THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`phi:real^2->real^K`; `s':real^2->bool`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`phi:real^2->real^K`; `s':real^2->bool`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
  REWRITE_TAC[cm_gen] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CMT_WAN_GDIR_EQ THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN s` (fun th -> ASM_SIMP_TAC[th]) THEN
  MP_TAC(ISPEC `s':real^2->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]);;

(* Continuous maps that agree a.e. on an open set agree on it.               *)

let HMD_CONT_AE_EQ = prove
 (`!(s:real^N->bool) (u:real^N->real^K) u'.
     open s /\ u continuous_on s /\ u' continuous_on s /\
     negligible {x | x IN s /\ ~(u x = u' x)}
     ==> !x. x IN s ==> u x = u' x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `open {x | x IN s /\ ~((u:real^N->real^K) x = u' x)}` ASSUME_TAC THENL
   [SUBGOAL_THEN `{x | x IN s /\ ~((u:real^N->real^K) x = u' x)} =
                  {x | x IN s /\ (\x. u x - u' x) x IN (:real^K) DIFF {vec 0}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_SING; VECTOR_SUB_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_SUB; OPEN_DIFF; OPEN_UNIV; CLOSED_SING];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{x | x IN s /\ ~((u:real^N->real^K) x = u' x)}` OPEN_NOT_NEGLIGIBLE) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Energy comparisons.  For a uniformly elliptic continuous ambient          *)
(* metric G the G-energy density of a W^{1,2} map is integrable and          *)
(* lam dir <= gdir <= Lam dir.  L^2 bounds for maps with values in a        *)
(* bounded set.  The ellipticity constants of a cm_target.                   *)
(* ------------------------------------------------------------------------- *)

let HMD_TARGET_ELLIPTIC = prove
 (`!S (G:real^K->real^K^K) d.
     cm_target S G d
     ==> ?lam Lam. &0 < lam /\ lam <= Lam /\
                   ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
                   (!z xi. lam * norm xi pow 2 <= xi dot (G z ** xi) /\
                           xi dot (G z ** xi) <= Lam * norm xi pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [cm_target]) THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `Lam:real`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS THEN ASM_REWRITE_TAC[]);;

let HMD_GDIR_INTEGRABLE = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) (u:real^N->real^K) Lam i.
     open s /\ wan_w12 s u /\ 1 <= i /\ i <= dimindex(:N) /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z xi. abs(xi dot (G z ** xi)) <= Lam * norm xi pow 2)
     ==> (\x. lift(wan_wd s i u x dot (G(u x) ** wan_wd s i u x))) integrable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `wan_wd s i (u:real^N->real^K)`;
                 `\x. (G:real^K->real^K^K)((u:real^N->real^K) x)`; `Lam:real`]
                HMC_QUAD_INTEGRABLE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[WAN_WD_WORKS] THEN
  SUBGOAL_THEN
   `((vectorize:real^K^K->real^(K,K)finite_prod) o
     (\x. (G:real^K->real^K^K)((u:real^N->real^K) x))) =
    ((vectorize o G) o u)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC HMC_MEAS_COMPOSE THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP WAN_W12_IMP_LSPACE o
    check (fun th -> can (find_term ((=) `wan_w12:(real^N->bool)->(real^N->real^K)->bool`))
                         (concl th))) THEN
  SIMP_TAC[lspace; IN_ELIM_THM]);;

let HMD_GDIR_BOUNDS = prove
 (`!(s:real^N->bool) (G:real^K->real^K^K) (u:real^N->real^K) lam Lam.
     open s /\ wan_w12 s u /\ &0 <= lam /\
     ((vectorize:real^K^K->real^(K,K)finite_prod) o G) continuous_on (:real^K) /\
     (!z xi. lam * norm xi pow 2 <= xi dot (G z ** xi) /\
             xi dot (G z ** xi) <= Lam * norm xi pow 2)
     ==> (!i. 1 <= i /\ i <= dimindex(:N)
              ==> (\x. lift(wan_wd s i u x dot (G(u x) ** wan_wd s i u x)))
                  integrable_on s) /\
         lam * wan_dir s u <= wan_gdir s G u /\ wan_gdir s G u <= Lam * wan_dir s u /\
         &0 <= wan_gdir s G u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z xi. abs(xi dot ((G:real^K->real^K^K) z ** xi)) <= Lam * norm xi pow 2`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPECL [`z:real^K`; `xi:real^K`]) THEN
    SUBGOAL_THEN `&0 <= lam * norm(xi:real^K) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\x. lift(wan_wd s i u x dot ((G:real^K->real^K^K)((u:real^N->real^K) x) **
                                          wan_wd s i u x))) integrable_on s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HMD_GDIR_INTEGRABLE THEN
    EXISTS_TAC `Lam:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> (\x. lift(norm(wan_wd s i (u:real^N->real^K) x) pow 2)) integrable_on s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_LSPACE2_SQNORM_INTEGRABLE THEN
    ASM_SIMP_TAC[WAN_WD_WORKS; ETA_AX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lam * wan_dir s (u:real^N->real^K) <= wan_gdir s G u /\
                wan_gdir s G u <= Lam * wan_dir s u`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[wan_dir; wan_gdir; GSYM SUM_LMUL] THEN CONJ_TAC THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THENL
     [SUBGOAL_THEN
       `lam * drop(integral s (\x. lift(norm(wan_wd s i (u:real^N->real^K) x) pow 2))) =
        drop(integral s (\x. lam % lift(norm(wan_wd s i u x) pow 2)))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]; ALL_TAC];
      SUBGOAL_THEN
       `Lam * drop(integral s (\x. lift(norm(wan_wd s i (u:real^N->real^K) x) pow 2))) =
        drop(integral s (\x. Lam % lift(norm(wan_wd s i u x) pow 2)))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL]; ALL_TAC]] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; DROP_CMUL; LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lam * wan_dir s (u:real^N->real^K)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[WAN_DIR_POS]);;

(* L^2 bound for the difference of two maps with values a.e. in a ball.      *)

let HMD_L2_BOUND = prove
 (`!(s:real^N->bool) (v:real^N->real^K) u B Z.
     measurable s /\ (\x. v x - u x) IN lspace s (&2) /\ negligible Z /\
     (!x. x IN s DIFF Z ==> norm(v x) <= B /\ norm(u x) <= B)
     ==> lnorm s (&2) (\x. v x - u x) pow 2 <= (&2 * B) pow 2 * measure s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[WAN_SOB_LNORM2_SQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s (\x:real^N. lift((&2 * B) pow 2)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN EXISTS_TAC `Z:real^N->bool` THEN
    ASM_SIMP_TAC[WAN_LSPACE2_SQNORM_INTEGRABLE; INTEGRABLE_ON_CONST; LIFT_DROP] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(a:real^K) <= B /\ norm(b:real^K) <= B ==> norm(a - b) <= &2 * B`) THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[INTEGRAL_CONST_GEN; DROP_CMUL; LIFT_DROP] THEN
    REWRITE_TAC[REAL_MUL_SYM; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Existence of energy minimizers with W^{1,2} boundary values (Morrey,      *)
(* CM 2008 Cor 3.4): the direct method.  A minimizing sequence in the class *)
(* of maps with the boundary values of u (W_0 sense) and values in S a.e.   *)
(* has bounded W^{1,2} differences from u; WAN_RELLICH0 gives an a.e. and   *)
(* L^2 convergent subsequence, values in S survive (S closed), and          *)
(* WAN_GDIR_LSC on the tails bounds the energy of the limit by the infimum. *)
(* ------------------------------------------------------------------------- *)

let hmd_class = new_definition
 `hmd_class (S:real^K->bool) (s:real^2->bool) (u:real^2->real^K) =
    {v:real^2->real^K | cm_wmap S s v /\ wan_w120 s (\x. v x - u x)}`;;

let HMD_IN_CLASS = prove
 (`!(S:real^K->bool) s (u:real^2->real^K) v.
     v IN hmd_class S s u <=> cm_wmap S s v /\ wan_w120 s (\x. v x - u x)`,
  REWRITE_TAC[hmd_class; IN_ELIM_THM]);;

let HMD_W120_ZERO = prove
 (`!(s:real^N->bool). open s ==> wan_w120 s (\x. vec 0:real^K)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WAN_VTEST_W120 THEN
  ASM_REWRITE_TAC[wan_vtest; SMOOTH_MAP_ON_CONST] THEN
  EXISTS_TAC `{}:real^N->bool` THEN REWRITE_TAC[COMPACT_EMPTY; EMPTY_SUBSET]);;

let HMD_W120_REFL = prove
 (`!(s:real^N->bool) (u:real^N->real^K). open s ==> wan_w120 s (\x. u x - u x)`,
  SIMP_TAC[VECTOR_SUB_REFL; HMD_W120_ZERO]);;

let HMD_CLASS_SELF = prove
 (`!(S:real^K->bool) s (u:real^2->real^K).
     open s /\ cm_wmap S s u ==> u IN hmd_class S s u`,
  SIMP_TAC[HMD_IN_CLASS; HMD_W120_REFL]);;

let HMD_CLASS_SHIFT = prove
 (`!(S:real^K->bool) s (u:real^2->real^K) w.
     open s /\ wan_w120 s (\x. w x - u x) ==> hmd_class S s w = hmd_class S s u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; HMD_IN_CLASS] THEN
  X_GEN_TAC `v:real^2->real^K` THEN
  ASM_CASES_TAC `cm_wmap (S:real^K->bool) s (v:real^2->real^K)` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`s:real^2->bool`; `\x. (v:real^2->real^K) x - w x`;
                   `\x. (w:real^2->real^K) x - u x`] WAN_W120_ADD) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `((v:real^N) - w) + (w - u) = v - u`];
    MP_TAC(ISPECL [`s:real^2->bool`; `\x. (v:real^2->real^K) x - u x`;
                   `\x. (w:real^2->real^K) x - u x`] WAN_W120_SUB) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `((v:real^N) - u) - (w - u) = v - w`]]);;

(* Domain monotonicity of the L^p norm.                                      *)

let HMD_LNORM_SUBSET = prove
 (`!(f:real^M->real^N) s t p.
     f IN lspace s p /\ lebesgue_measurable t /\ t SUBSET s /\ &0 <= p
     ==> lnorm t p f <= lnorm s p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnorm] THEN MATCH_MP_TAC RPOW_LE2 THEN
  SUBGOAL_THEN `(f:real^M->real^N) IN lspace t p` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lspace; IN_ELIM_THM]) THEN
  REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    SIMP_TAC[RPOW_POS_LE; NORM_POS_LE];
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
    SIMP_TAC[RPOW_POS_LE; NORM_POS_LE]]);;

(* Subsequences of convergent real sequences.                                *)

let HMD_REALLIM_SUBSEQ = prove
 (`!(f:num->real) l (r:num->num).
     (!m n. m < n ==> r m < r n) /\ (f ---> l) sequentially
     ==> ((\n. f(r n)) ---> l) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o (f:num->real)`; `r:num->num`; `lift l`] LIM_SUBSEQUENCE) THEN
  ASM_REWRITE_TAC[GSYM TENDSTO_REAL] THEN REWRITE_TAC[TENDSTO_REAL; o_DEF]);;

(* The W^{1,2} bound on the minimizing sequence.                             *)

let HMD_CLASS_BOUND = prove
 (`!(S:real^K->bool) s (u:real^2->real^K) v B.
     open s /\ bounded s /\ (!z. z IN S ==> norm z <= B) /\
     cm_wmap S s u /\ v IN hmd_class S s u
     ==> lnorm s (&2) (\x. v x - u x) pow 2 + wan_dir s (\x. v x - u x)
         <= (&2 * B) pow 2 * measure s + &2 * wan_dir s v + &2 * wan_dir s u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HMD_IN_CLASS; cm_wmap] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a <= a' /\ b <= b' ==> a + b <= a' + b'`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC HMD_L2_BOUND THEN EXISTS_TAC `(Z:real^2->bool) UNION Z'` THEN
    ASM_SIMP_TAC[MEASURABLE_OPEN; NEGLIGIBLE_UNION; WAN_W12_SUB; WAN_W12_IMP_LSPACE] THEN
    REWRITE_TAC[IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN ASM_MESON_TAC[IN_DIFF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `u:real^2->real^K`] WAN_DIR_NEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `v:real^2->real^K`; `\x. --((u:real^2->real^K) x)`]
                WAN_DIR_ADD_LE) THEN
  ASM_REWRITE_TAC[GSYM VECTOR_SUB]);;

(* Minimizing sequences.                                                      *)

let HMD_MINSEQ = prove
 (`!(S:real^K->bool) (G:real^K->real^K^K) d s (u:real^2->real^K).
     cm_target S G d /\ open s /\ cm_wmap S s u
     ==> ?m v. (!w. w IN hmd_class S s u ==> m <= cm_gen G s w) /\
               (!n. v n IN hmd_class S s u /\ cm_gen G s (v n) < m + inv(&n + &1)) /\
               &0 <= m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  SUBGOAL_THEN `!w. w IN hmd_class S s (u:real^2->real^K) ==> &0 <= cm_gen G s w`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^2->real^K` THEN REWRITE_TAC[HMD_IN_CLASS; cm_wmap; cm_gen] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`; `w:real^2->real^K`;
                   `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `m = inf (IMAGE (cm_gen G s) (hmd_class S s (u:real^2->real^K)))` THEN
  SUBGOAL_THEN `~(IMAGE (cm_gen G s) (hmd_class S s (u:real^2->real^K)) = {}) /\
                (?b. !x. x IN IMAGE (cm_gen G s) (hmd_class S s u) ==> b <= x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
     [EXISTS_TAC `u:real^2->real^K` THEN MATCH_MP_TAC HMD_CLASS_SELF THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (cm_gen G s) (hmd_class S s (u:real^2->real^K))` INF) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[FORALL_IN_IMAGE]] THEN
  STRIP_TAC THEN EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= m` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`IMAGE (cm_gen G s) (hmd_class S s (u:real^2->real^K))`;
                 `m + inv(&n + &1)`] INF_APPROACH) THEN
  ASM_REWRITE_TAC[EXISTS_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e ==> m < m + e`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC);;

(* Values in a closed set survive a.e. limits.                               *)

let HMD_AE_LIMIT_IN = prove
 (`!(S:real^K->bool) (s:real^N->bool) (v:num->real^N->real^K) w Z N0.
     closed S /\ (!n. negligible(Z n)) /\ negligible N0 /\
     (!n x. x IN s DIFF Z n ==> v n x IN S) /\
     (!x. x IN s DIFF N0 ==> ((\n. v n x) --> w x) sequentially)
     ==> ?Z'. negligible Z' /\ !x. x IN s DIFF Z' ==> w x IN S`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `N0 UNION UNIONS {(Z:num->real^N->bool) n | n IN (:num)}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION; NEGLIGIBLE_COUNTABLE_UNIONS] THEN
  X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_UNIV; DE_MORGAN_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_IN_CLOSED_SET) THEN
  EXISTS_TAC `\n. (v:num->real^N->real^K) n x` THEN
  ASM_SIMP_TAC[IN_DIFF; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN ASM_MESON_TAC[]);;

let HMD_LE_INV_LIMIT = prove
 (`!x c a. &0 <= a /\ (!N. x <= c + a * inv(&N + &1)) ==> x <= c`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `a = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (x - c) / a` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  SUBGOAL_THEN `a * inv(&N + &1) < x - c` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `a * inv(&N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `(/)`)) (concl th))) THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The existence theorem.  HMD_LSC_TAILS: the G-energy bound passes to       *)
(* L^2 and a.e. limits (WAN_GDIR_LSC with the L^2_loc convergence obtained  *)
(* from L^2 convergence on s).  HMD_EXISTS_MIN: every cm_wmap u on a        *)
(* bounded open set has an energy minimizer with the boundary values of u.  *)
(* ------------------------------------------------------------------------- *)

let HMD_LSC_TAILS = prove
 (`!S (G:real^K->real^K^K) d s (v:num->real^2->real^K) (w:real^2->real^K) M E N0.
     cm_target S G d /\ WAN_GDIR_LSC_STATEMENT (:2) (:K) /\ open s /\
     (!n. wan_w12 s (v n) /\ wan_dir s (v n) <= M) /\ wan_w12 s w /\
     ((\n. lnorm s (&2) (\x. v n x - w x)) ---> &0) sequentially /\
     negligible N0 /\ (!x. x IN s DIFF N0 ==> ((\n. v n x) --> w x) sequentially) /\
     (!n. wan_gdir s G (v n) <= E)
     ==> wan_gdir s G w <= E`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WAN_GDIR_LSC_STATEMENT] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`s:real^2->bool`; `G:real^K->real^K^K`; `v:num->real^2->real^K`;
    `w:real^2->real^K`; `M:real`; `E:real`]) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[WAN_W12_IMP_LSPACE] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `Lam:real` THEN MAP_EVERY X_GEN_TAC [`y:real^K`; `xi:real^K`] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPECL [`y:real^K`; `xi:real^K`] o
      check (fun th -> can (find_term ((=) `lam:real`)) (concl th) && is_forall(concl th))) THEN
    SUBGOAL_THEN `&0 <= lam * norm(xi:real^K) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE];
      ASM_REAL_ARITH_TAC];
    FIRST_ASSUM(MP_TAC o MATCH_MP HMC_TARGET_BASICS) THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`y:real^K`; `xi:real^K`] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lam * norm(xi:real^K) pow 2` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_LT_IMP_LE];
    X_GEN_TAC `k:real^2->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC `\n. lnorm s (&2) (\x. (v:num->real^2->real^K) n x - w x)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a <= b ==> abs a <= b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUBSET THEN
      EXISTS_TAC `s:real^2->bool` THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; WAN_W12_SUB; WAN_W12_IMP_LSPACE; ETA_AX; REAL_POS];
      MATCH_MP_TAC HMD_LNORM_SUBSET THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_COMPACT; WAN_W12_SUB; WAN_W12_IMP_LSPACE; ETA_AX; REAL_POS] THEN
      REAL_ARITH_TAC];
    EXISTS_TAC `N0:real^2->bool` THEN ASM_REWRITE_TAC[]]);;

let HMD_EXISTS_MIN = prove
 (`!S (G:real^K->real^K^K) d s (u:real^2->real^K).
     cm_target S G d /\ WAN_RELLICH0_STATEMENT (:2) (:K) /\
     WAN_GDIR_LSC_STATEMENT (:2) (:K) /\ open s /\ bounded s /\ cm_wmap S s u
     ==> ?w. cm_minimizer S G s w /\ wan_w120 s (\x. w x - u x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HMD_TARGET_ELLIPTIC) THEN
  SUBGOAL_THEN `?B. !z:real^K. z IN S ==> norm z <= B` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cm_target]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[BOUNDED_POS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(S:real^K->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [cm_target]) THEN
    SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `s:real^2->bool`;
                 `u:real^2->real^K`] HMD_MINSEQ) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `v:num->real^2->real^K`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!n. cm_wmap S s ((v:num->real^2->real^K) n) /\ wan_w120 s (\x. v n x - u x) /\
        wan_w12 s (v n) /\ wan_dir s (v n) <= (&2 * (m + &1)) / lam /\
        wan_gdir s G (v n) < &2 * (m + inv(&n + &1))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[HMD_IN_CLASS] o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `wan_w12 s ((v:num->real^2->real^K) n)` ASSUME_TAC THENL
     [ASM_MESON_TAC[cm_wmap]; ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `G:real^K->real^K^K`; `(v:num->real^2->real^K) n`;
                   `lam:real`; `Lam:real`] HMD_GDIR_BOUNDS) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN STRIP_TAC THEN
    UNDISCH_TAC `cm_gen G s ((v:num->real^2->real^K) n) < m + inv(&n + &1)` THEN
    REWRITE_TAC[cm_gen] THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      SUBGOAL_THEN `inv(&n + &1) <= &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `M = (&2 * B) pow 2 * measure(s:real^2->bool) +
                  &2 * ((&2 * (m + &1)) / lam) + &2 * wan_dir s (u:real^2->real^K)` THEN
  SUBGOAL_THEN
   `!n. lnorm s (&2) (\x. (v:num->real^2->real^K) n x - u x) pow 2 +
        wan_dir s (\x. v n x - u x) <= M`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "M" THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * B) pow 2 * measure(s:real^2->bool) +
                &2 * wan_dir s ((v:num->real^2->real^K) n) + &2 * wan_dir s (u:real^2->real^K)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HMD_CLASS_BOUND THEN EXISTS_TAC `S:real^K->bool` THEN
      ASM_REWRITE_TAC[HMD_IN_CLASS];
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_LE_RADD; REAL_LE_LADD;
                   REAL_ARITH `&0 < &2`]];
    ALL_TAC] THEN
  UNDISCH_TAC `WAN_RELLICH0_STATEMENT (:2) (:K)` THEN REWRITE_TAC[WAN_RELLICH0_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^2->bool`; `\n x. (v:num->real^2->real^K) n x - u x`;
                             `M:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` (X_CHOOSE_THEN `f:real^2->real^K`
    (MP_TAC o BETA_RULE))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `N0:real^2->bool` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `wan_w12 s (f:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[wan_w120]; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (u:real^2->real^K)` ASSUME_TAC THENL
   [ASM_MESON_TAC[cm_wmap]; ALL_TAC] THEN
  ABBREV_TAC `w = \x. (u:real^2->real^K) x + f x` THEN
  SUBGOAL_THEN `(\x. (w:real^2->real^K) x - u x) = f` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `wan_w12 s (w:real^2->real^K)` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC WAN_W12_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s DIFF N0
        ==> ((\n. (v:num->real^2->real^K) (r n) x) --> w x) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (fun th ->
      can (find_term ((=) `N0:real^2->bool`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD o CONJ (ISPECL [`sequentially`; `(u:real^2->real^K) x`] LIM_CONST)) THEN
    EXPAND_TAC "w" THEN REWRITE_TAC[VECTOR_ARITH `(u:real^N) + (v - u) = v`];
    ALL_TAC] THEN
  SUBGOAL_THEN `cm_wmap S s (w:real^2->real^K)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[cm_wmap] THEN MATCH_MP_TAC HMD_AE_LIMIT_IN THEN
    SUBGOAL_THEN `?Z:num->real^2->bool. !n. negligible (Z n) /\
                    !x. x IN s DIFF Z n ==> (v:num->real^2->real^K) n x IN S`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th ->
        can (find_term ((=) `cm_wmap:(real^K->bool)->(real^2->bool)->(real^2->real^K)->bool`))
            (concl th) && is_forall(concl th))) THEN
      SIMP_TAC[cm_wmap];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`\n. (v:num->real^2->real^K) ((r:num->num) n)`; `\n. (Z:num->real^2->bool) ((r:num->num) n)`;
                          `N0:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `w:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `wan_gdir s G (w:real^2->real^K) <= &2 * m` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_LE_INV_LIMIT THEN EXISTS_TAC `&2` THEN
    REWRITE_TAC[REAL_POS] THEN X_GEN_TAC `N:num` THEN
    REWRITE_TAC[REAL_ARITH `&2 * m + &2 * x = &2 * (m + x)`] THEN
    MATCH_MP_TAC HMD_LSC_TAILS THEN
    MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `d:real`;
                          `\k. (v:num->real^2->real^K) ((r:num->num)(k + N))`;
                          `(&2 * (m + &1)) / lam`; `N0:real^2->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`\n. lnorm s (&2) (\x. (v:num->real^2->real^K) ((r:num->num) n) x - u x - f x)`; `&0`;
        `\k:num. k + N`] HMD_REALLIM_SUBSEQ) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "w" THEN
      REWRITE_TAC[VECTOR_ARITH `(v:real^N) - (u + f) = v - u - f`];
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\n. (v:num->real^2->real^K) ((r:num->num) n) x`; `\k:num. k + N`;
                     `(w:real^2->real^K) x`] LIM_SUBSEQUENCE) THEN
      ASM_SIMP_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
      X_GEN_TAC `k:num` THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `&2 * (m + inv(&((r:num->num)(k + N)) + &1))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_LE_LADD] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_LE_RADD; REAL_OF_NUM_LE; REAL_ARITH `&0 < &n + &1`] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `k + N:num` THEN
      CONJ_TAC THENL [ARITH_TAC; ASM_MESON_TAC[MONOTONE_BIGGER]]];
    ALL_TAC] THEN
  REWRITE_TAC[cm_minimizer] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w':real^2->real^K` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `m:real` THEN CONJ_TAC THENL
   [REWRITE_TAC[cm_gen] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  SUBGOAL_THEN `hmd_class S s (w:real^2->real^K) = hmd_class S s u` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC HMD_CLASS_SHIFT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[HMD_IN_CLASS]);;

(* ------------------------------------------------------------------------- *)
(* Uniqueness (CM 2008 Cor 3.3) from the convexity hypothesis, the           *)
(* smooth harmonic representative (CM_MINIMIZER_SMOOTH), and the headline of *)
(* the unit, HMD_DEXIST.  hmd_convex S G e c is CM_CONVEXITY's conclusion    *)
(* for one target with explicit threshold e and constant c.                  *)
(* ------------------------------------------------------------------------- *)

let hmd_convex = new_definition
 `hmd_convex (S:real^K->bool) (G:real^K->real^K^K) e c <=>
    &0 < e /\ &0 < c /\
    !(a:real^2) r (u:real^2->real^K) v.
       &0 < r /\ cm_harmonic S G (ball(a,r)) v /\ cm_wmap S (ball(a,r)) v /\
       wan_gdir (ball(a,r)) G v <= e /\
       cm_wmap S (ball(a,r)) u /\ wan_w120 (ball(a,r)) (\x. u x - v x)
       ==> c * wan_dir (ball(a,r)) (\x. u x - v x)
           <= wan_gdir (ball(a,r)) G u - wan_gdir (ball(a,r)) G v`;;

let HMD_CONVEX_FROM = prove
 (`!S (G:real^K->real^K^K) d.
     CM_CONVEXITY_STATEMENT (:K) /\ cm_target S G d ==> ?e c. hmd_convex S G e c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CM_CONVEXITY_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[hmd_convex]);;

let HMD_CONVEX_MONO = prove
 (`!S (G:real^K->real^K^K) e c e'.
     hmd_convex S G e c /\ &0 < e' /\ e' <= e ==> hmd_convex S G e' c`,
  REWRITE_TAC[hmd_convex] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* The two minimality inequalities between minimizers with the same         *)
(* boundary values.                                                          *)

let HMD_MINIMIZERS_EQ_ENERGY = prove
 (`!(S:real^K->bool) (G:real^K->real^K^K) s (w:real^2->real^K) w'.
     open s /\ cm_minimizer S G s w /\ cm_minimizer S G s w' /\
     wan_w120 s (\x. w' x - w x)
     ==> wan_gdir s G w' = wan_gdir s G w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cm_minimizer] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cm_gen G s (w:real^2->real^K) <= cm_gen G s w' /\
                cm_gen G s (w':real^2->real^K) <= cm_gen G s w`
  MP_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^2->bool`; `\x. (w':real^2->real^K) x - w x`] WAN_W120_NEG) THEN
    ASM_REWRITE_TAC[VECTOR_NEG_SUB];
    REWRITE_TAC[cm_gen] THEN REAL_ARITH_TAC]);;

let HMD_UNIQUE = prove
 (`!S (G:real^K->real^K^K) e c (a:real^2) r (w:real^2->real^K) w'.
     hmd_convex S G e c /\ &0 < r /\
     cm_harmonic S G (ball(a,r)) w /\ cm_minimizer S G (ball(a,r)) w /\
     wan_gdir (ball(a,r)) G w <= e /\
     cm_minimizer S G (ball(a,r)) w' /\ wan_w120 (ball(a,r)) (\x. w' x - w x)
     ==> negligible {x | x IN ball(a,r) /\ ~(w' x = w x)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `wan_gdir (ball(a,r)) G (w':real^2->real^K) = wan_gdir (ball(a,r)) G w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_MINIMIZERS_EQ_ENERGY THEN EXISTS_TAC `S:real^K->bool` THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_dir (ball(a,r)) (\x. (w':real^2->real^K) x - w x) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC WAN_DIR_POS THEN ASM_MESON_TAC[wan_w120]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_MESON_TAC[hmd_convex]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ th)]) THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [hmd_convex]) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^2`; `r:real`; `w':real^2->real^K`;
                               `w:real^2->real^K`]) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[cm_minimizer];
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[WAN_POINCARE0_STATEMENT] (ISPECL [`(:2)`; `(:K)`] WAN_POINCARE0)) THEN
  DISCH_THEN(MP_TAC o SPECL [`ball(a:real^2,r)`; `a:real^2`; `r:real`;
                             `\x. (w':real^2->real^K) x - w x`]) THEN
  ASM_REWRITE_TAC[OPEN_BALL; SUBSET_REFL; REAL_MUL_RZERO] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\x. (w':real^2->real^K) x - w x) IN lspace (ball(a,r)) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC WAN_W12_IMP_LSPACE THEN ASM_MESON_TAC[wan_w120]; ALL_TAC] THEN
  SUBGOAL_THEN `lnorm (ball(a,r)) (&2) (\x. (w':real^2->real^K) x - w x) = &0` MP_TAC THENL
   [SUBGOAL_THEN `lnorm (ball(a,r)) (&2) (\x. (w':real^2->real^K) x - w x) pow 2 = &0`
    MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ y <= &0 ==> y = &0`) THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2];
      REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LNORM_EQ_0; REAL_ARITH `~(&2 = &0)`; VECTOR_SUB_EQ]);;

let HMD_DEXIST = prove
 (`!S (G:real^K->real^K^K) d e c (a:real^2) r (u:real^2->real^K).
     cm_target S G d /\ hmd_convex S G e c /\
     WAN_RELLICH0_STATEMENT (:2) (:K) /\ WAN_GDIR_LSC_STATEMENT (:2) (:K) /\
     CM_MINIMIZER_SMOOTH_STATEMENT (:K) /\
     &0 < r /\ cm_wmap S (ball(a,r)) u /\ wan_gdir (ball(a,r)) G u <= e
     ==> ?w. cm_minimizer S G (ball(a,r)) w /\ wan_w120 (ball(a,r)) (\x. w x - u x) /\
             cm_harmonic S G (ball(a,r)) w /\ wan_w12 (ball(a,r)) w /\
             wan_gdir (ball(a,r)) G w <= wan_gdir (ball(a,r)) G u /\
             (!x. ~(x IN ball(a,r)) ==> w x = u x) /\
             (!w'. cm_minimizer S G (ball(a,r)) w' /\
                   wan_w120 (ball(a,r)) (\x. w' x - u x)
                   ==> negligible {x | x IN ball(a,r) /\ ~(w' x = w x)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`; `ball(a:real^2,r)`;
                 `u:real^2->real^K`] HMD_EXISTS_MIN) THEN
  ASM_REWRITE_TAC[OPEN_BALL; BOUNDED_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `w0:real^2->real^K` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `CM_MINIMIZER_SMOOTH_STATEMENT (:K)` THEN
  REWRITE_TAC[CM_MINIMIZER_SMOOTH_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`S:real^K->bool`; `G:real^K->real^K^K`; `d:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^2`; `r:real`; `w0:real^2->real^K`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^2->real^K` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `w = \x. if x IN ball(a,r) then (w1:real^2->real^K) x else u x` THEN
  SUBGOAL_THEN `!x. x IN ball(a,r) ==> (w:real^2->real^K) x = w1 x` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~(x IN ball(a,r)) ==> (w:real^2->real^K) x = u x` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `negligible {x | x IN ball(a,r) /\ ~((w0:real^2->real^K) x = w x)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x | x IN ball(a,r) /\ ~((w0:real^2->real^K) x = w1 x)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cm_minimizer S G (ball(a,r)) (w:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_MINIMIZER_AE THEN EXISTS_TAC `w0:real^2->real^K` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_w120 (ball(a,r)) (\x. (w:real^2->real^K) x - u x)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_W120_AE THEN EXISTS_TAC `\x. (w0:real^2->real^K) x - u x` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ball(a:real^2,r)`; `w0:real^2->real^K`; `w:real^2->real^K`;
                   `u:real^2->real^K`] HMD_NULL_SUB) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `w:real^2->real^K` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cm_harmonic S G (ball(a,r)) (w:real^2->real^K)` ASSUME_TAC THENL
   [MATCH_MP_TAC HMD_HARMONIC_CONG THEN EXISTS_TAC `w1:real^2->real^K` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `wan_gdir (ball(a,r)) G (w:real^2->real^K) <= wan_gdir (ball(a,r)) G u`
  ASSUME_TAC THENL
   [UNDISCH_TAC `cm_minimizer S G (ball(a,r)) (w:real^2->real^K)` THEN
    REWRITE_TAC[cm_minimizer; cm_gen] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^2->real^K` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`ball(a:real^2,r)`; `\x. (w:real^2->real^K) x - u x`] WAN_W120_NEG) THEN
      ASM_REWRITE_TAC[OPEN_BALL; VECTOR_NEG_SUB];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[cm_minimizer; cm_wmap]; ALL_TAC] THEN
  X_GEN_TAC `w':real^2->real^K` THEN STRIP_TAC THEN
  MATCH_MP_TAC HMD_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`S:real^K->bool`; `G:real^K->real^K^K`; `e:real`; `c:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(a:real^2,r)`; `\x. (w':real^2->real^K) x - u x`;
                 `\x. (w:real^2->real^K) x - u x`] WAN_W120_SUB) THEN
  ASM_REWRITE_TAC[OPEN_BALL; VECTOR_ARITH `((w':real^N) - u) - (w - u) = w' - w`]);;

