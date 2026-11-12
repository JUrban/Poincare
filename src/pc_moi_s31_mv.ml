(* ========================================================================= *)
(* pc_moi_s31_mv: Mayer-Vietoris for compact polyhedra at H_1 (Moise 28.11  *)
(* p.205; the chain cutting in the proof of 31.4, p.221).  Main theorem     *)
(* MV_POLY |- MOI_S31_MV_POLY (pc_moi_s3032_stmt.ml).  Route:               *)
(* derived-neighbourhood retractions relative to a INTER b give an open     *)
(* cover of a UNION b with retractions onto a, b, a INTER b that are        *)
(* compatible up to homotopy; ATOP_MAYER_VIETORIS (pc_top_mv) on that       *)
(* cover, homotopy invariance and functoriality give the exactness.         *)
(* ========================================================================= *)

needs "src/pc_moi_s34_h1.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_s3032_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: the derived-neighbourhood retraction of a polyhedral pair       *)
(* relative to the subpolyhedron (the rel form of MOI_S4J_PAIR_RETRACT),    *)
(* and the gluing of two homotopies on two closed pieces that are           *)
(* stationary on the common part.                                           *)
(* ========================================================================= *)

let MOI_S3MV_PAIR_RETRACT_REL = prove
 (`!(p:real^N->bool) q.
     pl_polyhedron p /\ pl_polyhedron q /\ q SUBSET p
     ==> ?u r. open u /\ q SUBSET u /\
               (!x. x IN p INTER u ==> r x IN q) /\ (!x. x IN q ==> r x = x) /\
               r continuous_on (p INTER u) /\
               homotopic_with (\h. !x. x IN q ==> h x = x)
                 (subtopology euclidean (p INTER u),subtopology euclidean p) (\x. x) r`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4J_PAIR_TRIANGULATION) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` (X_CHOOSE_THEN
    `l:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_DEFORMATION_RETRACT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  ABBREV_TAC `n = derived_nbhd (t:(real^N->bool)->bool) l` THEN
  MP_TAC(ISPECL [`subtopology euclidean (p:real^N->bool)`;
                 `n:real^N->bool`] OPEN_IN_INTERIOR_OF) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `r:real^N->real^N`] THEN
  SUBGOAL_THEN `(p:real^N->bool) INTER u SUBSET n` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (p:real^N->bool)`;
                   `n:real^N->bool`] INTERIOR_OF_SUBSET) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N->bool) SUBSET p INTER u` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^N->bool) SUBSET subtopology euclidean p interior_of n` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `retraction (n,q) (r:real^N->real^N)` THEN
  REWRITE_TAC[retraction] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    UNDISCH_TAC `(q:real^N->bool) SUBSET p INTER u` THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (r:real^N->real^N) n SUBSET q` THEN
    UNDISCH_TAC `(p:real^N->bool) INTER u SUBSET n` THEN SET_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `n:real^N->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_RIGHT THEN
    EXISTS_TAC `n:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_SUBSET_LEFT THEN
    EXISTS_TAC `n:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* Gluing: homotopies f1 ~ g1 on k1 and f2 ~ g2 on k2, both stationary on   *)
(* k1 INTER k2 where f1 = f2, give a homotopy of the pasted maps.           *)

let MOI_S3MV_HOMOTOPIC_CASES = prove
 (`!k1 k2 y (f1:real^N->real^M) g1 f2 g2.
     closed_in (subtopology euclidean (k1 UNION k2)) k1 /\
     closed_in (subtopology euclidean (k1 UNION k2)) k2 /\
     homotopic_with (\h. !x. x IN k1 INTER k2 ==> h x = f1 x)
       (subtopology euclidean k1,subtopology euclidean y) f1 g1 /\
     homotopic_with (\h. !x. x IN k1 INTER k2 ==> h x = f2 x)
       (subtopology euclidean k2,subtopology euclidean y) f2 g2 /\
     (!x. x IN k1 INTER k2 ==> f1 x = f2 x)
     ==> homotopic_with (\h. T)
           (subtopology euclidean (k1 UNION k2),subtopology euclidean y)
           (\x. if x IN k1 then f1 x else f2 x) (\x. if x IN k1 then g1 x else g2 x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMOTOPIC_WITH_EUCLIDEAN] THEN BETA_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "c2")
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `h1:real^(1,N)finite_sum->real^M` (CONJUNCTS_THEN2 (LABEL_TAC "h1c")
        (CONJUNCTS_THEN2 (LABEL_TAC "h1i") (CONJUNCTS_THEN2 (LABEL_TAC "h10")
          (CONJUNCTS_THEN2 (LABEL_TAC "h11") (LABEL_TAC "h1p"))))))
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `h2:real^(1,N)finite_sum->real^M` (CONJUNCTS_THEN2 (LABEL_TAC "h2c")
          (CONJUNCTS_THEN2 (LABEL_TAC "h2i") (CONJUNCTS_THEN2 (LABEL_TAC "h20")
            (CONJUNCTS_THEN2 (LABEL_TAC "h21") (LABEL_TAC "h2p"))))))
        (LABEL_TAC "eq"))))) THEN
  SUBGOAL_THEN
   `interval[vec 0:real^1,vec 1] PCROSS ((k1:real^N->bool) UNION k2) =
    (interval[vec 0,vec 1] PCROSS k1) UNION (interval[vec 0,vec 1] PCROSS k2)`
  (LABEL_TAC "pu") THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\z:real^(1,N)finite_sum.
                if sndcart z IN k1 then (h1:real^(1,N)finite_sum->real^M) z else h2 z` THEN
  REWRITE_TAC[SNDCART_PASTECART] THEN REPEAT CONJ_TAC THENL
   [USE_THEN "pu" SUBST1_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "pu" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC CLOSED_IN_PCROSS THEN
      ASM_REWRITE_TAC[CLOSED_IN_REFL];
      USE_THEN "pu" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC CLOSED_IN_PCROSS THEN
      ASM_REWRITE_TAC[CLOSED_IN_REFL];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`tt:real^1`; `x:real^N`] THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) IN k1 INTER k2` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      USE_THEN "h1p" (MP_TAC o SPEC `x:real^N` o C MATCH_MP
        (ASSUME `(tt:real^1) IN interval[vec 0,vec 1]`)) THEN
      USE_THEN "h2p" (MP_TAC o SPEC `x:real^N` o C MATCH_MP
        (ASSUME `(tt:real^1) IN interval[vec 0,vec 1]`)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                SNDCART_PASTECART; IN_UNION] THEN
    MAP_EVERY X_GEN_TAC [`tt:real^1`; `x:real^N`] THEN DISCH_TAC THEN
    COND_CASES_TAC THENL
     [USE_THEN "h1i" (MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART;
                                             PASTECART_IN_PCROSS]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "h2i" (MP_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE; FORALL_PASTECART;
                                             PASTECART_IN_PCROSS]) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Part 2: the open cover s = a UNION (b INTER u2), t = b UNION             *)
(* (a INTER u1) of a UNION b, with the pasted retractions Rs: s -> a,       *)
(* Rt: t -> b, rho: s INTER t -> a INTER b and the homotopies Rs ~ rho in a *)
(* and Rt ~ rho in b on s INTER t = (a INTER u1) UNION (b INTER u2).        *)
(* ========================================================================= *)

(* One side: Rs is continuous, and on s INTER t it is homotopic in a to rho. *)

let MOI_S3MV_SIDE = prove
 (`!a b c u1 u2 (r1:real^N->real^N) r2.
     closed a /\ closed b /\ a INTER b = c /\ c SUBSET u1 /\ c SUBSET u2 /\
     (!x. x IN a INTER u1 ==> r1 x IN c) /\ (!x. x IN c ==> r1 x = x) /\
     homotopic_with (\h. !x. x IN c ==> h x = x)
       (subtopology euclidean (a INTER u1),subtopology euclidean a) (\x. x) r1 /\
     (!x. x IN b INTER u2 ==> r2 x IN c) /\ (!x. x IN c ==> r2 x = x) /\
     r2 continuous_on (b INTER u2)
     ==> continuous_map (subtopology euclidean (a UNION (b INTER u2)),subtopology euclidean a)
                        (\x. if x IN a then x else r2 x) /\
         homotopic_with (\h. T)
           (subtopology euclidean ((a INTER u1) UNION (b INTER u2)),subtopology euclidean a)
           (\x. if x IN a then x else r2 x) (\x. if x IN a then r1 x else r2 x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ca") (CONJUNCTS_THEN2 (LABEL_TAC "cb")
    (CONJUNCTS_THEN2 (LABEL_TAC "c") (CONJUNCTS_THEN2 (LABEL_TAC "cu1")
    (CONJUNCTS_THEN2 (LABEL_TAC "cu2") (CONJUNCTS_THEN2 (LABEL_TAC "r1in")
    (CONJUNCTS_THEN2 (LABEL_TAC "r1fix") (CONJUNCTS_THEN2 (LABEL_TAC "h1")
    (CONJUNCTS_THEN2 (LABEL_TAC "r2in") (CONJUNCTS_THEN2 (LABEL_TAC "r2fix")
      (LABEL_TAC "r2c"))))))))))) THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET a` (LABEL_TAC "ca'") THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN a /\ x IN b ==> x IN c` (LABEL_TAC "inc") THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN b INTER u2 ==> (r2:real^N->real^N) x IN a` (LABEL_TAC "r2a") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "r2in" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "ca'" (MP_TAC o REWRITE_RULE[SUBSET]) THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `a:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `b:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        USE_THEN "inc" MP_TAC THEN USE_THEN "cu2" MP_TAC THEN SET_TAC[];
        REWRITE_TAC[CONTINUOUS_ON_ID];
        ASM_REWRITE_TAC[];
        X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN
        DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        CONV_TAC SYM_CONV THEN USE_THEN "r2fix" MATCH_MP_TAC THEN
        USE_THEN "inc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN
      X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN USE_THEN "r2a" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a INTER u1:real^N->bool`; `b INTER u2:real^N->bool`; `a:real^N->bool`;
                 `\x:real^N. x`; `r1:real^N->real^N`; `r2:real^N->real^N`;
                 `r2:real^N->real^N`] MOI_S3MV_HOMOTOPIC_CASES) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `a:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "inc" MP_TAC THEN USE_THEN "cu1" MP_TAC THEN SET_TAC[];
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `b:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "inc" MP_TAC THEN USE_THEN "cu2" MP_TAC THEN SET_TAC[];
      MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
      EXISTS_TAC `\h:real^N->real^N. !x. x IN c ==> h x = x` THEN
      CONJ_TAC THENL [USE_THEN "h1" ACCEPT_TAC; ALL_TAC] THEN
      BETA_TAC THEN X_GEN_TAC `h:real^N->real^N` THEN STRIP_TAC THEN
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN USE_THEN "inc" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[HOMOTOPIC_WITH_REFL; CONTINUOUS_MAP_EUCLIDEAN2] THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN USE_THEN "r2fix" MATCH_MP_TAC THEN
      USE_THEN "inc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^N. if x IN a INTER u1 then x else r2 x`;
    `\x:real^N. if x IN a INTER u1 then (r1:real^N->real^N) x else r2 x`] THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNION; IN_INTER] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN a` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:real^N) IN u1` (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `(x:real^N) IN a /\ x IN u1 \/ x IN b /\ x IN u2` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "cu1" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  USE_THEN "inc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* rho is continuous from s INTER t into a INTER b. *)

let MOI_S3MV_RHO_CONT = prove
 (`!a b c u1 u2 (r1:real^N->real^N) r2.
     closed a /\ closed b /\ a INTER b = c /\ c SUBSET u1 /\ c SUBSET u2 /\
     (!x. x IN a INTER u1 ==> r1 x IN c) /\ (!x. x IN c ==> r1 x = x) /\
     r1 continuous_on (a INTER u1) /\
     (!x. x IN b INTER u2 ==> r2 x IN c) /\ (!x. x IN c ==> r2 x = x) /\
     r2 continuous_on (b INTER u2)
     ==> continuous_map (subtopology euclidean ((a INTER u1) UNION (b INTER u2)),
                         subtopology euclidean c)
                        (\x. if x IN a then r1 x else r2 x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ca") (CONJUNCTS_THEN2 (LABEL_TAC "cb")
    (CONJUNCTS_THEN2 (LABEL_TAC "c") (CONJUNCTS_THEN2 (LABEL_TAC "cu1")
    (CONJUNCTS_THEN2 (LABEL_TAC "cu2") (CONJUNCTS_THEN2 (LABEL_TAC "r1in")
    (CONJUNCTS_THEN2 (LABEL_TAC "r1fix") (CONJUNCTS_THEN2 (LABEL_TAC "r1c")
    (CONJUNCTS_THEN2 (LABEL_TAC "r2in") (CONJUNCTS_THEN2 (LABEL_TAC "r2fix")
      (LABEL_TAC "r2c"))))))))))) THEN
  SUBGOAL_THEN `!x:real^N. x IN a /\ x IN b ==> x IN c` (LABEL_TAC "inc") THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `a:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "inc" MP_TAC THEN USE_THEN "cu1" MP_TAC THEN SET_TAC[];
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `b:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "inc" MP_TAC THEN USE_THEN "cu2" MP_TAC THEN SET_TAC[];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) IN c` ASSUME_TAC THENL
       [USE_THEN "inc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "r1fix" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^N) IN c`)]) THEN
      USE_THEN "r2fix" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^N) IN c`)])];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [USE_THEN "r1in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
      SUBGOAL_THEN `(x:real^N) IN c` ASSUME_TAC THENL
       [USE_THEN "inc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "r1fix" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^N) IN c`)]) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "r2in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER]]]);;

(* ========================================================================= *)
(* Part 3: the cover of a UNION b for polyhedra a, b.                      *)
(* ========================================================================= *)

let MOI_S3MV_COVER = prove
 (`!a b:real^N->bool.
     pl_polyhedron a /\ pl_polyhedron b
     ==> ?s t (rs:real^N->real^N) rt rho.
           open_in (subtopology euclidean (a UNION b)) s /\
           open_in (subtopology euclidean (a UNION b)) t /\
           a SUBSET s /\ b SUBSET t /\ s UNION t = a UNION b /\
           continuous_map (subtopology euclidean s,subtopology euclidean a) rs /\
           (!x. x IN a ==> rs x = x) /\
           continuous_map (subtopology euclidean t,subtopology euclidean b) rt /\
           (!x. x IN b ==> rt x = x) /\
           continuous_map (subtopology euclidean (s INTER t),
                           subtopology euclidean (a INTER b)) rho /\
           homotopic_with (\h. T)
             (subtopology euclidean (s INTER t),subtopology euclidean a) rs rho /\
           homotopic_with (\h. T)
             (subtopology euclidean (s INTER t),subtopology euclidean b) rt rho`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_polyhedron (a INTER b:real^N->bool) /\ closed (a:real^N->bool) /\
    closed (b:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[PL_POLYHEDRON_INTER] THEN
    ASM_MESON_TAC[PL_POLYHEDRON_IMP_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `a INTER b:real^N->bool`] MOI_S3MV_PAIR_RETRACT_REL) THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N->bool` (X_CHOOSE_THEN `r1:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `a INTER b:real^N->bool`] MOI_S3MV_PAIR_RETRACT_REL) THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:real^N->bool` (X_CHOOSE_THEN `r2:real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `c = (a:real^N->bool) INTER b` THEN
  SUBGOAL_THEN `(b:real^N->bool) INTER a = c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[INTER_COMM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `b:real^N->bool`; `c:real^N->bool`; `u1:real^N->bool`;
                 `u2:real^N->bool`; `r1:real^N->real^N`; `r2:real^N->real^N`]
    MOI_S3MV_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `a:real^N->bool`; `c:real^N->bool`; `u2:real^N->bool`;
                 `u1:real^N->bool`; `r2:real^N->real^N`; `r1:real^N->real^N`]
    MOI_S3MV_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `b:real^N->bool`; `c:real^N->bool`; `u1:real^N->bool`;
                 `u2:real^N->bool`; `r1:real^N->real^N`; `r2:real^N->real^N`]
    MOI_S3MV_RHO_CONT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (a UNION b)) (a UNION (b INTER u2):real^N->bool) /\
    open_in (subtopology euclidean (a UNION b)) (b UNION (a INTER u1):real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `a UNION (b INTER u2) = (a UNION b) INTER (u2 UNION ((:real^N) DIFF b)) /\
      b UNION (a INTER u1) = (a UNION b) INTER (u1 UNION ((:real^N) DIFF a))`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [UNDISCH_TAC `(c:real^N->bool) SUBSET u1` THEN
      UNDISCH_TAC `(c:real^N->bool) SUBSET u2` THEN EXPAND_TAC "c" THEN SET_TAC[];
      CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
      MATCH_MP_TAC OPEN_UNION THEN ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_with (\h. T)
      (subtopology euclidean ((a INTER u1) UNION (b INTER u2)),subtopology euclidean b)
      (\x:real^N. if x IN b then x else r1 x) (\x. if x IN a then r1 x else r2 x)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(a INTER u1) UNION (b INTER u2) = (b INTER u2) UNION (a INTER u1):real^N->bool`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`\x:real^N. if x IN b then x else r1 x`;
      `\x:real^N. if x IN b then (r2:real^N->real^N) x else r1 x`] THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNION; IN_INTER] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN a` THEN ASM_CASES_TAC `(x:real^N) IN b` THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `(x:real^N) IN c` ASSUME_TAC THENL
       [EXPAND_TAC "c" THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `(x:real^N) IN b /\ x IN u2 \/ x IN a /\ x IN u1` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`a UNION (b INTER u2):real^N->bool`; `b UNION (a INTER u1):real^N->bool`;
    `\x:real^N. if x IN a then x else r2 x`; `\x:real^N. if x IN b then x else r1 x`;
    `\x:real^N. if x IN a then (r1:real^N->real^N) x else r2 x`] THEN
  SUBGOAL_THEN
   `(a UNION (b INTER u2)) INTER (b UNION (a INTER u1)) =
    (a INTER u1) UNION (b INTER u2):real^N->bool`
  SUBST1_TAC THENL
   [UNDISCH_TAC `(c:real^N->bool) SUBSET u1` THEN
    UNDISCH_TAC `(c:real^N->bool) SUBSET u2` THEN EXPAND_TAC "c" THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(SET_TAC[]) THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* Part 4: the homology algebra.  From the cover, Mayer-Vietoris for       *)
(* the open cover (ATOP_MAYER_VIETORIS) gives w in H_1(s INTER t); then     *)
(* z = rho_* w maps to x and y by homotopy invariance and functoriality.    *)
(* ========================================================================= *)

(* One side: if w and x have the same image in H_1(s), then rho_* w maps  *)
(* to x in H_1(a).                                                          *)

let MOI_S3MV_SIDE_ALG = prove
 (`!a c s st (rs:real^N->real^N) rho x w.
     c SUBSET a /\ a SUBSET s /\ st SUBSET s /\
     continuous_map (subtopology euclidean s,subtopology euclidean a) rs /\
     (!z. z IN a ==> rs z = z) /\
     continuous_map (subtopology euclidean st,subtopology euclidean c) rho /\
     homotopic_with (\h. T) (subtopology euclidean st,subtopology euclidean a) rs rho /\
     x IN group_carrier(homology_group(&1,subtopology euclidean a)) /\
     hom_induced (&1) (subtopology euclidean st,{}) (subtopology euclidean s,{}) (\x. x) w =
     hom_induced (&1) (subtopology euclidean a,{}) (subtopology euclidean s,{}) (\x. x) x
     ==> hom_induced (&1) (subtopology euclidean c,{}) (subtopology euclidean a,{}) (\x. x)
           (hom_induced (&1) (subtopology euclidean st,{}) (subtopology euclidean c,{}) rho w) =
         x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean c,subtopology euclidean a) (\x:real^N. x) /\
    continuous_map (subtopology euclidean a,subtopology euclidean s) (\x:real^N. x) /\
    continuous_map (subtopology euclidean st,subtopology euclidean s) (\x:real^N. x)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION]; ALL_TAC] THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (st:real^N->bool)`;
                 `subtopology euclidean (c:real^N->bool)`;
                 `subtopology euclidean (a:real^N->bool)`;
                 `rho:real^N->real^N`; `\x:real^N. x`] HOM_INDUCED_COMPOSE_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o C AP_THM `w:((num->real)->real^N)frag->bool`) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(\x:real^N. x) o (rho:real^N->real^N) = rho` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (st:real^N->bool)`;
                 `subtopology euclidean (a:real^N->bool)`;
                 `rs:real^N->real^N`; `rho:real^N->real^N`] HOMOLOGY_HOMOTOPY_EMPTY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (st:real^N->bool)`;
                 `subtopology euclidean (s:real^N->bool)`;
                 `subtopology euclidean (a:real^N->bool)`;
                 `\x:real^N. x`; `rs:real^N->real^N`] HOM_INDUCED_COMPOSE_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o C AP_THM `w:((num->real)->real^N)frag->bool`) THEN
  REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(rs:real^N->real^N) o (\x:real^N. x) = rs` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF; ETA_AX]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (a:real^N->bool)`;
                 `subtopology euclidean (s:real^N->bool)`;
                 `subtopology euclidean (a:real^N->bool)`;
                 `\x:real^N. x`; `rs:real^N->real^N`] HOM_INDUCED_COMPOSE_EMPTY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o C AP_THM `x:((num->real)->real^N)frag->bool`) THEN
  REWRITE_TAC[o_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `hom_induced (&1) (subtopology euclidean (a:real^N->bool),{})
                               (subtopology euclidean a,{}) (\x. x) x` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN MATCH_MP_TAC HOM_INDUCED_EQ THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC HOM_INDUCED_ID THEN ASM_REWRITE_TAC[GSYM homology_group]]);;

(* The exactness from the cover data. *)

let MOI_S3MV_ALGEBRA = prove
 (`!a b s t (rs:real^N->real^N) rt rho x y.
     open_in (subtopology euclidean (a UNION b)) s /\
     open_in (subtopology euclidean (a UNION b)) t /\
     a SUBSET s /\ b SUBSET t /\ s UNION t = a UNION b /\
     continuous_map (subtopology euclidean s,subtopology euclidean a) rs /\
     (!z. z IN a ==> rs z = z) /\
     continuous_map (subtopology euclidean t,subtopology euclidean b) rt /\
     (!z. z IN b ==> rt z = z) /\
     continuous_map (subtopology euclidean (s INTER t),
                     subtopology euclidean (a INTER b)) rho /\
     homotopic_with (\h. T)
       (subtopology euclidean (s INTER t),subtopology euclidean a) rs rho /\
     homotopic_with (\h. T)
       (subtopology euclidean (s INTER t),subtopology euclidean b) rt rho /\
     x IN group_carrier(homology_group(&1,subtopology euclidean a)) /\
     y IN group_carrier(homology_group(&1,subtopology euclidean b)) /\
     hom_induced (&1) (subtopology euclidean a,{})
                 (subtopology euclidean (a UNION b),{}) (\x. x) x =
     hom_induced (&1) (subtopology euclidean b,{})
                 (subtopology euclidean (a UNION b),{}) (\x. x) y
     ==> ?z. z IN group_carrier(homology_group(&1,subtopology euclidean (a INTER b))) /\
             hom_induced (&1) (subtopology euclidean (a INTER b),{})
                         (subtopology euclidean a,{}) (\x. x) z = x /\
             hom_induced (&1) (subtopology euclidean (a INTER b),{})
                         (subtopology euclidean b,{}) (\x. x) z = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(s:real^N->bool) SUBSET a UNION b /\ (t:real^N->bool) SUBSET a UNION b /\
    s INTER t SUBSET a UNION b /\ s INTER t SUBSET s /\ s INTER t SUBSET t /\
    a INTER b SUBSET a /\ a INTER b SUBSET b /\ a SUBSET a UNION b /\ b SUBSET a UNION b`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) UNION t = a UNION b` THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (a UNION b:real^N->bool)`;
                 `s:real^N->bool`; `t:real^N->bool`]
    (REWRITE_RULE[ATOP_MAYER_VIETORIS_STATEMENT]
      (INST_TYPE [`:real^N`,`:A`] ATOP_MAYER_VIETORIS))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4J_SUBTOP] THEN
  DISCH_THEN(CHOOSE_THEN (MP_TAC o CONJUNCT1)) THEN
  REWRITE_TAC[group_exactness] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hf") (CONJUNCTS_THEN2 (LABEL_TAC "hg")
    (LABEL_TAC "ex"))) THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean a,subtopology euclidean s) (\x:real^N. x) /\
    continuous_map (subtopology euclidean b,subtopology euclidean t) (\x:real^N. x) /\
    continuous_map (subtopology euclidean s,subtopology euclidean (a UNION b)) (\x:real^N. x) /\
    continuous_map (subtopology euclidean t,subtopology euclidean (a UNION b)) (\x:real^N. x)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION]; ALL_TAC] THEN
  ABBREV_TAC `x' = hom_induced (&1) (subtopology euclidean a,{})
                                (subtopology euclidean s,{}) (\x:real^N. x) x` THEN
  ABBREV_TAC `y' = hom_induced (&1) (subtopology euclidean b,{})
                                (subtopology euclidean t,{}) (\x:real^N. x) y` THEN
  SUBGOAL_THEN
   `x' IN group_carrier(homology_group(&1,subtopology euclidean (s:real^N->bool))) /\
    y' IN group_carrier(homology_group(&1,subtopology euclidean (t:real^N->bool)))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x'"; "y'"] THEN CONJ_TAC THEN
    MATCH_MP_TAC ATOP_HOMOMORPHISM_IN THENL
     [EXISTS_TAC `homology_group(&1,subtopology euclidean (a:real^N->bool))`;
      EXISTS_TAC `homology_group(&1,subtopology euclidean (b:real^N->bool))`] THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced (&1) (subtopology euclidean s,{}) (subtopology euclidean (a UNION b),{})
                (\x:real^N. x) x' =
    hom_induced (&1) (subtopology euclidean t,{}) (subtopology euclidean (a UNION b),{})
                (\x:real^N. x) y'`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x'"; "y'"] THEN
    MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (a:real^N->bool)`; `{}:real^N->bool`;
                   `subtopology euclidean (s:real^N->bool)`; `{}:real^N->bool`;
                   `subtopology euclidean (a UNION b:real^N->bool)`; `{}:real^N->bool`]
      ATOP_HOM_INDUCED_INCLUSIONS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C AP_THM `x:((num->real)->real^N)frag->bool`) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (b:real^N->bool)`; `{}:real^N->bool`;
                   `subtopology euclidean (t:real^N->bool)`; `{}:real^N->bool`;
                   `subtopology euclidean (a UNION b:real^N->bool)`; `{}:real^N->bool`]
      ATOP_HOM_INDUCED_INCLUSIONS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o C AP_THM `y:((num->real)->real^N)frag->bool`) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `group_div (homology_group(&1,subtopology euclidean (a UNION b:real^N->bool)))
      (hom_induced (&1) (subtopology euclidean s,{})
                   (subtopology euclidean (a UNION b),{}) (\x:real^N. x) x')
      (hom_induced (&1) (subtopology euclidean t,{})
                   (subtopology euclidean (a UNION b),{}) (\x:real^N. x) y') =
    group_id (homology_group(&1,subtopology euclidean (a UNION b)))`
  (LABEL_TAC "div") THENL
   [MP_TAC(ISPECL [`homology_group(&1,subtopology euclidean (a UNION b:real^N->bool))`;
                   `hom_induced (&1) (subtopology euclidean s,{})
                      (subtopology euclidean (a UNION b),{}) (\x:real^N. x) x'`;
                   `hom_induced (&1) (subtopology euclidean t,{})
                      (subtopology euclidean (a UNION b),{}) (\x:real^N. x) y'`]
      GROUP_DIV_EQ_ID) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC ATOP_HOMOMORPHISM_IN THENL
       [EXISTS_TAC `homology_group(&1,subtopology euclidean (s:real^N->bool))`;
        EXISTS_TAC `homology_group(&1,subtopology euclidean (t:real^N->bool))`] THEN
      ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "ex" (MP_TAC o SPEC `(x':((num->real)->real^N)frag->bool,y':((num->real)->real^N)frag->bool)` o
    GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[group_image; group_kernel; IN_IMAGE; IN_ELIM_THM; PROD_GROUP; IN_CROSS;
              PAIR_EQ] THEN
  USE_THEN "div" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:((num->real)->real^N)frag->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `hom_induced (&1) (subtopology euclidean (s INTER t),{})
                (subtopology euclidean (a INTER b),{}) (rho:real^N->real^N) w` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ATOP_HOMOMORPHISM_IN THEN
    EXISTS_TAC `homology_group(&1,subtopology euclidean (s INTER t:real^N->bool))` THEN
    ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY];
    MATCH_MP_TAC MOI_S3MV_SIDE_ALG THEN
    EXISTS_TAC `s:real^N->bool` THEN EXISTS_TAC `rs:real^N->real^N` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3MV_SIDE_ALG THEN
    EXISTS_TAC `t:real^N->bool` THEN EXISTS_TAC `rt:real^N->real^N` THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Part 5: the theorem MV_POLY.                                             *)
(* ========================================================================= *)

let MV_POLY = prove
 (MOI_S31_MV_POLY,
  MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `b:real^N->bool`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `b:real^N->bool`] MOI_S3MV_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `t:real^N->bool`
    (X_CHOOSE_THEN `rs:real^N->real^N` (X_CHOOSE_THEN `rt:real^N->real^N`
      (X_CHOOSE_THEN `rho:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3MV_ALGEBRA THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `t:real^N->bool`; `rs:real^N->real^N`;
                        `rt:real^N->real^N`; `rho:real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;

