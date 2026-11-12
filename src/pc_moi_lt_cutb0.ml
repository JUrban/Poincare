(* ========================================================================= *)
(* pc_moi_lt_cutb0: lemmas shared by the two halves of the arc case of the   *)
(* cut step of the loop theorem (Moise GTM 47 p.185-187 Cases 3-4),          *)
(* pc_moi_lt_cutb and pc_moi_lt_seam.  All results are general.              *)
(*   TRANSFER: a crossing2 chart can be shrunk into any open set           *)
(*   (MOI_LC0_CROSSING2_SHRINK) and pulled back along a source map that    *)
(*   matches the two disks over an open set (MOI_LC0_CROSSING2_TRANSFER).  *)
(*   LOOP: two simple loops onto the frontier of a planar convex body are   *)
(*   homotopic loops in it up to orientation (MOI_LC0_CONVEX_LOOPS); a      *)
(*   planar polygon with interior is parametrized by std_triangle with the  *)
(*   boundary loop homotopic to any given simple loop onto its frontier     *)
(*   (MOI_LC0_DISK_LOOP).                                                   *)
(*   RECT: the rectangle [a,b] x [0,1], its frontier, its two U-shaped      *)
(*   boundary arcs, horizontal segments, four-arc loops and pasting of PL   *)
(*   maps along vertical lines.                                             *)
(* ========================================================================= *)

needs "src/pc_moi_lt_cuta2.ml";;
needs "src/pc_moi_s26_fill.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* TRANSFER.  A crossing2 chart at y can be taken inside any open           *)
(* set containing y (the chart is cut by a small ball around the centre and *)
(* rescaled, as in MOI_LA2_CROSSING2_LOCAL of pc_moi_lt_cuta2); and crossing2 *)
(* charts pass to a second disk f' that agrees over an open set U with f    *)
(* composed with a continuous source map p onto the f-preimage of U.        *)
(* ------------------------------------------------------------------------- *)

let MOI_LC0_CROSSING2_SHRINK = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) y w0.
     moi_lt_crossing2_at c f y /\ open w0 /\ y IN w0
     ==> ?u (h:real^N->real^3) h' n1 n2.
           u SUBSET w0 /\
           open_in (subtopology euclidean (UNIONS c)) u /\ y IN u /\
           pl_homeomorphism (u,IMAGE h u) (h,h') /\ h y = vec 0 /\
           ((~(y IN complex_boundary c) /\ u INTER complex_boundary c = {} /\
             IMAGE h u = ball(vec 0,&1)) \/
            (y IN complex_boundary c /\
             IMAGE h u = ball(vec 0,&1) INTER {z:real^3 | &0 <= z$3} /\
             IMAGE h (u INTER complex_boundary c) =
             IMAGE h u INTER {z:real^3 | z$3 = &0})) /\
           {x | x IN std_triangle /\ f x IN u} = n1 UNION n2 /\ DISJOINT n1 n2 /\
           IMAGE (h o f) n1 = IMAGE h u INTER {z:real^3 | z$1 = &0} /\
           IMAGE (h o f) n2 = IMAGE h u INTER {z:real^3 | z$2 = &0} /\
           IMAGE h (moi_lt_double_image f INTER u) =
           IMAGE h u INTER {z:real^3 | z$1 = &0 /\ z$2 = &0} /\
           open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n1 /\
           open_in (subtopology euclidean {x | x IN std_triangle /\ f x IN u}) n2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_lt_crossing2_at] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `n1:real^2->bool`
      (X_CHOOSE_THEN `n2:real^2->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 (LABEL_TAC "case") STRIP_ASSUME_TAC)))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  (* the shape of the chart: the unit ball cut by a cone *)
  SUBGOAL_THEN `?cc:real^3->bool. IMAGE (h:real^N->real^3) u = ball(vec 0,&1) INTER cc /\
                                  (!z t. z IN cc /\ &0 < t ==> t % z IN cc)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "case" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `(:real^3)` THEN ASM_REWRITE_TAC[INTER_UNIV; MOI_LA2_CONES];
      EXISTS_TAC `{z:real^3 | &0 <= z$3}` THEN ASM_REWRITE_TAC[MOI_LA2_CONES]];
    ALL_TAC] THEN
  (* a radius *)
  SUBGOAL_THEN `?r. &0 < r /\ r <= &1 /\
                    !z. z IN IMAGE (h:real^N->real^3) u /\ z IN ball(vec 0,r)
                        ==> (h':real^3->real^N) z IN w0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:real^N->real^3`; `h':real^3->real^N`; `u:real^N->bool`;
                   `IMAGE (h:real^N->real^3) u`; `u INTER w0:real^N->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[OPEN_IN_OPEN_INTER]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(vec 0:real^3) IN oo` ASSUME_TAC THENL
     [SUBGOAL_THEN `(vec 0:real^3) IN IMAGE (h:real^N->real^3) (u INTER w0)` MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `vec 0:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min r0 (&1)` THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN IMAGE (h:real^N->real^3) (u INTER w0)` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      MP_TAC(ISPECL [`vec 0:real^3`; `min r0 (&1)`; `r0:real`] SUBSET_BALL) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `ball(vec 0:real^3,r0) SUBSET oo` THEN
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,min r0 (&1))` THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* the shrunk chart *)
  ABBREV_TAC `u' = {p:real^N | p IN u /\ (h:real^N->real^3) p IN ball(vec 0,r)}` THEN
  SUBGOAL_THEN `(u':real^N->bool) SUBSET u /\ u' SUBSET w0 /\ (y:real^N) IN u' /\
                IMAGE (h:real^N->real^3) u' = IMAGE h u INTER ball(vec 0,r) /\
                (!a. IMAGE h (a INTER u') = IMAGE h (a INTER u) INTER ball(vec 0,r)) /\
                (!a. IMAGE h (u' INTER a) = IMAGE h (u INTER a) INTER ball(vec 0,r)) /\
                open_in (subtopology euclidean u) u'`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u'" THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:real^N` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(p:real^N) = h'((h:real^N->real^3) p)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
      SET_TAC[];
      SET_TAC[];
      SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (u':real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* scaling the cone pieces of the small ball back to the unit ball *)
  SUBGOAL_THEN
   `!pp:real^3->bool. (!z t. z IN pp /\ &0 < t ==> t % z IN pp)
        ==> IMAGE (\z. inv r % (z - vec 0))
                  ((IMAGE (h:real^N->real^3) u INTER pp) INTER ball(vec 0,r)) =
            IMAGE h u INTER pp`
  ASSUME_TAC THENL
   [X_GEN_TAC `pp:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:real`; `cc INTER pp:real^3->bool`] MOI_LA2_CONE_SCALE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(CONJUNCT2(CONJUNCT2(CONJUNCT2(CONJUNCT2 MOI_LA2_CONES)))) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[GSYM INTER_ASSOC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\z. inv r % (z - vec 0)) (IMAGE (h:real^N->real^3) u') = IMAGE h u`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(:real^3)` o check (fun th -> is_forall (concl th) &&
      can (find_term (fun t -> t = `pp:real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[INTER_UNIV; CONJUNCT1 MOI_LA2_CONES] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (h:real^N->real^3) u = ball(vec 0,&1) INTER cc` THEN
  DISCH_THEN(K ALL_TAC) THEN
  ABBREV_TAC `m1 = {x | x IN n1 /\ (f:real^2->real^N) x IN u'}` THEN
  ABBREV_TAC `m2 = {x | x IN n2 /\ (f:real^2->real^N) x IN u'}` THEN
  SUBGOAL_THEN `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u'} = m1 UNION m2`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = n1 UNION n2` THEN
    UNDISCH_TAC `(u':real^N->bool) SUBSET u` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) m1 =
                IMAGE (h o f) n1 INTER ball(vec 0,r) /\
                IMAGE ((h:real^N->real^3) o (f:real^2->real^N)) m2 =
                IMAGE (h o f) n2 INTER ball(vec 0,r)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m1"; "m2"; "u'"] THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = n1 UNION n2` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM; IN_UNION; o_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`u':real^N->bool`; `(\z:real^3. inv r % (z - vec 0)) o (h:real^N->real^3)`;
    `(h':real^3->real^N) o (\w:real^3. vec 0 + r % w)`; `m1:real^2->bool`;
    `m2:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* the chart is a PL homeomorphism *)
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (h:real^N->real^3) u'` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
       [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
        MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `IMAGE (h:real^N->real^3) u`] THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `open_in (subtopology euclidean u) (u':real^N->bool)` THEN
        REWRITE_TAC[OPEN_IN_OPEN] THEN
        DISCH_THEN(X_CHOOSE_THEN `ww:real^N->bool` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
        ASM_MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL]];
      UNDISCH_TAC `IMAGE (\z. inv r % (z - vec 0)) (IMAGE (h:real^N->real^3) u') =
                   IMAGE h u` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MOI_LCH_SCALE_PLH THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN REWRITE_TAC[OPEN_BALL] THEN
      ASM_MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL]];
    (* the centre *)
    ASM_REWRITE_TAC[o_THM; VECTOR_SUB_REFL; VECTOR_MUL_RZERO];
    (* interior or boundary point *)
    USE_THEN "case" (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `{z:real^3 | z$3 = &0}` o check (fun th ->
        is_forall (concl th) && can (find_term (fun t -> t = `pp:real^3->bool`)) (concl th))) THEN
      REWRITE_TAC[MOI_LA2_CONES] THEN ASM_REWRITE_TAC[]];
    (* the two sheets are disjoint *)
    MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN
    UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN SET_TAC[];
    (* the first sheet *)
    SUBGOAL_THEN `IMAGE (h:real^N->real^3) (IMAGE (f:real^2->real^N) m1) = IMAGE (h o f) m1`
    SUBST1_TAC THENL [REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{z:real^3 | z$1 = &0}` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `pp:real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[MOI_LA2_CONES];
    (* the second sheet *)
    SUBGOAL_THEN `IMAGE (h:real^N->real^3) (IMAGE (f:real^2->real^N) m2) = IMAGE (h o f) m2`
    SUBST1_TAC THENL [REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{z:real^3 | z$2 = &0}` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `pp:real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[MOI_LA2_CONES];
    (* the double image *)
    FIRST_X_ASSUM(MP_TAC o SPEC `{z:real^3 | z$1 = &0 /\ z$2 = &0}` o check (fun th ->
      is_forall (concl th) && can (find_term (fun t -> t = `pp:real^3->bool`)) (concl th))) THEN
    REWRITE_TAC[MOI_LA2_CONES] THEN ASM_REWRITE_TAC[];
    (* the sheets are open in the preimage *)
    UNDISCH_TAC `open_in (subtopology euclidean {x | x IN std_triangle /\
                    (f:real^2->real^N) x IN u}) n1` THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o1:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `o1:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN
    UNDISCH_TAC `n1:real^2->bool = (n1 UNION n2) INTER o1` THEN
    UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN SET_TAC[];
    UNDISCH_TAC `open_in (subtopology euclidean {x | x IN std_triangle /\
                    (f:real^2->real^N) x IN u}) n2` THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o2:real^2->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `o2:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN
    UNDISCH_TAC `n2:real^2->bool = (n1 UNION n2) INTER o2` THEN
    UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN SET_TAC[]]);;

(* Pulling a crossing2 chart back along a source map p: over an open set U *)
(* containing y, f' is f o p, p is continuous there and reaches every point *)
(* of the f-preimage of U, and the two double images agree in U.           *)

let MOI_LC0_CROSSING2_TRANSFER = prove
 (`!(c:(real^N->bool)->bool) (f:real^2->real^N) (f':real^2->real^N)
    (p:real^2->real^2) y U.
     moi_lt_crossing2_at c f y /\ open U /\ y IN U /\
     (!x. x IN std_triangle /\ f' x IN U ==> p x IN std_triangle /\ f (p x) = f' x) /\
     p continuous_on {x | x IN std_triangle /\ f' x IN U} /\
     (!z. z IN std_triangle /\ f z IN U
          ==> ?x. x IN std_triangle /\ f' x IN U /\ p x = z) /\
     moi_lt_double_image f' INTER U = moi_lt_double_image f INTER U
     ==> moi_lt_crossing2_at c f' y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "PF") (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (LABEL_TAC "ONTO") ASSUME_TAC)))))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `y:real^N`; `U:real^N->bool`]
    MOI_LC0_CROSSING2_SHRINK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `n1:real^2->bool`
      (X_CHOOSE_THEN `n2:real^2->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (CONJUNCTS_THEN2 ASSUME_TAC
              (CONJUNCTS_THEN2 (LABEL_TAC "case") STRIP_ASSUME_TAC))))))))))) THEN
  REWRITE_TAC[moi_lt_crossing2_at] THEN
  ABBREV_TAC `m1 = {x | x IN std_triangle /\ (f':real^2->real^N) x IN u /\
                        (p:real^2->real^2) x IN n1}` THEN
  ABBREV_TAC `m2 = {x | x IN std_triangle /\ (f':real^2->real^N) x IN u /\
                        (p:real^2->real^2) x IN n2}` THEN
  (* points of the f'-preimage of u go into the f-preimage of u *)
  SUBGOAL_THEN `!x. x IN std_triangle /\ (f':real^2->real^N) x IN u
                    ==> (p:real^2->real^2) x IN std_triangle /\ f (p x) = f' x /\
                        p x IN n1 UNION n2`
  (LABEL_TAC "PU") THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    USE_THEN "PF" (MP_TAC o SPEC `x:real^2`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = n1 UNION n2` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^2->bool. a SUBSET n1 UNION n2
                  ==> IMAGE ((h:real^N->real^3) o (f':real^2->real^N))
                        {x | x IN std_triangle /\ f' x IN u /\ (p:real^2->real^2) x IN a} =
                      IMAGE (h o (f:real^2->real^N)) a`
  (LABEL_TAC "IM") THENL
   [X_GEN_TAC `a:real^2->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; o_THM] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(p:real^2->real^2) x` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "PU" (MP_TAC o SPEC `x:real^2`) THEN ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `x0:real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(x0:real^2) IN std_triangle /\ (f:real^2->real^N) x0 IN u`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x IN u} = n1 UNION n2` THEN
        UNDISCH_TAC `(x0:real^2) IN a` THEN UNDISCH_TAC `(a:real^2->bool) SUBSET n1 UNION n2` THEN
        SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "ONTO" (MP_TAC o SPEC `x0:real^2`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `x:real^2` THEN
      USE_THEN "PF" (MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  (* openness: m_i is the preimage of n_i under p, restricted *)
  SUBGOAL_THEN `(p:real^2->real^2) continuous_on
                {x | x IN std_triangle /\ (f':real^2->real^N) x IN u}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{x | x IN std_triangle /\ (f':real^2->real^N) x IN U}` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(u:real^N->bool) SUBSET U` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:real^2->bool. open_in (subtopology euclidean
                       {x | x IN std_triangle /\ (f:real^2->real^N) x IN u}) n
       ==> open_in (subtopology euclidean
                     {x | x IN std_triangle /\ (f':real^2->real^N) x IN u})
                   {x | x IN std_triangle /\ f' x IN u /\ (p:real^2->real^2) x IN n}`
  (LABEL_TAC "OP") THENL
   [X_GEN_TAC `n:real^2->bool` THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o1:real^2->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "NE"))) THEN
    MP_TAC(ISPECL [`p:real^2->real^2`;
                   `{x | x IN std_triangle /\ (f':real^2->real^N) x IN u}`;
                   `o1:real^2->bool`] CONTINUOUS_OPEN_IN_PREIMAGE) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o2:real^2->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "PE"))) THEN
    EXISTS_TAC `o2:real^2->bool` THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "PE" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
    USE_THEN "NE" SUBST1_TAC THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    USE_THEN "PU" (MP_TAC o SPEC `x:real^2`) THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`u:real^N->bool`; `h:real^N->real^3`; `h':real^3->real^N`; `m1:real^2->bool`;
    `m2:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* the preimage splits *)
    MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN X_GEN_TAC `x:real^2` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN USE_THEN "PU" (MP_TAC o SPEC `x:real^2`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[];
      MESON_TAC[]];
    (* disjoint *)
    MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN
    UNDISCH_TAC `DISJOINT (n1:real^2->bool) n2` THEN SET_TAC[];
    (* first sheet *)
    EXPAND_TAC "m1" THEN USE_THEN "IM" (fun th ->
      REWRITE_TAC[MATCH_MP th (SET_RULE `(n1:real^2->bool) SUBSET n1 UNION n2`)]) THEN
    ASM_REWRITE_TAC[];
    (* second sheet *)
    EXPAND_TAC "m2" THEN USE_THEN "IM" (fun th ->
      REWRITE_TAC[MATCH_MP th (SET_RULE `(n2:real^2->bool) SUBSET n1 UNION n2`)]) THEN
    ASM_REWRITE_TAC[];
    (* the double image *)
    SUBGOAL_THEN `moi_lt_double_image (f':real^2->real^N) INTER u =
                  moi_lt_double_image (f:real^2->real^N) INTER u`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `moi_lt_double_image (f':real^2->real^N) INTER U =
                 moi_lt_double_image (f:real^2->real^N) INTER U` THEN
    UNDISCH_TAC `(u:real^N->bool) SUBSET U` THEN SET_TAC[];
    (* the sheets are open in the preimage *)
    EXPAND_TAC "m1" THEN USE_THEN "OP" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    EXPAND_TAC "m2" THEN USE_THEN "OP" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;


(* ------------------------------------------------------------------------- *)
(* LOOP.  Loops on the frontier of a bounded planar convex set              *)
(* with interior are classified by the winding number around an interior   *)
(* point (the frontier is a retract of the punctured plane); simple loops   *)
(* onto the frontier have winding number 1 or -1.  The reflection of        *)
(* std_triangle in the diagonal reverses its boundary loop.  A planar       *)
(* polygon with interior is the image of std_triangle under a PL            *)
(* homeomorphism whose boundary loop is homotopic, on the frontier, to any  *)
(* given simple loop onto the frontier.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_LC0_CONVEX_LOOPS_WN = prove
 (`!(d:real^2->bool) z (p:real^1->real^2) q.
     convex d /\ bounded d /\ z IN interior d /\
     path p /\ pathfinish p = pathstart p /\ path_image p SUBSET frontier d /\
     path q /\ pathfinish q = pathstart q /\ path_image q SUBSET frontier d
     ==> (homotopic_loops (frontier d) p q <=>
          winding_number(p,z) = winding_number(q,z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((z:real^2) IN frontier d)` ASSUME_TAC THENL
   [REWRITE_TAC[frontier; IN_DIFF] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((z:real^2) IN path_image p) /\ ~(z IN path_image q)` STRIP_ASSUME_TAC
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier d SUBSET (:real^2) DELETE z` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN
    EXISTS_TAC `frontier d:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^1->real^2`; `q:real^1->real^2`; `z:real^2`]
    WINDING_NUMBER_HOMOTOPIC_LOOPS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`d:real^2->bool`; `z:real^2`] FRONTIER_RETRACT_OF_PUNCTURED_UNIVERSE) THEN
  ASM_REWRITE_TAC[retract_of; retraction] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^2->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p:real^1->real^2`; `q:real^1->real^2`; `r:real^2->real^2`;
                 `(:real^2) DELETE z`; `frontier d:real^2->bool`]
    HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!g:real^1->real^2. path g /\ pathfinish g = pathstart g /\ path_image g SUBSET frontier d
       ==> homotopic_loops (frontier d) g ((r:real^2->real^2) o g)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[o_THM] THEN
    X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `path_image (g:real^1->real^2) SUBSET frontier d` THEN
    REWRITE_TAC[path_image] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(r:real^2->real^2) o (p:real^1->real^2)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
  EXISTS_TAC `(r:real^2->real^2) o (q:real^1->real^2)` THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[HOMOTOPIC_LOOPS_SYM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Simple loops onto the frontier wind once, in one of the two directions. *)

let MOI_LC0_SIMPLE_LOOP_WN = prove
 (`!(d:real^2->bool) z (p:real^1->real^2).
     convex d /\ bounded d /\ z IN interior d /\
     simple_path p /\ pathfinish p = pathstart p /\ path_image p = frontier d
     ==> winding_number(p,z) = Cx(&1) \/ winding_number(p,z) = --Cx(&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^2) IN inside(path_image p)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INSIDE_FRONTIER_EQ_INTERIOR]; ALL_TAC] THEN
  MP_TAC(ISPEC `p:real^1->real^2` SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_LC0_CONVEX_LOOPS = prove
 (`!(d:real^2->bool) (p:real^1->real^2) q.
     convex d /\ bounded d /\ ~(interior d = {}) /\
     simple_path p /\ pathfinish p = pathstart p /\ path_image p = frontier d /\
     simple_path q /\ pathfinish q = pathstart q /\ path_image q = frontier d
     ==> homotopic_loops (frontier d) p q \/
         homotopic_loops (frontier d) p (reversepath q)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^2`) THEN
  SUBGOAL_THEN `path (p:real^1->real^2) /\ path (q:real^1->real^2)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `~((z:real^2) IN path_image q)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[frontier; IN_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d:real^2->bool`; `z:real^2`; `p:real^1->real^2`]
    MOI_LC0_SIMPLE_LOOP_WN) THEN
  MP_TAC(ISPECL [`d:real^2->bool`; `z:real^2`; `q:real^1->real^2`]
    MOI_LC0_SIMPLE_LOOP_WN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [DISJ1_TAC; DISJ2_TAC; DISJ2_TAC; DISJ1_TAC] THEN
  (W(MP_TAC o PART_MATCH (lhand o rand) MOI_LC0_CONVEX_LOOPS_WN o snd) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[SUBSET_REFL; PATH_REVERSEPATH; PATHSTART_REVERSEPATH;
                     PATHFINISH_REVERSEPATH; PATH_IMAGE_REVERSEPATH];
     DISCH_THEN SUBST1_TAC] THEN
   ASM_SIMP_TAC[WINDING_NUMBER_REVERSEPATH] THEN CONV_TAC COMPLEX_RING));;

(* The reflection of std_triangle in its diagonal. *)

let MOI_LC0_STD_REFLECT = prove
 (`pl_homeomorphism (std_triangle,std_triangle)
     ((\x:real^2. vector[x$2; x$1]),(\x:real^2. vector[x$2; x$1])) /\
   IMAGE (\x:real^2. vector[x$2; x$1]) (relative_frontier std_triangle) =
   relative_frontier std_triangle /\
   homotopic_loops (relative_frontier std_triangle)
     ((\x:real^2. vector[x$2; x$1]) o std_triangle_loop)
     (reversepath std_triangle_loop)`,
  ABBREV_TAC `rt = \x:real^2. vector[x$2; x$1]:real^2` THEN
  SUBGOAL_THEN `linear (rt:real^2->real^2)` ASSUME_TAC THENL
   [EXPAND_TAC "rt" THEN REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
      VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. (rt:real^2->real^2) (rt x) = x` ASSUME_TAC THENL
   [EXPAND_TAC "rt" THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]; ALL_TAC] THEN
  SUBGOAL_THEN `(rt:real^2->real^2) (vec 0) = vec 0 /\ rt (basis 1) = basis 2 /\
                rt (basis 2) = basis 1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rt" THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT; BASIS_COMPONENT;
             ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (rt:real^2->real^2) std_triangle = std_triangle` ASSUME_TAC THENL
   [REWRITE_TAC[std_triangle] THEN ASM_SIMP_TAC[GSYM CONVEX_HULL_LINEAR_IMAGE] THEN
    REWRITE_TAC[IMAGE_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (std_triangle,std_triangle)
                  ((rt:real^2->real^2),(rt:real^2->real^2))` ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (rt:real^2->real^2) (relative_frontier std_triangle) =
                relative_frontier std_triangle` ASSUME_TAC THENL
   [SUBGOAL_THEN `!s:real^2->bool. IMAGE (rt:real^2->real^2) (relative_frontier s) =
                                   relative_frontier (IMAGE rt s)`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`std_triangle`; `rt:real^2->real^2`; `vec 0:real^2`] PL_MAP_ON_AFFINE) THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; std_triangle; POLYTOPE_CONVEX_HULL;
                 FINITE_INSERT; FINITE_EMPTY; VECTOR_ADD_RID; ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[std_triangle_loop] THEN
  SUBGOAL_THEN `(vec 0:real^2) IN relative_frontier std_triangle /\
                (basis 1:real^2) IN relative_frontier std_triangle /\
                (basis 2:real^2) IN relative_frontier std_triangle /\
                segment[vec 0:real^2,basis 2] SUBSET relative_frontier std_triangle /\
                segment[basis 2:real^2,basis 1] SUBSET relative_frontier std_triangle /\
                segment[basis 1:real^2,vec 0] SUBSET relative_frontier std_triangle`
  STRIP_ASSUME_TAC THENL
   [MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN
    REWRITE_TAC[std_triangle_loop] THEN
    SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
             PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
    REWRITE_TAC[SEGMENT_SYM] THEN
    REWRITE_TAC[SUBSET; IN_UNION] THEN
    MESON_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM JOINPATHS_LINEAR_IMAGE; GSYM LINEPATH_LINEAR_IMAGE] THEN
  SIMP_TAC[REVERSEPATH_JOINPATHS; PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
           PATHFINISH_LINEPATH; REVERSEPATH_LINEPATH] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_IMP_HOMOTOPIC_LOOPS THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  MATCH_MP_TAC HOMOTOPIC_PATHS_ASSOC THEN
  ASM_REWRITE_TAC[PATH_LINEPATH; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH]);;

(* A planar polygon with interior: a PL homeomorphism from std_triangle,  *)
(* boundary onto frontier.  (The argument of MOI_FSB_CELL_SIMPLEX of        *)
(* pc_moi_fnd_surfb, which is outside this load closure.)                   *)

let MOI_LC0_CELL_TRIANGLE = prove
 (`!d:real^2->bool.
     polytope d /\ ~(interior d = {})
     ==> ?p q. pl_homeomorphism (std_triangle,d) (p,q) /\
               IMAGE p (relative_frontier std_triangle) = frontier d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `d:real^2->bool` MOI_SFR_POLYGON_CELL) THEN
  ASM_SIMP_TAC[AFF_DIM_NONEMPTY_INTERIOR; DIMINDEX_2] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`std_triangle`; `kk:real^2->bool`; `&2:int`] MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2->real^2` (X_CHOOSE_THEN `q:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(f:real^2->real^2) o (p:real^2->real^2)`;
                        `(q:real^2->real^2) o (g:real^2->real^2)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `kk:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN
  UNDISCH_TAC `pl_homeomorphism (relative_frontier std_triangle,relative_frontier kk)
                 (p:real^2->real^2,q)` THEN
  SIMP_TAC[pl_homeomorphism; homeomorphism] THEN ASM_REWRITE_TAC[]);;

(* Two distinct unit signs are opposite. *)

let MOI_LC0_UNIT_SIGNS = prove
 (`!a b:complex. (a = Cx(&1) \/ a = --Cx(&1)) /\ (b = Cx(&1) \/ b = --Cx(&1)) /\ ~(a = b)
                 ==> --a = b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(CONJUNCT2(CONJUNCT2 th)) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2 th)) THEN MP_TAC(CONJUNCT1 th)) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  CONV_TAC COMPLEX_RING);;

let MOI_LC0_DISK_LOOP = prove
 (`!(d:real^2->bool) (L:real^1->real^2).
     polytope d /\ ~(interior d = {}) /\
     simple_path L /\ pathfinish L = pathstart L /\ path_image L = frontier d
     ==> ?p q. pl_homeomorphism (std_triangle,d) (p,q) /\
               IMAGE p (relative_frontier std_triangle) = frontier d /\
               homotopic_loops (frontier d) (p o std_triangle_loop) L`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex (d:real^2->bool) /\ bounded d` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_BOUNDED]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^2`) THEN
  MP_TAC(ISPEC `d:real^2->bool` MOI_LC0_CELL_TRIANGLE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^2->real^2` (X_CHOOSE_THEN `q0:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `relative_frontier std_triangle SUBSET std_triangle` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    MESON_TAC[SIMPLEX_IMP_CLOSED; MOI_LTD_STD_TRIANGLE_SIMPLEX];
    ALL_TAC] THEN
  (* the boundary loop of p0 and its basic facts *)
  SUBGOAL_THEN
   `!p q:real^2->real^2. pl_homeomorphism (std_triangle,d) (p,q) /\
          IMAGE p (relative_frontier std_triangle) = frontier d
          ==> simple_path (p o std_triangle_loop) /\
              path (p o std_triangle_loop) /\
              pathfinish (p o std_triangle_loop) = pathstart (p o std_triangle_loop) /\
              path_image (p o std_triangle_loop) = frontier d /\
              p continuous_on relative_frontier std_triangle`
  (LABEL_TAC "B") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^2->real^2) continuous_on relative_frontier std_triangle`
    ASSUME_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) /\ c /\ d /\ e ==> a /\ b /\ c /\ d /\ e`) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[MOI_S6F_LOOP_SIMPLE; MOI_LTD_STD_TRIANGLE_LOOP] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MESON_TAC[SIMPLE_PATH_IMP_PATH];
      REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; MOI_LTD_STD_TRIANGLE_LOOP];
      REWRITE_TAC[PATH_IMAGE_COMPOSE; MOI_LTD_STD_TRIANGLE_LOOP] THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  USE_THEN "B" (fun th -> MP_TAC(MATCH_MP th (CONJ
    (ASSUME `pl_homeomorphism (std_triangle,d) (p0:real^2->real^2,q0)`)
    (ASSUME `IMAGE (p0:real^2->real^2) (relative_frontier std_triangle) = frontier d`)))) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `path (L:real^1->real^2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d:real^2->bool`; `z:real^2`; `(p0:real^2->real^2) o std_triangle_loop`]
    MOI_LC0_SIMPLE_LOOP_WN) THEN
  MP_TAC(ISPECL [`d:real^2->bool`; `z:real^2`; `L:real^1->real^2`]
    MOI_LC0_SIMPLE_LOOP_WN) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((z:real^2) IN frontier d)` ASSUME_TAC THENL
   [REWRITE_TAC[frontier; IN_DIFF] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `winding_number((p0:real^2->real^2) o std_triangle_loop,z) =
                 winding_number(L,z)` THENL
   [DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(K ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [`p0:real^2->real^2`; `q0:real^2->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOI_LC0_CONVEX_LOOPS_WN o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  (* the reflected parametrization *)
  ABBREV_TAC `rt = \x:real^2. vector[x$2; x$1]:real^2` THEN
  MP_TAC MOI_LC0_STD_REFLECT THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (std_triangle,d)
                  ((p0:real^2->real^2) o (rt:real^2->real^2),(rt:real^2->real^2) o q0) /\
                IMAGE (p0 o rt) (relative_frontier std_triangle) = frontier d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `std_triangle` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IMAGE_o]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(p0:real^2->real^2) o (rt:real^2->real^2)`;
                        `(rt:real^2->real^2) o (q0:real^2->real^2)`] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "B" (fun th -> MP_TAC(MATCH_MP th (CONJ
    (ASSUME `pl_homeomorphism (std_triangle,d)
               ((p0:real^2->real^2) o (rt:real^2->real^2),(rt:real^2->real^2) o q0)`)
    (ASSUME `IMAGE ((p0:real^2->real^2) o (rt:real^2->real^2))
               (relative_frontier std_triangle) = frontier d`)))) THEN
  STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOI_LC0_CONVEX_LOOPS_WN o snd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; DISCH_THEN SUBST1_TAC] THEN
  (* p0 o rt o loop is homotopic to the reverse of p0 o loop *)
  SUBGOAL_THEN
   `homotopic_loops (frontier d) (((p0:real^2->real^2) o (rt:real^2->real^2)) o std_triangle_loop)
                    (reversepath (p0 o std_triangle_loop))`
  MP_TAC THENL
   [REWRITE_TAC[GSYM o_ASSOC; GSYM PATH_COMPOSE_REVERSEPATH] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `relative_frontier std_triangle` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MOI_LC0_CONVEX_LOOPS_WN o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL; PATH_REVERSEPATH; PATHSTART_REVERSEPATH;
                    PATHFINISH_REVERSEPATH; PATH_IMAGE_REVERSEPATH];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[WINDING_NUMBER_REVERSEPATH] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC MOI_LC0_UNIT_SIGNS THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* RECT.  The rectangle [a,b] x [0,1]: polytope with interior,              *)
(* its frontier; horizontal and vertical segments; the U-shaped boundary   *)
(* arcs moi_lc0_larc a s, from (s,1) through the left side to (s,0), and    *)
(* moi_lc0_rarc t b, from (t,0) through the right side to (t,1); simple     *)
(* loops from four arcs; pasting PL maps along a vertical line.             *)
(* ------------------------------------------------------------------------- *)

let moi_lc0_larc = new_definition
 `moi_lc0_larc a s = linepath(vector[s; &1]:real^2,vector[a; &1]) ++
                     linepath(vector[a; &1],vector[a; &0]) ++
                     linepath(vector[a; &0],vector[s; &0])`;;

let moi_lc0_rarc = new_definition
 `moi_lc0_rarc t b = linepath(vector[t; &0]:real^2,vector[b; &0]) ++
                     linepath(vector[b; &0],vector[b; &1]) ++
                     linepath(vector[b; &1],vector[t; &1])`;;

let MOI_LC0_VEC0 = prove
 (`vec 0:real^2 = vector[&0; &0]`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VEC_COMPONENT]);;

let MOI_LC0_RECT_FACTS = prove
 (`!a b. a < b
         ==> polytope (interval[vector[a; &0],vector[b; &1]]:real^2->bool) /\
             convex (interval[vector[a; &0],vector[b; &1]]:real^2->bool) /\
             compact (interval[vector[a; &0],vector[b; &1]]:real^2->bool) /\
             bounded (interval[vector[a; &0],vector[b; &1]]:real^2->bool) /\
             ~(interior (interval[vector[a; &0],vector[b; &1]]:real^2->bool) = {}) /\
             relative_frontier (interval[vector[a; &0],vector[b; &1]]:real^2->bool) =
             frontier (interval[vector[a; &0],vector[b; &1]]) /\
             frontier (interval[vector[a; &0],vector[b; &1]]:real^2->bool) =
             {x | a <= x$1 /\ x$1 <= b /\ &0 <= x$2 /\ x$2 <= &1 /\
                  (x$1 = a \/ x$1 = b \/ x$2 = &0 \/ x$2 = &1)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interior (interval[vector[a; &0],vector[b; &1]]:real^2->bool) = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2;
                VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLYTOPE_INTERVAL; CONVEX_INTERVAL; COMPACT_INTERVAL; BOUNDED_INTERVAL;
               RELATIVE_FRONTIER_NONEMPTY_INTERIOR] THEN
  REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; EXTENSION; IN_DIFF; IN_INTERVAL; IN_ELIM_THM;
              DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  GEN_TAC THEN ASM_REAL_ARITH_TAC);;

(* Horizontal and vertical segments as coordinate sets. *)

let MOI_LC0_HSEG = prove
 (`!s t c. s <= t
           ==> segment[vector[s; c],vector[t; c]:real^2] =
               {x | x$2 = c /\ s <= x$1 /\ x$1 <= t} /\
               segment[vector[t; c],vector[s; c]:real^2] =
               {x | x$2 = c /\ s <= x$1 /\ x$1 <= t}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SEGMENT_HORIZONTAL o lhand o snd) THEN
  REWRITE_TAC[VECTOR_2] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_LC0_VSEG = prove
 (`!s t c. s <= t
           ==> segment[vector[c; s],vector[c; t]:real^2] =
               {x | x$1 = c /\ s <= x$2 /\ x$2 <= t} /\
               segment[vector[c; t],vector[c; s]:real^2] =
               {x | x$1 = c /\ s <= x$2 /\ x$2 <= t}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^2` THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SEGMENT_VERTICAL o lhand o snd) THEN
  REWRITE_TAC[VECTOR_2] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_LC0_VECTOR2_EQ = prove
 (`!x:real^2 u v. x = vector[u; v] <=> x$1 = u /\ x$2 = v`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

let MOI_LC0_VECTOR2_INJ = prove
 (`!u v u' v'. vector[u; v]:real^2 = vector[u'; v'] <=> u = u' /\ v = v'`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2]);;

(* The left and right U-shaped arcs. *)

let MOI_LC0_LARC = prove
 (`!a s. a < s
         ==> arc (moi_lc0_larc a s) /\
             pl_map_on (interval[vec 0,vec 1]) (moi_lc0_larc a s) /\
             pathstart (moi_lc0_larc a s) = vector[s; &1] /\
             pathfinish (moi_lc0_larc a s) = vector[s; &0] /\
             path_image (moi_lc0_larc a s) =
             {x:real^2 | (x$1 = a /\ &0 <= x$2 /\ x$2 <= &1) \/
                         ((x$2 = &0 \/ x$2 = &1) /\ a <= x$1 /\ x$1 <= s)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `a <= s /\ &0 <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_lc0_larc] THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
           PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  ASM_SIMP_TAC[MOI_LC0_HSEG; MOI_LC0_VSEG] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM_SIMP_TAC[MOI_LC0_HSEG; MOI_LC0_VSEG; ARC_LINEPATH_EQ; MOI_LC0_VECTOR2_INJ] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC ARC_JOIN THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
      ASM_SIMP_TAC[MOI_LC0_HSEG; MOI_LC0_VSEG; ARC_LINEPATH_EQ; MOI_LC0_VECTOR2_INJ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_SING; MOI_LC0_VECTOR2_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_ELIM_THM; IN_SING; MOI_LC0_VECTOR2_EQ] THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_LINEPATH; PATHSTART_LINEPATH] THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL] THEN
    MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL];
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC]);;

let MOI_LC0_RARC = prove
 (`!t b. t < b
         ==> arc (moi_lc0_rarc t b) /\
             pl_map_on (interval[vec 0,vec 1]) (moi_lc0_rarc t b) /\
             pathstart (moi_lc0_rarc t b) = vector[t; &0] /\
             pathfinish (moi_lc0_rarc t b) = vector[t; &1] /\
             path_image (moi_lc0_rarc t b) =
             {x:real^2 | (x$1 = b /\ &0 <= x$2 /\ x$2 <= &1) \/
                         ((x$2 = &0 \/ x$2 = &1) /\ t <= x$1 /\ x$1 <= b)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `t <= b /\ &0 <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_lc0_rarc] THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
           PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  ASM_SIMP_TAC[MOI_LC0_HSEG; MOI_LC0_VSEG] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM_SIMP_TAC[MOI_LC0_HSEG; MOI_LC0_VSEG; ARC_LINEPATH_EQ; MOI_LC0_VECTOR2_INJ] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC ARC_JOIN THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
      ASM_SIMP_TAC[MOI_LC0_HSEG; MOI_LC0_VSEG; ARC_LINEPATH_EQ; MOI_LC0_VECTOR2_INJ] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_SING; MOI_LC0_VECTOR2_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNION; IN_ELIM_THM; IN_SING; MOI_LC0_VECTOR2_EQ] THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_LINEPATH; PATHSTART_LINEPATH] THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL] THEN
    MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL];
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN ASM_REAL_ARITH_TAC]);;

(* A loop from four arcs meeting cyclically in their ends. *)

let MOI_LC0_FOUR_ARCS = prove
 (`!(p1:real^1->real^N) p2 p3 p4.
     arc p1 /\ arc p2 /\ arc p3 /\ arc p4 /\
     pathfinish p1 = pathstart p2 /\ pathfinish p2 = pathstart p3 /\
     pathfinish p3 = pathstart p4 /\ pathfinish p4 = pathstart p1 /\
     path_image p1 INTER path_image p2 = {pathstart p2} /\
     path_image p2 INTER path_image p3 = {pathstart p3} /\
     path_image p3 INTER path_image p4 = {pathstart p4} /\
     path_image p4 INTER path_image p1 = {pathstart p1} /\
     path_image p1 INTER path_image p3 = {} /\ path_image p2 INTER path_image p4 = {}
     ==> simple_path (p1 ++ p2 ++ p3 ++ p4) /\
         pathfinish (p1 ++ p2 ++ p3 ++ p4) = pathstart (p1 ++ p2 ++ p3 ++ p4) /\
         path_image (p1 ++ p2 ++ p3 ++ p4) =
         path_image p1 UNION path_image p2 UNION path_image p3 UNION path_image p4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN] THEN
  MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
  ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN
    ASM_SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATH_IMAGE_JOIN] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ARC_JOIN THEN ASM_REWRITE_TAC[SUBSET_REFL];
      ASM SET_TAC[]];
    ASM SET_TAC[]]);;

(* Pasting PL maps on two rectangles side by side. *)

let MOI_LC0_RECT_UNION = prove
 (`!a c b. a <= c /\ c <= b
           ==> interval[vector[a; &0],vector[c; &1]] UNION
               interval[vector[c; &0],vector[b; &1]] =
               interval[vector[a; &0],vector[b; &1]]:real^2->bool`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  GEN_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_LC0_RECT_PASTE = prove
 (`!(f:real^2->real^N) a c b.
     a <= c /\ c <= b /\
     pl_map_on (interval[vector[a; &0],vector[c; &1]]) f /\
     pl_map_on (interval[vector[c; &0],vector[b; &1]]) f
     ==> pl_map_on (interval[vector[a; &0],vector[b; &1]]) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real`; `c:real`; `b:real`] MOI_LC0_RECT_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN
  REWRITE_TAC[CLOSED_INTERVAL] THEN SET_TAC[]);;

(* The four boundary arcs of [a,b] x [0,1] between the ends of the chords *)
(* x = s and x = t: their ends, images, pairwise intersections and union.  *)

let MOI_LC0_RECT_ARCS = prove
 (`!a s t b.
     a < s /\ s < t /\ t < b
     ==> arc (moi_lc0_larc a s) /\
         arc (linepath(vector[s; &0]:real^2,vector[t; &0])) /\
         arc (moi_lc0_rarc t b) /\
         arc (linepath(vector[t; &1]:real^2,vector[s; &1])) /\
         pathstart (moi_lc0_larc a s) = vector[s; &1] /\
         pathfinish (moi_lc0_larc a s) = vector[s; &0] /\
         pathstart (moi_lc0_rarc t b) = vector[t; &0] /\
         pathfinish (moi_lc0_rarc t b) = vector[t; &1] /\
         path_image (moi_lc0_larc a s) INTER
         path_image (linepath(vector[s; &0],vector[t; &0])) = {vector[s; &0]} /\
         path_image (linepath(vector[s; &0],vector[t; &0])) INTER
         path_image (moi_lc0_rarc t b) = {vector[t; &0]} /\
         path_image (moi_lc0_rarc t b) INTER
         path_image (linepath(vector[t; &1],vector[s; &1])) = {vector[t; &1]} /\
         path_image (linepath(vector[t; &1],vector[s; &1])) INTER
         path_image (moi_lc0_larc a s) = {vector[s; &1]} /\
         path_image (moi_lc0_larc a s) INTER path_image (moi_lc0_rarc t b) = {} /\
         path_image (linepath(vector[s; &0],vector[t; &0])) INTER
         path_image (linepath(vector[t; &1]:real^2,vector[s; &1])) = {} /\
         path_image (moi_lc0_larc a s) UNION
         path_image (linepath(vector[s; &0],vector[t; &0])) UNION
         path_image (moi_lc0_rarc t b) UNION
         path_image (linepath(vector[t; &1],vector[s; &1])) =
         frontier (interval[vector[a; &0],vector[b; &1]])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real`; `s:real`] MOI_LC0_LARC) THEN
  MP_TAC(ISPECL [`t:real`; `b:real`] MOI_LC0_RARC) THEN
  MP_TAC(ISPECL [`a:real`; `b:real`] MOI_LC0_RECT_FACTS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `s <= t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[PATH_IMAGE_LINEPATH; MOI_LC0_HSEG; ARC_LINEPATH_EQ; MOI_LC0_VECTOR2_INJ] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM; IN_SING; NOT_IN_EMPTY;
              MOI_LC0_VECTOR2_EQ] THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN
  ASM_CASES_TAC `(x:real^2)$2 = &0` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  ASM_CASES_TAC `(x:real^2)$2 = &1` THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  ASM_REAL_ARITH_TAC);;

