(* ========================================================================= *)
(* Unit pc_rfs_ccscpush: general position for maps of compact               *)
(* low-dimensional spaces into Hausdorff spaces with ball charts.           *)
(* A ball chart of radius r is a homeomorphism b of ball(0,r) in real^N     *)
(* onto an open set.  A continuous map H of a compact space X that embeds   *)
(* in real^M, M < N, is homotopic to a map that misses the closed ball      *)
(* b(cball(0,r1)), r1 < r, and differs from H only where H lies in          *)
(* b(ball(0,r)) (CCS_PUSH_OFF_BALL); the same for finitely many disjoint    *)
(* ball charts (CCS_PUSH_OFF_BALLS).  Loops are circle maps (CCS_LOOP_      *)
(* CIRCLE), so loops in a manifold of dimension at least 3 can be pushed    *)
(* off finitely many closed balls by a homotopy of loops                    *)
(* (CCS_LOOP_PUSH_OFF_BALLS).  Route: ATOP_PUSH_OFF_CHART (pc_top_genpos)   *)
(* on the closed preimage of a half ball, a straight-line homotopy in the   *)
(* chart, and the radial push |y| -> max(|y|,a).                            *)
(* ========================================================================= *)

needs "src/pc_top_genpos.ml";;

prioritize_real();;
type_invention_error := true;;

(* The homeomorphism of real^N onto ball(0,r): v -> r v / (1 + |v|).        *)

let CCS_BALL_UNIV_HOMEO = prove
 (`!r. &0 < r
       ==> homeomorphic_maps
             (euclidean:(real^N)topology,
              subtopology euclidean (ball(vec 0:real^N,r)))
             ((\v. r % (inv(&1 + norm v) % v)),(\u. inv(r - norm u) % u))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              CONTINUOUS_MAP_EUCLIDEAN_EUCLIDEAN; CONTINUOUS_MAP_EUCLIDEAN;
              SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_BALL_0] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN
    SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= x ==> ~(&1 + x = &0)`] THEN
    REWRITE_TAC[o_DEF; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_ID];
    X_GEN_TAC `v:real^N` THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`;
                 REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `inv(&1 + norm(v:real^N)) * norm v < &1` MP_TAC THENL
     [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ;
                   REAL_ARITH `&0 <= x ==> &0 < &1 + x`] THEN
      REAL_ARITH_TAC;
      DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `r * x < r * &1 ==> r * x < r`) THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN
    SIMP_TAC[IN_BALL_0; REAL_SUB_0; REAL_ARITH `x < r ==> ~(r = x)`] THEN
    REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_ID];
    X_GEN_TAC `v:real^N` THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_INV; REAL_ABS_MUL] THEN
    MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`;
                 REAL_ARITH `&0 <= x ==> abs(&1 + x) = &1 + x`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `r - r * inv(&1 + norm(v:real^N)) * norm v = r * inv(&1 + norm v)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 <= norm(v:real^N)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[VECTOR_MUL_LID] `!c v:real^N. c = &1 ==> c % v = v`) THEN
    UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 <= norm(v:real^N)` THEN
    CONV_TAC REAL_FIELD;
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `x < r ==> abs(r - x) = r - x`] THEN
    MATCH_MP_TAC(MESON[VECTOR_MUL_LID] `!c v:real^N. c = &1 ==> c % v = v`) THEN
    SUBGOAL_THEN `&1 + inv(r - norm(u:real^N)) * norm u = r * inv(r - norm u)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `norm(u:real^N) < r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    UNDISCH_TAC `&0 < r` THEN
    UNDISCH_TAC `norm(u:real^N) < r` THEN CONV_TAC REAL_FIELD]);;

(* Pasting two closed pieces (PASTING_LEMMA_CLOSED with two indices).      *)

let CCS_CONTINUOUS_MAP_CLOSED_CASES = prove
 (`!top top' s t (f:A->B) g h.
        closed_in top s /\ closed_in top t /\ topspace top SUBSET s UNION t /\
        continuous_map (subtopology top s,top') f /\
        continuous_map (subtopology top t,top') g /\
        (!x. x IN topspace top /\ x IN s /\ x IN t ==> f x = g x) /\
        (!x. x IN topspace top /\ x IN s ==> h x = f x) /\
        (!x. x IN topspace top /\ x IN t ==> h x = g x)
        ==> continuous_map (top,top') h`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:bool`,`:K`] PASTING_LEMMA_CLOSED) THEN
  MAP_EVERY EXISTS_TAC
   [`\b. if b then (f:A->B) else g`; `\b. if b then (s:A->bool) else t`;
    `{T,F}`] THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
              EXISTS_IN_INSERT] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MAP_EVERY BOOL_CASES_TAC [`i:bool`; `j:bool`] THEN
    REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_CASES_TAC `(x:A) IN s` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[]]);;

(* A map of the second factor, restricted to the preimage of k.            *)

let CCS_CONTINUOUS_MAP_SND_RESTRICT = prove
 (`!(top1:C topology) (X:B topology) (Y:A topology) k g.
        continuous_map (subtopology X k,Y) g
        ==> continuous_map
              (subtopology (prod_topology top1 X)
                 {p | p IN topspace(prod_topology top1 X) /\ SND p IN k},Y)
              (\p. g(SND p))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology X (k:B->bool)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[CONTINUOUS_MAP_SND];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER;
                IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM;
                IN_CROSS] THEN
    SIMP_TAC[]]);;

(* Two maps that agree off a closed set k, which both map into the image   *)
(* of a convex set s under a chart b, are homotopic (straight line in the  *)
(* chart on k, constant off k).                                            *)

let CCS_HOMOTOPIC_IN_CHART = prove
 (`!X top (H:B->A) H' (b:real^N->A) s k.
        hausdorff_space top /\ convex s /\
        homeomorphic_map (subtopology euclidean s,subtopology top (IMAGE b s)) b /\
        continuous_map (X,top) H /\ continuous_map (X,top) H' /\
        closed_in X k /\
        (!z. z IN topspace X /\ ~(z IN k) ==> H' z = H z) /\
        (!z. z IN k ==> H z IN IMAGE b s /\ H' z IN IMAGE b s)
        ==> homotopic_with (\h. T) (X,top) H H'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b':A->real^N` MP_TAC) THEN
  REWRITE_TAC[homeomorphic_maps; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
              INTER_UNIV; IN_INTER] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(k:B->bool) SUBSET topspace X` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:B. z IN topspace X ==> (H:B->A) z IN topspace top /\
                                          (H':B->A) z IN topspace top`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; SUBSET; IN_IMAGE];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC [`H:B->A`; `\z:B. if z IN k then (H':B->A) z else H z`] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `z:B` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[]] THEN
  REWRITE_TAC[homotopic_with] THEN
  EXISTS_TAC
   `\p:real#B. if SND p IN k
               then (b:real^N->A)((&1 - FST p) % (b':A->real^N)((H:B->A)(SND p)) +
                                   FST p % b'((H':B->A)(SND p)))
               else H(SND p)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `z:B` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LZERO; VECTOR_MUL_LID;
                VECTOR_ADD_RID] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    X_GEN_TAC `z:B` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_LID;
                VECTOR_ADD_LID] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC CCS_CONTINUOUS_MAP_CLOSED_CASES THEN
  MAP_EVERY EXISTS_TAC
   [`{p | p IN topspace(prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                     (X:B topology)) /\ SND p IN k}`;
    `{p | p IN topspace(prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                     (X:B topology)) /\
          SND p IN {z | z IN topspace X /\ (H':B->A) z = H z}}`;
    `\p:real#B. (b:real^N->A)((&1 - FST p) % (b':A->real^N)((H:B->A)(SND p)) +
                               FST p % b'((H':B->A)(SND p)))`;
    `\p:real#B. (H:B->A)(SND p)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `X:B topology` THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_SND];
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `X:B topology` THEN REWRITE_TAC[CONTINUOUS_MAP_SND] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAPS_EQ THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY;
                FORALL_PAIR_THM; IN_CROSS] THEN
    ASM_MESON_TAC[];
    ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `X:B topology` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_SND];
    REWRITE_TAC[IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM;
                IN_CROSS] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(&1 - t) % v + t % v:real^N = v`] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(&1 - t) % v + t % v:real^N = v`] THEN
    ASM_MESON_TAC[]] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology euclidean (s:real^N->bool)` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `IMAGE (b:real^N->A) s` THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!G:B->A. continuous_map (X,top) G /\
            (!z. z IN k ==> G z IN IMAGE (b:real^N->A) (s:real^N->bool))
            ==> continuous_map
                  (subtopology
                    (prod_topology (subtopology euclideanreal (real_interval[&0,&1]))
                                   X)
                    {p | p IN topspace(prod_topology
                                (subtopology euclideanreal (real_interval[&0,&1])) X) /\
                         SND p IN k},
                   euclidean)
                  (\p:real#B. (b':A->real^N)(G(SND p)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`subtopology euclideanreal (real_interval[&0,&1])`;
                   `X:B topology`; `euclidean:(real^N)topology`; `k:B->bool`;
                   `\z:B. (b':A->real^N)((G:B->A) z)`]
                  CCS_CONTINUOUS_MAP_SND_RESTRICT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top (IMAGE (b:real^N->A) s)` THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN ASM_SIMP_TAC[] THEN
    TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
        REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST]) THEN
    REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
    EXISTS_TAC `real_interval[&0,&1]` THEN REWRITE_TAC[CONTINUOUS_MAP_FST];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER;
              IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `z:B`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONVEX_ALT]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
    check (fun th -> free_in `b':A->real^N` (concl th) &&
                     is_comb (concl th) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER;
              TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pushing a map off the centre of a ball chart, and the                     *)
(* radial push off a closed sub-ball.                                       *)
(* ------------------------------------------------------------------------- *)

(* ATOP_PUSH_OFF_CHART applied in the open set w = b(ball(0,r)) to the      *)
(* closed preimage of the half ball: the new map misses the centre, agrees *)
(* with H where H is outside w, stays in w where H is in w, and is         *)
(* homotopic to H.                                                          *)

let CCS_PUSH_OFF_CENTRE = prove
 (`!X top (H:B->A) (iota:B->real^M) (b:real^N->A) r.
        dimindex(:M) < dimindex(:N) /\
        compact_space X /\ continuous_map (X,euclidean) iota /\
        (!y z. y IN topspace X /\ z IN topspace X /\ iota y = iota z ==> y = z) /\
        hausdorff_space top /\ continuous_map (X,top) H /\ &0 < r /\
        open_in top (IMAGE b (ball(vec 0,r))) /\
        homeomorphic_map (subtopology euclidean (ball(vec 0,r)),
                          subtopology top (IMAGE b (ball(vec 0,r)))) b
        ==> ?H'. continuous_map (X,top) H' /\
                 (!z. z IN topspace X ==> ~(H' z = b(vec 0))) /\
                 (!z. z IN topspace X /\ ~(H z IN IMAGE b (ball(vec 0,r)))
                      ==> H' z = H z) /\
                 (!z. z IN topspace X /\ H z IN IMAGE b (ball(vec 0,r))
                      ==> H' z IN IMAGE b (ball(vec 0,r))) /\
                 homotopic_with (\h. T) (X,top) H H'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `w = IMAGE (b:real^N->A) (ball(vec 0,r))` THEN
  ABBREV_TAC `e = \v:real^N. (b:real^N->A)(r % (inv(&1 + norm v) % v))` THEN
  SUBGOAL_THEN `homeomorphic_map (euclidean,subtopology top w) (e:real^N->A)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(e:real^N->A) = b o (\v:real^N. r % (inv(&1 + norm v) % v))`
    SUBST1_TAC THENL
     [EXPAND_TAC "e" THEN REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^N,r))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHIC_MAPS_IMP_MAP THEN
    EXISTS_TAC `\u:real^N. inv(r - norm u) % u` THEN
    ASM_SIMP_TAC[CCS_BALL_UNIV_HOMEO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `w:A->bool`; `e:real^N->A`]
                ATOP_INVERSE_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:A->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(e:real^N->A)(vec 0) = (b:real^N->A)(vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:B. z IN topspace X ==> (H:B->A) z IN topspace top`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; SUBSET; IN_IMAGE];
    ALL_TAC] THEN
  ABBREV_TAC
   `K = {z | z IN topspace X /\
             (H:B->A) z IN IMAGE (e:real^N->A) (cball(vec 0,&1))}` THEN
  SUBGOAL_THEN
   `!z:B. z IN K <=>
          z IN topspace X /\ (H:B->A) z IN IMAGE (e:real^N->A) (cball(vec 0,&1))`
  (LABEL_TAC "Kdef") THENL
   [EXPAND_TAC "K" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `closed_in X (K:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_SIMP_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology X (K:B->bool)`; `subtopology top (w:A->bool)`;
                 `H:B->A`; `iota:B->real^M`; `w:A->bool`; `e:real^N->A`]
                ATOP_PUSH_OFF_CHART) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; CLOSED_IN_COMPACT_SPACE;
                 CONTINUOUS_MAP_FROM_SUBTOPOLOGY; HAUSDORFF_SPACE_SUBTOPOLOGY;
                 OPEN_IN_SUBTOPOLOGY_REFL; SUBTOPOLOGY_SUBTOPOLOGY;
                 INTER_IDEMPOT] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    X_GEN_TAC `z:B` THEN USE_THEN "Kdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `H0:B->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z:B. z IN K ==> (H0:B->A) z IN w` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> free_in `H0:B->A` (concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    USE_THEN "Kdef" (fun th -> REWRITE_TAC[th]) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:B. z IN K ==> (H:B->A) z IN w` ASSUME_TAC THENL
   [USE_THEN "Kdef" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\z:B. if z IN K then (H0:B->A) z else H z` THEN
  SUBGOAL_THEN
   `!z:B. z IN topspace X /\ ~((H:B->A) z IN IMAGE (e:real^N->A) (ball(vec 0,&1)))
          ==> (if z IN K then (H0:B->A) z else H z) = H z`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `continuous_map (X,top) (\z:B. if z IN K then (H0:B->A) z else H z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CCS_CONTINUOUS_MAP_CLOSED_CASES THEN
    MAP_EVERY EXISTS_TAC
     [`K:B->bool`;
      `{z | z IN topspace X /\
            (H:B->A) z IN topspace top DIFF IMAGE (e:real^N->A) (ball(vec 0,&1))}`;
      `H0:B->A`; `H:B->A`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_IN_DIFF THEN
      ASM_SIMP_TAC[CLOSED_IN_TOPSPACE; OPEN_BALL];
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; IN_DIFF] THEN
      USE_THEN "Kdef" (fun th -> REWRITE_TAC[th]) THEN
      X_GEN_TAC `z:B` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(H:B->A) z IN IMAGE (e:real^N->A) (ball(vec 0,&1))` THEN
      ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[IMAGE_SUBSET; BALL_SUBSET_CBALL; SUBSET];
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[];
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `z:B` THEN DISCH_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((z:B) IN K)` THEN USE_THEN "Kdef" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^N` THEN
    ASM_REWRITE_TAC[CENTRE_IN_CBALL; REAL_POS];
    X_GEN_TAC `z:B` THEN STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    X_GEN_TAC `z:B` THEN STRIP_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC CCS_HOMOTOPIC_IN_CHART THEN
    MAP_EVERY EXISTS_TAC [`b:real^N->A`; `ball(vec 0:real^N,r)`; `K:B->bool`] THEN
    REWRITE_TAC[CONVEX_BALL; ASSUME `IMAGE (b:real^N->A) (ball(vec 0,r)) = w`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN TRY COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

(* Pasting two open pieces.                                                 *)

let CCS_CONTINUOUS_MAP_OPEN_CASES = prove
 (`!top top' s t (f:A->B) g h.
        open_in top s /\ open_in top t /\ topspace top SUBSET s UNION t /\
        continuous_map (subtopology top s,top') f /\
        continuous_map (subtopology top t,top') g /\
        (!x. x IN topspace top /\ x IN s ==> h x = f x) /\
        (!x. x IN topspace top /\ x IN t ==> h x = g x)
        ==> continuous_map (top,top') h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC TOPC_CONTINUOUS_MAP_LOCAL THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN s \/ x IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[];
    EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `f:A->B` THEN
    ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER];
    EXISTS_TAC `t:A->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN EXISTS_TAC `g:A->B` THEN
    ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER]]);;

let CCS_CONTINUOUS_MAP_NORM = prove
 (`!top (f:A->real^N).
        continuous_map (top,euclidean) f
        ==> continuous_map (top,euclideanreal) (\x. norm(f x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_norm] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_SQRT THEN MATCH_MP_TAC CONTINUOUS_MAP_DOT THEN
  ASM_REWRITE_TAC[]);;

(* The radial push y -> (1 + t (max(|y|,a)/|y| - 1)) y moves |y| to        *)
(* |y| + t (max(|y|,a) - |y|).                                              *)

let CCS_RADIAL_NORM = prove
 (`!(y:real^N) a t.
        ~(y = vec 0) /\ &0 <= t
        ==> norm((&1 + t * (max (norm y) a / norm y - &1)) % y) =
            norm y + t * (max (norm y) a - norm y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_MUL] THEN
  SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `n = norm(y:real^N)` THEN ABBREV_TAC `m = max n a` THEN
  SUBGOAL_THEN `n <= m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= m / n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + t * (m / n - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  UNDISCH_TAC `&0 < n` THEN CONV_TAC REAL_FIELD);;

(* A map missing the centre of a ball chart b on ball(0,r) is homotopic,   *)
(* by the radial push |y| -> max(|y|,a) with a = (r1 + r) / 2, to a map    *)
(* missing the closed ball b(cball(0,r1)), changed only inside b(ball r).  *)

let CCS_RADIAL_PUSH = prove
 (`!X top (H:B->A) (b:real^N->A) r r1.
        hausdorff_space top /\ continuous_map (X,top) H /\
        &0 < r1 /\ r1 < r /\
        open_in top (IMAGE b (ball(vec 0,r))) /\
        homeomorphic_map (subtopology euclidean (ball(vec 0,r)),
                          subtopology top (IMAGE b (ball(vec 0,r)))) b /\
        (!z. z IN topspace X ==> ~(H z = b(vec 0)))
        ==> ?H'. continuous_map (X,top) H' /\
                 (!z. z IN topspace X ==> ~(H' z IN IMAGE b (cball(vec 0,r1)))) /\
                 (!z. z IN topspace X /\ ~(H z IN IMAGE b (ball(vec 0,r)))
                      ==> H' z = H z) /\
                 (!z. z IN topspace X /\ H z IN IMAGE b (ball(vec 0,r))
                      ==> H' z IN IMAGE b (ball(vec 0,r))) /\
                 homotopic_with (\h. T) (X,top) H H'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `w = IMAGE (b:real^N->A) (ball(vec 0,r))` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b':A->real^N` MP_TAC) THEN
  REWRITE_TAC[homeomorphic_maps; TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN;
              INTER_UNIV; IN_INTER] THEN
  STRIP_TAC THEN
  ABBREV_TAC `a = (r1 + r) / &2` THEN
  SUBGOAL_THEN `r1 < a /\ a < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(w:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:B. z IN topspace X ==> (H:B->A) z IN topspace top`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; SUBSET; IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN w ==> (b':A->real^N) y IN ball(vec 0,r)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> free_in `b':A->real^N` (concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER;
                TOPSPACE_EUCLIDEAN; INTER_UNIV] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN w ==> (b:real^N->A)((b':A->real^N) y) = y`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. v IN ball(vec 0,r) ==> (b:real^N->A) v IN w`
  ASSUME_TAC THENL [EXPAND_TAC "w" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:B. z IN topspace X /\ (H:B->A) z IN w ==> ~((b':A->real^N)(H z) = vec 0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `!z:B. z IN topspace X ==> ~((H:B->A) z = (b:real^N->A)(vec 0))` THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `z:B` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:A s. y IN w /\ s < r
            ==> (y IN IMAGE (b:real^N->A) (cball(vec 0,s)) <=>
                 (b':A->real^N) y IN cball(vec 0,s))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `v IN ball(vec 0:real^N,r)` ASSUME_TAC THENL
       [UNDISCH_TAC `v IN cball(vec 0:real^N,s)` THEN
        REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[]];
      DISCH_TAC THEN EXISTS_TAC `(b':A->real^N) y` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in top (IMAGE (b:real^N->A) (cball(vec 0,a)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (ball(vec 0:real^N,r))` THEN
    REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (b:real^N->A) (cball(vec 0,a)) SUBSET w` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `rho = \t (v:real^N). (&1 + t * (max (norm v) a / norm v - &1)) % v` THEN
  SUBGOAL_THEN
   `!t v:real^N. ~(v = vec 0) /\ &0 <= t
                 ==> norm((rho:real->real^N->real^N) t v) =
                     norm v + t * (max (norm v) a - norm v)`
  ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[] THEN MESON_TAC[CCS_RADIAL_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. (rho:real->real^N->real^N) (&0) v = v`
  ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID;
                                      VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t v:real^N. a < norm v ==> (rho:real->real^N->real^N) t v = v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "rho" THEN
    SUBGOAL_THEN `max (norm(v:real^N)) a = norm v` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(v:real^N) / norm v = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_DIV_REFL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_ADD_RID; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t v:real^N. v IN ball(vec 0,r) /\ ~(v = vec 0) /\
                 &0 <= t /\ t <= &1
                 ==> (rho:real->real^N->real^N) t v IN ball(vec 0,r)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[IN_BALL_0] THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(v:real^N) IN ball(vec 0,r)` THEN REWRITE_TAC[IN_BALL_0] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `max (norm(v:real^N)) a < r` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `t * (max (norm(v:real^N)) a - norm v) <=
                  &1 * (max (norm v) a - norm v)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC
   `\z:B. if (H:B->A) z IN w
          then (b:real^N->A)((rho:real->real^N->real^N) (&1) ((b':A->real^N)(H z)))
          else H z` THEN
  ABBREV_TAC `kw = {z | z IN topspace X /\ (H:B->A) z IN w}` THEN
  ABBREV_TAC
   `ko = {z | z IN topspace X /\
              (H:B->A) z IN topspace top DIFF IMAGE (b:real^N->A) (cball(vec 0,a))}` THEN
  SUBGOAL_THEN `open_in X (kw:B->bool) /\ open_in X (ko:B->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["kw"; "ko"] THEN CONJ_TAC THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology X kw,euclidean)
                   (\z:B. (b':A->real^N)((H:B->A) z))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top (w:A->bool)` THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
      EXPAND_TAC "kw" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER;
                  IN_ELIM_THM] THEN
      SIMP_TAC[];
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `ball(vec 0:real^N,r)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclideanreal (real_interval[&0,&1])`;
                 `X:B topology`; `euclidean:(real^N)topology`; `kw:B->bool`;
                 `\z:B. (b':A->real^N)((H:B->A) z)`]
                CCS_CONTINUOUS_MAP_SND_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC
   `sw = {p | p IN topspace(prod_topology
                (subtopology euclideanreal (real_interval[&0,&1])) (X:B topology)) /\
              SND p IN kw}` THEN
  SUBGOAL_THEN
   `!p. p IN sw
        ==> FST p IN real_interval[&0,&1] /\ SND p IN topspace X /\
            (H:B->A)(SND p) IN w /\ ~((b':A->real^N)(H(SND p)) = vec 0) /\
            b'(H(SND p)) IN ball(vec 0,r)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["sw"; "kw"] THEN
    REWRITE_TAC[IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY; FORALL_PAIR_THM; IN_CROSS;
                TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map
      (subtopology (prod_topology
         (subtopology euclideanreal (real_interval[&0,&1])) (X:B topology)) sw,
       euclideanreal)
      (\p:real#B. &1 + FST p * (max (norm((b':A->real^N)((H:B->A)(SND p)))) a /
                                norm(b'(H(SND p))) - &1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN
    REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
      EXISTS_TAC `real_interval[&0,&1]` THEN REWRITE_TAC[CONTINUOUS_MAP_FST];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
    REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
      MATCH_MP_TAC CCS_CONTINUOUS_MAP_NORM THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CCS_CONTINUOUS_MAP_NORM THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; NORM_EQ_0] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_with (\h. T) (X,top) (H:B->A)
      (\z. if H z IN w then (b:real^N->A)((rho:real->real^N->real^N) (&1)
                                            ((b':A->real^N)(H z)))
           else H z)`
  ASSUME_TAC THENL
   [REWRITE_TAC[homotopic_with] THEN
    EXISTS_TAC
     `\p:real#B. if (H:B->A)(SND p) IN w
                 then (b:real^N->A)((rho:real->real^N->real^N) (FST p)
                                     ((b':A->real^N)(H(SND p))))
                 else H(SND p)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `z:B` THEN COND_CASES_TAC THEN ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC CCS_CONTINUOUS_MAP_OPEN_CASES THEN
    MAP_EVERY EXISTS_TAC
     [`sw:real#B->bool`;
      `{p | p IN topspace(prod_topology
              (subtopology euclideanreal (real_interval[&0,&1])) (X:B topology)) /\
            SND p IN ko}`;
      `\p:real#B. (b:real^N->A)((rho:real->real^N->real^N) (FST p)
                                  ((b':A->real^N)((H:B->A)(SND p))))`;
      `\p:real#B. (H:B->A)(SND p)`] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "sw" THEN MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `X:B topology` THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_SND];
      MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
      EXISTS_TAC `X:B topology` THEN ASM_REWRITE_TAC[CONTINUOUS_MAP_SND];
      MAP_EVERY EXPAND_TAC ["sw"; "kw"; "ko"] THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; TOPSPACE_PROD_TOPOLOGY;
                  FORALL_PAIR_THM; IN_CROSS; IN_DIFF] THEN
      MP_TAC(ASSUME `IMAGE (b:real^N->A) (cball(vec 0,a)) SUBSET w`) THEN
      MP_TAC(ASSUME `!z:B. z IN topspace X ==> (H:B->A) z IN topspace top`) THEN
      REWRITE_TAC[SUBSET] THEN MESON_TAC[];
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclidean (ball(vec 0:real^N,r))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC CONTINUOUS_MAP_INTO_FULLTOPOLOGY THEN
        EXISTS_TAC `w:A->bool` THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [EXPAND_TAC "rho" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_VECTOR_MUL THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
        X_GEN_TAC `p:real#B` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          try fst(dest_const(fst(strip_comb(rand(snd(strip_forall(concl th))))))) = "IN" &&
              free_in `rho:real->real^N->real^N` (concl th) &&
              is_imp(snd(strip_forall(concl th)))
          with Failure _ -> false)) THEN
        UNDISCH_TAC `(p:real#B) IN sw` THEN
        FIRST_X_ASSUM(fun th -> if free_in `sw:real#B->bool` (concl th) &&
                                   is_forall(concl th)
                                then MP_TAC(SPEC `p:real#B` th) else NO_TAC) THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN MESON_TAC[]];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC `X:B topology` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_SND];
      EXPAND_TAC "sw" THEN EXPAND_TAC "kw" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      EXPAND_TAC "ko" THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `a < norm((b':A->real^N)((H:B->A)(SND(x:real#B))))`
      ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LE; GSYM IN_CBALL_0] THEN
        ASM_MESON_TAC[];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z:B. z IN topspace X /\ (H:B->A) z IN w
          ==> (rho:real->real^N->real^N) (&1) ((b':A->real^N)(H z)) IN
              ball(vec 0,r) /\
              a <= norm(rho (&1) (b'(H z)))`
  (LABEL_TAC "rho1") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        try fst(dest_const(fst(strip_comb(rand(snd(strip_forall(concl th))))))) = "IN" &&
            free_in `rho:real->real^N->real^N` (concl th) &&
            is_imp(snd(strip_forall(concl th)))
        with Failure _ -> false)) THEN
      REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[REAL_POS] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. v IN ball(vec 0,r) /\
               (b:real^N->A) v IN IMAGE b (cball(vec 0,r1))
               ==> norm v <= r1`
  (LABEL_TAC "cb") THENL
   [X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(u:real^N) IN ball(vec 0,r)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN
      MAP_EVERY UNDISCH_TAC [`norm(u:real^N) <= r1`; `r1 < r`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `v:real^N = u` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC(SPEC `v:real^N` (ASSUME
      `!x:real^N. x IN ball(vec 0,r) ==> (b':A->real^N)(b x) = x`)) THEN
    MP_TAC(SPEC `u:real^N` (ASSUME
      `!x:real^N. x IN ball(vec 0,r) ==> (b':A->real^N)(b x) = x`)) THEN
    REWRITE_TAC[ASSUME `(v:real^N) IN ball(vec 0,r)`;
                ASSUME `(u:real^N) IN ball(vec 0,r)`] THEN
    MP_TAC(ASSUME `(b:real^N->A) v = b u`) THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:B` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ALL_TAC;
      UNDISCH_TAC `~((H:B->A) z IN w)` THEN
      MATCH_MP_TAC(SET_RULE `(s:A->bool) SUBSET t ==> ~((x:A) IN t) ==> ~(x IN s)`) THEN
      EXPAND_TAC "w" THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN X_GEN_TAC `x:real^N` THEN
      MP_TAC(ASSUME `r1 < r`) THEN REAL_ARITH_TAC] THEN
    REMOVE_THEN "rho1" (MP_TAC o SPEC `z:B`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN DISCH_TAC THEN
    REMOVE_THEN "cb" (MP_TAC o SPEC
      `(rho:real->real^N->real^N) (&1) ((b':A->real^N)((H:B->A) z))`) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`a <= norm((rho:real->real^N->real^N) (&1) ((b':A->real^N)((H:B->A) z)))`;
      `r1 < a`] THEN
    REAL_ARITH_TAC;
    SIMP_TAC[];
    SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    REMOVE_THEN "rho1" (MP_TAC o SPEC `z:B`) THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Pushing off one closed ball, then off finitely many                       *)
(* disjoint ones.                                                           *)
(* ------------------------------------------------------------------------- *)

let CCS_PUSH_OFF_BALL = prove
 (`!X top (H:B->A) (iota:B->real^M) (b:real^N->A) r r1.
        dimindex(:M) < dimindex(:N) /\
        compact_space X /\ continuous_map (X,euclidean) iota /\
        (!y z. y IN topspace X /\ z IN topspace X /\ iota y = iota z ==> y = z) /\
        hausdorff_space top /\ continuous_map (X,top) H /\
        &0 < r1 /\ r1 < r /\
        open_in top (IMAGE b (ball(vec 0,r))) /\
        homeomorphic_map (subtopology euclidean (ball(vec 0,r)),
                          subtopology top (IMAGE b (ball(vec 0,r)))) b
        ==> ?H'. continuous_map (X,top) H' /\
                 (!z. z IN topspace X ==> ~(H' z IN IMAGE b (cball(vec 0,r1)))) /\
                 (!z. z IN topspace X /\ ~(H z IN IMAGE b (ball(vec 0,r)))
                      ==> H' z = H z) /\
                 (!z. z IN topspace X /\ H z IN IMAGE b (ball(vec 0,r))
                      ==> H' z IN IMAGE b (ball(vec 0,r))) /\
                 homotopic_with (\h. T) (X,top) H H'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:B topology`; `top:A topology`; `H:B->A`; `iota:B->real^M`;
                 `b:real^N->A`; `r:real`] CCS_PUSH_OFF_CENTRE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < r1`; `r1 < r`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H1:B->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X:B topology`; `top:A topology`; `H1:B->A`;
                 `b:real^N->A`; `r:real`; `r1:real`] CCS_RADIAL_PUSH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H2:B->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `H2:B->A` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[HOMOTOPIC_WITH_TRANS]]);;

let CCS_PUSH_OFF_BALLS = prove
 (`!X top (H:B->A) (iota:B->real^M) (bs:(real^N->A)->bool) r r1.
        dimindex(:M) < dimindex(:N) /\
        compact_space X /\ continuous_map (X,euclidean) iota /\
        (!y z. y IN topspace X /\ z IN topspace X /\ iota y = iota z ==> y = z) /\
        hausdorff_space top /\ continuous_map (X,top) H /\
        &0 < r1 /\ r1 < r /\ FINITE bs /\
        (!b. b IN bs
             ==> open_in top (IMAGE b (ball(vec 0,r))) /\
                 homeomorphic_map (subtopology euclidean (ball(vec 0,r)),
                                   subtopology top (IMAGE b (ball(vec 0,r)))) b) /\
        (!b b'. b IN bs /\ b' IN bs /\ ~(b = b')
                ==> DISJOINT (IMAGE b (ball(vec 0,r))) (IMAGE b' (ball(vec 0,r))))
        ==> ?H'. continuous_map (X,top) H' /\
                 (!z b. z IN topspace X /\ b IN bs
                        ==> ~(H' z IN IMAGE b (cball(vec 0,r1)))) /\
                 homotopic_with (\h. T) (X,top) H H'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e /\ f /\ g /\ h /\ i /\ j /\ k ==> l <=>
                    a /\ b /\ c /\ d /\ e /\ g /\ h ==> i ==> f /\ j /\ k ==> l`] THEN
  STRIP_TAC THEN DISCH_TAC THEN SPEC_TAC(`H:B->A`,`H:B->A`) THEN
  UNDISCH_TAC `FINITE(bs:(real^N->A)->bool)` THEN
  SPEC_TAC(`bs:(real^N->A)->bool`,`bs:(real^N->A)->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `H:B->A` THEN ASM_REWRITE_TAC[HOMOTOPIC_WITH_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`b:real^N->A`; `bs:(real^N->A)->bool`] THEN
  STRIP_TAC THEN X_GEN_TAC `H:B->A` THEN
  REWRITE_TAC[FORALL_IN_INSERT; IN_INSERT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `H:B->A`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H1:B->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`X:B topology`; `top:A topology`; `H1:B->A`; `iota:B->real^M`;
                 `b:real^N->A`; `r:real`; `r1:real`] CCS_PUSH_OFF_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H2:B->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `H2:B->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[HOMOTOPIC_WITH_TRANS]] THEN
  MAP_EVERY X_GEN_TAC [`z:B`; `c:real^N->A`] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(c:real^N->A = b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (c:real^N->A) (cball(vec 0,r1)) SUBSET IMAGE c (ball(vec 0,r))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN
    X_GEN_TAC `x:real^N` THEN MP_TAC(ASSUME `r1 < r`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(H1:B->A) z IN IMAGE (b:real^N->A) (ball(vec 0,r))` THENL
   [SUBGOAL_THEN `(H2:B->A) z IN IMAGE (b:real^N->A) (ball(vec 0,r))` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `DISJOINT (IMAGE (b:real^N->A) (ball(vec 0,r))) (IMAGE (c:real^N->A) (ball(vec 0,r)))`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `IMAGE (c:real^N->A) (cball(vec 0,r1)) SUBSET IMAGE c (ball(vec 0,r))` THEN
    SET_TAC[];
    SUBGOAL_THEN `(H2:B->A) z = H1 z` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Loops as maps of the circle.                                             *)
(* ------------------------------------------------------------------------- *)

let CCS_CEXP_2PI = prove
 (`cexp(ii * Cx(&2 * pi * &1)) = cexp(ii * Cx(&2 * pi * &0))`,
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; COMPLEX_MUL_RZERO; CEXP_0] THEN
  REWRITE_TAC[CEXP_EULER; GSYM CX_COS; GSYM CX_SIN; COS_NPI; SIN_NPI] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]);;

let CCS_CIRCLE_PATH = prove
 (`continuous_map (subtopology euclideanreal (real_interval[&0,&1]),
                   subtopology euclidean (sphere(vec 0:real^2,&1)))
                  (\t. cexp(ii * Cx(&2 * pi * t))) /\
   IMAGE (\t. cexp(ii * Cx(&2 * pi * t))) (real_interval[&0,&1]) =
   sphere(vec 0:real^2,&1)`,
  CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`&2 * pi`; `&0`] TOPC_CEXP_PATH_CONTINUOUS) THEN
      REWRITE_TAC[REAL_ADD_RID; REAL_MUL_ASSOC];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                  IN_SPHERE_0; NORM_CEXP_II]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SPHERE_0; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `z:complex` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[NORM_CEXP_II]; ALL_TAC] THEN
    DISCH_TAC THEN EXISTS_TAC `Arg z / (&2 * pi)` THEN
    MP_TAC(SPEC `z:complex` ARG) THEN ASM_REWRITE_TAC[COMPLEX_MUL_LID] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &2 * pi` ASSUME_TAC THENL
     [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_DIV_LMUL;
                 REAL_LT_IMP_NZ; REAL_MUL_LID] THEN
    SUBGOAL_THEN `&2 * pi * Arg z / (&2 * pi) = Arg z` SUBST1_TAC THENL
     [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; FIRST_ASSUM ACCEPT_TAC]]);;

let CCS_LOOP_CIRCLE = prove
 (`!top (g:real->A).
        path_in top g /\ g(&1) = g(&0)
        ==> ?G. continuous_map
                  (subtopology euclidean (sphere(vec 0:real^2,&1)),top) G /\
                !t. t IN real_interval[&0,&1]
                    ==> G(cexp(ii * Cx(&2 * pi * t))) = g t`,
  REWRITE_TAC[path_in] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subtopology euclideanreal (real_interval[&0,&1])`;
                 `subtopology euclidean (sphere(vec 0:real^2,&1))`;
                 `top:A topology`; `\t. cexp(ii * Cx(&2 * pi * t))`;
                 `g:real->A`] QUOTIENT_MAP_LIFT_EXISTS) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_QUOTIENT_MAP THEN
      REWRITE_TAC[CCS_CIRCLE_PATH; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; COMPACT_IN_EUCLIDEANREAL_INTERVAL;
               HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN];
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`&0`; `s:real`; `&0`; `t:real`] TOPC_DISK_MAP_FIBRES) THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO; COMPLEX_MUL_LID] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    MESON_TAC[]]);;

let CCS_CIRCLE_HOMOTOPIC_LOOPS = prove
 (`!top (G:real^2->A) G'.
        homotopic_with (\h. T)
          (subtopology euclidean (sphere(vec 0,&1)),top) G G'
        ==> homotopic_with (\r. r(&1) = r(&0))
              (subtopology euclideanreal (real_interval[&0,&1]),top)
              (\t. G(cexp(ii * Cx(&2 * pi * t))))
              (\t. G'(cexp(ii * Cx(&2 * pi * t))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\h:real^2->A. T`; `\r:real->A. r(&1) = r(&0)`;
                 `G:real^2->A`; `G':real^2->A`;
                 `\t. cexp(ii * Cx(&2 * pi * t))`;
                 `subtopology euclideanreal (real_interval[&0,&1])`;
                 `subtopology euclidean (sphere(vec 0:real^2,&1))`;
                 `top:A topology`] HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_RIGHT) THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[CCS_CIRCLE_PATH] THEN REWRITE_TAC[CCS_CEXP_2PI]);;

(* Loops in a Hausdorff space are homotopic, as loops, to loops missing the  *)
(* closed balls b(cball(0,r1)) of finitely many disjoint ball charts of     *)
(* dimension at least 3.                                                    *)

let CCS_LOOP_PUSH_OFF_BALLS = prove
 (`!top (g:real->A) (bs:(real^N->A)->bool) r r1.
        3 <= dimindex(:N) /\ hausdorff_space top /\
        path_in top g /\ g(&1) = g(&0) /\
        &0 < r1 /\ r1 < r /\ FINITE bs /\
        (!b. b IN bs
             ==> open_in top (IMAGE b (ball(vec 0,r))) /\
                 homeomorphic_map (subtopology euclidean (ball(vec 0,r)),
                                   subtopology top (IMAGE b (ball(vec 0,r)))) b) /\
        (!b b'. b IN bs /\ b' IN bs /\ ~(b = b')
                ==> DISJOINT (IMAGE b (ball(vec 0,r))) (IMAGE b' (ball(vec 0,r))))
        ==> ?g'. path_in top g' /\ g'(&1) = g'(&0) /\
                 (!t b. t IN real_interval[&0,&1] /\ b IN bs
                        ==> ~(g' t IN IMAGE b (cball(vec 0,r1)))) /\
                 homotopic_with (\r. r(&1) = r(&0))
                   (subtopology euclideanreal (real_interval[&0,&1]),top) g g'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `g:real->A`] CCS_LOOP_CIRCLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^2->A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`subtopology euclidean (sphere(vec 0:real^2,&1))`;
                 `top:A topology`; `G:real^2->A`; `\x:real^2. x`;
                 `bs:(real^N->A)->bool`; `r:real`; `r1:real`]
                CCS_PUSH_OFF_BALLS) THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[ARITH_RULE `3 <= n ==> 2 < n`; COMPACT_SPACE_SUBTOPOLOGY;
                 COMPACT_IN_EUCLIDEAN; COMPACT_SPHERE] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID];
    ALL_TAC] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(X_CHOOSE_THEN `G':real^2->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\t. (G':real^2->A)(cexp(ii * Cx(&2 * pi * t)))` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[path_in] THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (sphere(vec 0:real^2,&1))` THEN
    ASM_REWRITE_TAC[CCS_CIRCLE_PATH];
    REWRITE_TAC[CCS_CEXP_2PI];
    MAP_EVERY X_GEN_TAC [`t:real`; `b:real^N->A`] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM CCS_CIRCLE_PATH] THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`\t. (G:real^2->A)(cexp(ii * Cx(&2 * pi * t)))`;
      `\t. (G':real^2->A)(cexp(ii * Cx(&2 * pi * t)))`] THEN
    ASM_SIMP_TAC[CCS_CIRCLE_HOMOTOPIC_LOOPS; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
      MP_TAC(SPEC `&0` th) THEN MP_TAC(SPEC `&1` th)) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The abstract pinch argument.  If every loop of W is                       *)
(* homotopic in W to a loop in V, g maps V into a simply connected space M  *)
(* and P maps M back into W with P(g z) = z on V, then W is simply          *)
(* connected (when path connected).                                         *)
(* ------------------------------------------------------------------------- *)

let CCS_SC_FROM_PINCH = prove
 (`!(Z:B topology) W V (X:A topology) M g P.
        path_connected_space (subtopology Z W) /\ V SUBSET W /\
        simply_connected_space (subtopology X M) /\
        continuous_map (subtopology Z V,subtopology X M) g /\
        continuous_map (subtopology X M,subtopology Z W) P /\
        (!z. z IN V ==> P(g z) = z) /\
        (!h. path_in (subtopology Z W) h /\ h(&1) = h(&0)
             ==> ?h'. path_in (subtopology Z V) h' /\ h'(&1) = h'(&0) /\
                      homotopic_with (\r. r(&1) = r(&0))
                        (subtopology euclideanreal (real_interval[&0,&1]),
                         subtopology Z W) h h')
        ==> simply_connected_space (subtopology Z W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_LOOP_SOME] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real->B` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real->B`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h':real->B` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [SIMPLY_CONNECTED_SPACE_EQ_CONTRACTIBLE_LOOP_SOME] o
    check (fun th -> fst(dest_const(fst(strip_comb(concl th)))) =
                     "simply_connected_space")) THEN
  DISCH_THEN(MP_TAC o SPEC `(g:B->A) o (h':real->B)` o CONJUNCT2) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PATH_IN_COMPOSE THEN
      EXISTS_TAC `subtopology Z (V:B->bool)` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[o_THM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(P:A->B) a` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
      check (fun th -> free_in `P:A->B` (concl th) &&
                       fst(dest_const(fst(strip_comb(concl th)))) = "continuous_map")) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_TRANS THEN EXISTS_TAC `h':real->B` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\r:real->A. r(&1) = r(&0)`; `\r:real->B. r(&1) = r(&0)`;
                 `(g:B->A) o (h':real->B)`; `(\t:real. (a:A))`; `P:A->B`;
                 `subtopology euclideanreal (real_interval[&0,&1])`;
                 `subtopology X (M:A->bool)`; `subtopology Z (W:B->bool)`]
                HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_LEFT) THEN
  ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(P:A->B) o (g:B->A) o (h':real->B)`; `(P:A->B) o (\t:real. (a:A))`] THEN
  ASM_REWRITE_TAC[o_THM; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`subtopology Z (V:B->bool)`; `h':real->B`; `t:real`]
                  TOPC_PATH_IN_TOPSPACE) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN SIMP_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
      MP_TAC(SPEC `&0` th) THEN MP_TAC(SPEC `&1` th)) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[]]);;

