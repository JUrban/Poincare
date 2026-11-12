(* ========================================================================= *)
(* Unit pc_p2c_lcge (Part 2C, the general form G of local compactness): the  *)
(* embeddings of pc_p2c_cgemb for the general levels of pc_p2c_lcgb, with    *)
(* the exhaustion W of pc_p2c_lcgc.  The 35 cgemb lemmas whose statements    *)
(* mention its context are proved again here for the context p2ge_ctx; the   *)
(* definitions and the pure lemmas of cgemb are shared.  The cover of the    *)
(* closure of W j and the base point use the level-up lemma of lcgc; the     *)
(* main theorem P2GE_EMBED holds for given general levels, without           *)
(* completeness.  The contexts of cgemb are contexts here                    *)
(* (P2GE_CTX_OF_BALLS).                                                      *)
(* ========================================================================= *)

needs "src/pc_p2c_lcgc.ml";;
needs "src/pc_p2c_cgemb.ml";;

prioritize_real();;
type_invention_error := true;;

let p2ge_ctx = new_definition
 `p2ge_ctx (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
           (h:num->A->real^3^3) (x:num->A) (rho:num->real) (K:num->real)
           (N0:num->num) (B:num->num->real) (NB:num->num->num) (P:num->num)
           (Nn:num->num) (yc:num->num->num->A) (sq:num->num)
           (D:num#num->real^(3,3)finite_sum->real^1) (Gl:num->real^3->real^3^3)
           (kp:num->real^3->real^3) <=>
    p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
    p2cg_limit top atlas h yc rho sq D Gl /\
    p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp`;;

(* ------------------------------------------------------------------------- *)
(* The sequence and chart facts, the context facts, goodness of charts, the  *)
(* blending step (the cgemb lemmas on the normal charts, transitions, good   *)
(* maps and patched maps, for p2ge_ctx).                                     *)
(* ------------------------------------------------------------------------- *)

let P2GE_SEQ_MFD = prove
 (`!top atlas (h:num->A->real^3^3) x k.
     p2gb_seq top atlas h x
     ==> hausdorff_space (top k) /\ smooth_manifold_atlas (top k) (atlas k) /\
         riemannian_metric (atlas k) (h k)`,
  REWRITE_TAC[p2gb_seq] THEN MESON_TAC[]);;

let P2GE_NCH_PARAM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k
     ==> mfd_param (top k) (atlas k) (ball(vec 0,rho(NUMFST a)))
                   (p2cg_nch top atlas h yc k a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2GB_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2GE_SEQ_MFD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`;
                 `p2cg_frm (h:num->A->real^3^3) yc k a`; `(rho:num->real)(NUMFST a)`]
                GEON_NORMAL_PARAM) THEN
  ASM_REWRITE_TAC[P2CE_NCH_EQ] THEN SIMP_TAC[]);;

let P2GE_L_FACTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k
     ==> (!w. w IN ball(vec 0,rho(NUMFST a))
              ==> p2ce_L top atlas h yc rho k a (p2cg_nch top atlas h yc k a w) = w) /\
         (!p. p IN IMAGE (p2cg_nch top atlas h yc k a) (ball(vec 0,rho(NUMFST a)))
              ==> p2ce_L top atlas h yc rho k a p IN ball(vec 0,rho(NUMFST a)) /\
                  p2cg_nch top atlas h yc k a (p2ce_L top atlas h yc rho k a p) = p)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP P2GE_NCH_PARAM) THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2GE_SEQ_MFD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `p2cg_nch top atlas (h:num->A->real^3^3) yc k a`;
                 `ball(vec 0:real^3,rho(NUMFST a))`] GEON_PARAM_CHART_FACTS) THEN
  ASM_REWRITE_TAC[p2ce_L] THEN SIMP_TAC[]);;

let P2GE_G_RFS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k w.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k /\ w IN ball(vec 0,rho(NUMFST a))
     ==> p2cg_G top atlas h yc k a w =
         rfs_pullback (atlas k) (p2cg_nch top atlas h yc k a) (h k) w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2GB_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2GE_SEQ_MFD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `NUMFST a` o CONJUNCT1 o REWRITE_RULE[p2gb_levels]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`;
                 `p2cg_frm (h:num->A->real^3^3) yc k a`; `(rho:num->real)(NUMFST a)`;
                 `(K:num->real)(NUMFST a)`] P2CU_EXPMETRIC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^3` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[p2cg_G; rfs_pullback; P2CE_NCH_EQ]);;

let P2GE_T_NEAR = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl b c w0.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_limit top atlas h yc rho sq D Gl /\ w0 IN p2cg_om rho D b c
     ==> ?r N. &0 < r /\ ball(w0,r) SUBSET p2cg_om rho D b c /\
               (!n v. N <= n /\ v IN ball(w0,r)
                      ==> p2cg_T top atlas h yc rho (sq n) b c v IN
                          ball(vec 0,rho(NUMFST c) / &2) /\
                          p2cg_nch top atlas h yc (sq n) c
                            (p2cg_T top atlas h yc rho (sq n) b c v) =
                          p2cg_nch top atlas h yc (sq n) b v) /\
               p2ci_near w0 (\n. p2cg_T top atlas h yc rho (sq n) b c) (p2cg_tr rho D b c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:num`; `c:num`; `w0:real^3`] o
    check (fun th -> can (find_term ((=) `iterated_partial:(num)list->(real^3->real^3)->real^3->real^3`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rT:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tc")))) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `c:num`; `w0:real^3`]) P2GB_GOOD_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `nq:num` (X_CHOOSE_THEN `pq:num` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `q = p2cg_qv nq` THEN ABBREV_TAC `rq = inv(&2 pow pq)` THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `c:num`; `q:real^3`; `rq:real`;
                             `p2cg_nv N0 Nn b + p2cg_nv N0 Nn c`]) P2GB_GOOD_EVENTUALLY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `NG:num`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_good]) THEN
  SUBGOAL_THEN
   `!n:num. NG <= n
        ==> smooth_map_on (ball(q,&2 * rq))
              (p2cg_T (top:num->A topology) (atlas:num->((A->bool)#(A->real^3))->bool)
                      (h:num->A->real^3^3) (yc:num->num->num->A) rho (sq n) b c) /\
            (!v. v IN ball(q,&2 * rq)
                 ==> p2cg_T top atlas h yc rho (sq n) b c v IN
                     ball(vec 0,rho(NUMFST c) / &2) /\
                     p2cg_nch top atlas h yc (sq n) c
                       (p2cg_T top atlas h yc rho (sq n) b c v) =
                     p2cg_nch top atlas h yc (sq n) b v)`
  (LABEL_TAC "tg") THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (fun th -> can (find_term ((=) `NG:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`b:num`; `c:num`; `q:real^3`; `rq:real`; `(sq:num->num) n`])
                  P2GB_T_GOOD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `Ti:real^3->real^3` MP_TAC) STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!(f:real^3->real^3) s t x. IMAGE f s SUBSET t /\ x IN s ==> f x IN t`) THEN
    EXISTS_TAC `ball(q:real^3,&2 * rq)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < rq - dist(q:real^3,w0)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w0:real^3) IN ball(q,rq)` THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `r = min rT (rq - dist(q:real^3,w0))` THEN
  SUBGOAL_THEN `&0 < r /\ ball(w0:real^3,r) SUBSET ball(w0,rT) /\
                ball(w0:real^3,r) SUBSET ball(q,&2 * rq)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN
      MP_TAC(ISPECL [`q:real^3`; `w0:real^3`; `y:real^3`] DIST_TRIANGLE) THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `NG:num`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(w0:real^3,rT)` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`n:num`; `v:real^3`] THEN STRIP_TAC THEN
    USE_THEN "tg" (MP_TAC o C MP (ASSUME `NG:num <= n`) o SPEC `n:num`) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `(v:real^3) IN ball(w0,r)` THEN
    UNDISCH_TAC `ball(w0:real^3,r) SUBSET ball(q,&2 * rq)` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `r:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `NG:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(q:real^3,&2 * rq)` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "tg" (MP_TAC o C MP (ASSUME `NG:num <= n`) o SPEC `n:num`) THEN SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `p2cg_om rho D b c` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(w0:real^3,rT)` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)` THEN
      REWRITE_TAC[p2cl_system] THEN SIMP_TAC[]];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "tc" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
                   C MP (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:3)) l`) o SPEC `l:num list`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Kn:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN ball(w0,r)` THEN
    UNDISCH_TAC `ball(w0:real^3,r) SUBSET ball(w0,rT)` THEN SET_TAC[]]);;

let P2GE_CTX_FACTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
         p2cg_limit top atlas h yc rho sq D Gl /\
         p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) kp /\
         p2cg_dsys top atlas h yc rho sq D /\
         p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) /\
         (!n. n <= sq n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ge_ctx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONOTONE_BIGGER THEN
  UNDISCH_TAC `p2cg_dsys (top:num->A topology) atlas h yc rho sq D` THEN
  REWRITE_TAC[p2cg_dsys] THEN SIMP_TAC[]);;

let P2GE_GOOD_CHART = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp
    (Fs:num->real^3->A) b c w0 z0.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     p2ce_good top atlas h yc rho kp sq Fs b w0 /\
     w0 IN p2cg_dm rho b /\ z0 IN p2cg_dm rho c /\ kp b w0 = kp c z0
     ==> p2ce_good top atlas h yc rho kp sq Fs c z0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS)
    (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[p2ce_good] THEN
  DISCH_THEN(X_CHOOSE_THEN `rb:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `Nb:num` (LABEL_TAC "lb")) (LABEL_TAC "nb"))))) THEN
  (* gluing *)
  SUBGOAL_THEN `w0 IN p2cg_om rho D b c /\ p2cg_tr rho D b c w0 = z0 /\
                z0 IN p2cg_om rho D c b /\ p2cg_tr rho D c b z0 = w0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) (kp:num->real^3->real^3)` THEN
    REWRITE_TAC[p2cl_glue] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`b:num`; `c:num`; `w0:real^3`; `z0:real^3`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:num`; `b:num`; `z0:real^3`; `w0:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the transitions near w0 *)
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `b:num`; `c:num`; `w0:real^3`])
                P2GE_T_NEAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rT:real` (X_CHOOSE_THEN `NT:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "tf") (LABEL_TAC "tn")))))) THEN
  (* uniform closeness of R^b to the identity near w0 *)
  USE_THEN "nb" (MP_TAC o REWRITE_RULE[p2ci_near]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ru:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `rT / &2`)))))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nu:num` (LABEL_TAC "nu")) THEN
  (* a ball around z0 mapped by Tr c b close to w0 *)
  SUBGOAL_THEN `open(p2cg_om rho D c b) /\
                smooth_map_on (p2cg_om rho D c b) (p2cg_tr rho D c b)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)` THEN
    REWRITE_TAC[p2cl_system] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cg_tr rho D c b`; `p2cg_om rho D c b`; `z0:real^3`;
                 `min rb (min ru (rT / &2))`] P2CE_CONT_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dc")))) THEN
  SUBGOAL_THEN `p2cg_om rho D c b SUBSET p2cg_dm rho c /\
                (!z. z IN p2cg_om rho D c b
                     ==> p2cg_tr rho D c b z IN p2cg_om rho D b c /\
                         p2cg_tr rho D b c (p2cg_tr rho D c b z) = z) /\
                p2cg_om rho D b c SUBSET p2cg_dm rho b`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "tr") ASSUME_TAC)) THENL
   [UNDISCH_TAC `p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)` THEN
    REWRITE_TAC[p2cl_system] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the pointwise facts for large n *)
  SUBGOAL_THEN
   `!n z. Nb + Nu + NT + p2cg_nv N0 Nn b + p2cg_nv N0 Nn c <= n /\ z IN ball(z0,d)
          ==> (Fs:num->real^3->A) n (kp c z) =
              p2cg_nch top atlas h yc (sq n) c
                (p2cg_T top atlas h yc rho (sq n) b c
                   (p2ce_L top atlas h yc rho (sq n) b (Fs n (kp b (p2cg_tr rho D c b z))))) /\
              p2cg_T top atlas h yc rho (sq n) b c
                (p2ce_L top atlas h yc rho (sq n) b (Fs n (kp b (p2cg_tr rho D c b z))))
              IN ball(vec 0,rho(NUMFST c) / &2)`
  (LABEL_TAC "pt") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN p2cg_om rho D c b` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(z0,d)` THEN
      UNDISCH_TAC `ball(z0:real^3,d) SUBSET p2cg_om rho D c b` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2cg_tr rho D c b z IN p2cg_om rho D b c` ASSUME_TAC THENL
     [USE_THEN "tr" (MP_TAC o C MP (ASSUME `(z:real^3) IN p2cg_om rho D c b`) o
                     SPEC `z:real^3`) THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(p2cg_tr rho D c b z,w0) < min rb (min ru (rT / &2))` ASSUME_TAC THENL
     [USE_THEN "dc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(kp:num->real^3->real^3) c z = kp b (p2cg_tr rho D c b z)` SUBST1_TAC THENL
     [UNDISCH_TAC `p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D) (kp:num->real^3->real^3)` THEN
      REWRITE_TAC[p2cl_glue] THEN
      DISCH_THEN(MP_TAC o SPECL [`c:num`; `b:num`; `z:real^3`; `p2cg_tr rho D c b z`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`)
        THENL [EXISTS_TAC `p2cg_om rho D c b`; EXISTS_TAC `p2cg_om rho D b c`] THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2cg_tr rho D c b z IN ball(w0,rb) /\ p2cg_tr rho D c b z IN ball(w0,ru) /\
                  p2cg_tr rho D c b z IN ball(w0,rT / &2)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p2cg_nv N0 Nn b <= (sq:num->num) n /\ p2cg_nv N0 Nn c <= sq n`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `u = p2ce_L top atlas h yc rho ((sq:num->num) n) b
                      ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b
                         (p2cg_tr rho D c b z)))` THEN
    SUBGOAL_THEN `p2cg_nch top atlas h yc ((sq:num->num) n) b u =
                  (Fs:num->real^3->A) n ((kp:num->real^3->real^3) b (p2cg_tr rho D c b z))`
    ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN
      MP_TAC(ISPECL (p2cg_std @ [`b:num`; `(sq:num->num) n`]) P2GE_L_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `(Fs:num->real^3->A) n ((kp:num->real^3->real^3) b
                                  (p2cg_tr rho D c b z))` o CONJUNCT2) THEN
      ANTS_TAC THENL
       [USE_THEN "lb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^3) IN ball(w0,rT)` ASSUME_TAC THENL
     [USE_THEN "nu" (MP_TAC o SPECL [`n:num`; `p2cg_tr rho D c b z`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2cg_tr rho D c b z IN ball(w0,rT / &2)` THEN REWRITE_TAC[IN_BALL; dist] THEN
      MP_TAC(ISPECL [`w0 - u:real^3`; `w0 - p2cg_tr rho D c b z`] NORM_TRIANGLE_SUB) THEN
      MP_TAC(ISPECL [`u:real^3`; `p2cg_tr rho D c b z`] NORM_SUB) THEN
      REWRITE_TAC[VECTOR_ARITH `(w0 - u) - (w0 - v):real^3 = v - u`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "tf" (MP_TAC o SPECL [`n:num`; `u:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `p2cg_om rho D c b` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `Nb + Nu + NT + p2cg_nv N0 Nn b + p2cg_nv N0 Nn c` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `p2cg_T top atlas (h:num->A->real^3^3) yc rho (sq n) b c
                   (p2ce_L top atlas h yc rho (sq n) b
                      ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b
                        (p2cg_tr rho D c b z)))) IN ball(vec 0,rho(NUMFST c) / &2)` THEN
    REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMFST c`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the convergence: compose and identify *)
  SUBGOAL_THEN `p2ci_near z0 (\n:num. p2cg_tr rho D c b) (p2cg_tr rho D c b)` ASSUME_TAC THENL
   [MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `p2cg_om rho D c b` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z0:real^3`; `\n:num. p2cg_tr rho D c b`; `p2cg_tr rho D c b`;
                 `\n z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) b
                          ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b z))`;
                 `\z:real^3. z`] P2CI_NEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`z0:real^3`;
                 `\n:num. (\z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                                 (sq n) b ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b z))) o
                          p2cg_tr rho D c b`;
                 `(\z:real^3. z) o p2cg_tr rho D c b`;
                 `\n:num. p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) b c`;
                 `p2cg_tr rho D b c`] P2CI_NEAR_COMPOSE) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC P2CI_NEAR_EQ THEN
  EXISTS_TAC `\n:num. p2cg_T (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) b c o
                      ((\z. p2ce_L top atlas h yc rho (sq n) b
                              ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b z))) o
                       p2cg_tr rho D c b)` THEN
  EXISTS_TAC `p2cg_tr rho D b c o ((\z:real^3. z) o p2cg_tr rho D c b)` THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `Nb + Nu + NT + p2cg_nv N0 Nn b + p2cg_nv N0 Nn c`] THEN
  ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p2cg_nv N0 Nn c <= (sq:num->num) n` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL (p2cg_std @ [`c:num`; `(sq:num->num) n`]) P2GE_L_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `p2cg_T top atlas (h:num->A->real^3^3) yc rho (sq n) b c
                   (p2ce_L top atlas h yc rho (sq n) b
                      ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) b
                        (p2cg_tr rho D c b z)))) IN ball(vec 0,rho(NUMFST c) / &2)` THEN
    REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL (p2cg_std @ [`NUMFST c`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    USE_THEN "tr" (MP_TAC o SPEC `z:real^3`) THEN ANTS_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(z0,d)` THEN
      UNDISCH_TAC `ball(z0:real^3,d) SUBSET p2cg_om rho D c b` THEN SET_TAC[];
      SIMP_TAC[]]]);;

let P2GE_MU_FACTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc b.
     p2gb_levels top atlas h x rho K N0 B NB P Nn yc
     ==> smooth_map_on (:real^3) (\w. lift(p2ce_mu rho b w)) /\
         (!w. norm w <= rho(NUMFST b) / &7 ==> p2ce_mu rho b w = &1) /\
         (!w. rho(NUMFST b) / &6 <= norm w ==> p2ce_mu rho b w = &0) /\
         (!w. &0 <= p2ce_mu rho b w /\ p2ce_mu rho b w <= &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST b`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= rho(NUMFST b) / &7 /\ rho(NUMFST b) / &7 < rho(NUMFST b) / &6`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[p2ce_mu; SMOOTH_BUMP_SMOOTH; SMOOTH_BUMP_1; SMOOTH_BUMP_0;
               SMOOTH_BUMP_BOUNDS]);;

let P2GE_KP_FACTS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> (!i z. z IN p2cg_dm rho i ==> SND(p2cl_chart (p2cg_dm rho) kp i) (kp i z) = z) /\
         (!i z z'. z IN p2cg_dm rho i /\ z' IN p2cg_dm rho i /\ kp i z = kp i z'
                   ==> z = z')`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC P2CL_CHART_INV THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`;
                         `kp:num->real^3->real^3`; `i:num`; `z:real^3`; `z':real^3`]
                        P2CL_KP_INJ) THEN
    ASM_REWRITE_TAC[]]);;

let P2GE_F_SUC_CHART = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp cs k l z.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     z IN p2cg_dm rho (cs l)
     ==> p2ce_F top atlas h yc rho kp cs k (SUC l) (kp (cs l) z) =
         if norm z < rho(NUMFST(cs l)) / &6
         then p2cg_nch top atlas h yc k (cs l)
                ((&1 - p2ce_mu rho (cs l) z) %
                 p2ce_L top atlas h yc rho k (cs l)
                   (p2ce_F top atlas h yc rho kp cs k l (kp (cs l) z)) +
                 p2ce_mu rho (cs l) z % z)
         else p2ce_F top atlas h yc rho kp cs k l (kp (cs l) z)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP P2GE_KP_FACTS th) THEN
                       STRIP_ASSUME_TAC(MATCH_MP P2GE_CTX_FACTS th)) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST((cs:num->num) l)`]) P2GB_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(kp:num->real^3->real^3) (cs l) z IN
                IMAGE (kp (cs l)) (ball(vec 0,rho(NUMFST((cs:num->num) l)) / &6)) <=>
                norm z < rho(NUMFST(cs l)) / &6`
  ASSUME_TAC THENL
   [EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_BALL_0] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `z:real^3 = w` (fun th -> ASM_REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `(cs:num->num) l` THEN
      ASM_REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_BALL_0]];
    ALL_TAC] THEN
  REWRITE_TAC[P2CE_F_SUC] THEN ASM_SIMP_TAC[]);;

(* The blend step near a point of the chart where the previous map is good. *)

let P2GE_GOOD_BLEND = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp cs l w0.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     w0 IN p2cg_dm rho (cs l) /\
     p2ce_good top atlas h yc rho kp sq (\n. p2ce_F top atlas h yc rho kp cs (sq n) l)
               (cs l) w0
     ==> p2ce_good top atlas h yc rho kp sq
           (\n. p2ce_F top atlas h yc rho kp cs (sq n) (SUC l)) (cs l) w0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_KP_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`(cs:num->num) l`]) P2GE_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST((cs:num->num) l)`]) P2GB_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2ce_good] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `N1:num` (LABEL_TAC "ld")) (LABEL_TAC "nr"))))) THEN
  SUBGOAL_THEN
   `smooth_map_on (ball(w0:real^3,&1)) (\z. lift(p2ce_mu rho ((cs:num->num) l) z)) /\
    smooth_map_on (ball(w0:real^3,&1)) (\z. lift(&1 - p2ce_mu rho ((cs:num->num) l) z))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      DISCH_TAC THEN REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC SMOOTH_MAP_ON_SUB_OPEN THEN
      ASM_REWRITE_TAC[OPEN_BALL; SMOOTH_MAP_ON_CONST]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2ci_near w0
      (\n:num z. (&1 - p2ce_mu rho (cs l) z) %
             p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) (cs l)
               (p2ce_F top atlas h yc rho (kp:num->real^3->real^3) cs (sq n) l (kp (cs l) z)) +
             p2ce_mu rho (cs l) z % z)
      (\z:real^3. z)`
  (LABEL_TAC "nb") THENL
   [MP_TAC(ISPECL [`w0:real^3`;
                   `\n:num z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n)
                            (cs l) (p2ce_F top atlas h yc rho (kp:num->real^3->real^3) cs (sq n) l
                                      (kp (cs l) z))`;
                   `\z:real^3. z`; `\z. lift(&1 - p2ce_mu rho ((cs:num->num) l) z)`; `&1`]
                  P2CI_NEAR_SMUL) THEN
    ASM_REWRITE_TAC[REAL_LT_01; LIFT_DROP] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`w0:real^3`; `\n:num z:real^3. z`; `\z:real^3. z`;
                   `\z. lift(p2ce_mu rho ((cs:num->num) l) z)`; `&1`] P2CI_NEAR_SMUL) THEN
    ASM_REWRITE_TAC[REAL_LT_01; LIFT_DROP] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_ID];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`w0:real^3`;
                   `\n:num z. (&1 - p2ce_mu rho ((cs:num->num) l) z) %
                          p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n)
                            (cs l) (p2ce_F top atlas h yc rho (kp:num->real^3->real^3) cs (sq n) l
                                      (kp (cs l) z))`;
                   `\z:real^3. (&1 - p2ce_mu rho ((cs:num->num) l) z) % z`;
                   `\n:num z:real^3. p2ce_mu rho ((cs:num->num) l) z % z`;
                   `\z:real^3. p2ce_mu rho ((cs:num->num) l) z % z`] P2CI_NEAR_ADD) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_ARITH `(&1 - m) % z + m % z:real^3 = z`];
    ALL_TAC] THEN
  USE_THEN "nb" (MP_TAC o REWRITE_RULE[p2ci_near]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ru:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `rho(NUMFST((cs:num->num) l)) / &8`)))))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "nu")) THEN
  SUBGOAL_THEN
   `!n z. N1 + N2 + p2cg_nv N0 Nn ((cs:num->num) l) <= n /\ z IN ball(w0,min r ru)
          ==> p2ce_F top atlas h yc rho kp cs (sq n) (SUC l) (kp (cs l) z) =
              p2cg_nch top atlas h yc (sq n) (cs l)
                ((&1 - p2ce_mu rho (cs l) z) %
                 p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) (cs l)
                   (p2ce_F top atlas h yc rho (kp:num->real^3->real^3) cs (sq n) l
                      (kp (cs l) z)) +
                 p2ce_mu rho (cs l) z % z) /\
              (&1 - p2ce_mu rho (cs l) z) %
                 p2ce_L top atlas h yc rho (sq n) (cs l)
                   (p2ce_F top atlas h yc rho kp cs (sq n) l (kp (cs l) z)) +
              p2ce_mu rho (cs l) z % z IN ball(vec 0,rho(NUMFST(cs l)))`
  (LABEL_TAC "pt") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN ball(w0,r) /\ z IN ball(w0,ru)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(w0,min r ru)` THEN REWRITE_TAC[IN_BALL] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN p2cg_dm rho ((cs:num->num) l)` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN ball(w0,r)` THEN
      UNDISCH_TAC `ball(w0:real^3,r) SUBSET p2cg_dm rho ((cs:num->num) l)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `p2cg_nv N0 Nn ((cs:num->num) l) <= (sq:num->num) n` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL (p2ce_std @ [`cs:num->num`; `(sq:num->num) n`; `l:num`; `z:real^3`])
                    P2GE_F_SUC_CHART) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `p2ce_mu rho ((cs:num->num) l) z = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `&0`))
                        (rand(concl th)) && is_forall(concl th))) THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL (p2cg_std @ [`(cs:num->num) l`; `(sq:num->num) n`]) P2GE_L_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `p2ce_F top atlas (h:num->A->real^3^3) yc rho
                                  (kp:num->real^3->real^3) cs ((sq:num->num) n) l
                                  (kp (cs l) z)` o
                 CONJUNCT2) THEN
      ANTS_TAC THENL
       [USE_THEN "ld" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; SIMP_TAC[]];
      USE_THEN "nu" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IN_BALL_0] THEN
      MATCH_MP_TAC(NORM_ARITH `norm(z:real^3) < r / &4 /\ &0 < r
                               ==> norm(b - z) < r / &8 ==> norm b < r`) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN p2cg_dm rho ((cs:num->num) l)` THEN
      REWRITE_TAC[p2cg_dm; IN_BALL_0]];
    ALL_TAC] THEN
  EXISTS_TAC `min r ru` THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(w0:real^3,r)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    EXISTS_TAC `N1 + N2 + p2cg_nv N0 Nn ((cs:num->num) l)` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CI_NEAR_EQ THEN
    EXISTS_TAC
     `\n:num z. (&1 - p2ce_mu rho ((cs:num->num) l) z) %
            p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) (cs l)
              (p2ce_F top atlas h yc rho (kp:num->real^3->real^3) cs (sq n) l (kp (cs l) z)) +
            p2ce_mu rho (cs l) z % z` THEN
    EXISTS_TAC `\z:real^3. z` THEN
    MAP_EVERY EXISTS_TAC [`min r ru`; `N1 + N2 + p2cg_nv N0 Nn ((cs:num->num) l)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p2cg_nv N0 Nn ((cs:num->num) l) <= (sq:num->num) n` ASSUME_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL (p2cg_std @ [`(cs:num->num) l`; `(sq:num->num) n`]) P2GE_L_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]]);;

(* Where the cutoff is 1 the patched map is the normal chart map. *)

let P2GE_GOOD_RESET = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp cs l w0.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     norm w0 < rho(NUMFST(cs l)) / &7
     ==> p2ce_good top atlas h yc rho kp sq
           (\n. p2ce_F top atlas h yc rho kp cs (sq n) (SUC l)) (cs l) w0`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`(cs:num->num) l`]) P2GE_MU_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "mu1")
    (CONJUNCTS_THEN2 (LABEL_TAC "mu0") ASSUME_TAC))) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST((cs:num->num) l)`]) P2GB_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < rho(NUMFST((cs:num->num) l)) / &7 - norm(w0:real^3) /\
                !z:real^3. z IN ball(w0,rho(NUMFST(cs l)) / &7 - norm w0)
                           ==> norm z < rho(NUMFST(cs l)) / &7`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL; dist] THEN
    MP_TAC(ISPECL [`z:real^3`; `w0:real^3`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`z:real^3`; `w0:real^3`] NORM_SUB) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n z. p2cg_nv N0 Nn ((cs:num->num) l) <= n /\
          z IN ball(w0,rho(NUMFST(cs l)) / &7 - norm(w0:real^3))
          ==> p2ce_F top atlas h yc rho kp cs ((sq:num->num) n) (SUC l)
                ((kp:num->real^3->real^3) (cs l) z) =
              p2cg_nch (top:num->A topology) atlas (h:num->A->real^3^3) yc (sq n) (cs l) z /\
              z IN ball(vec 0,rho(NUMFST(cs l))) /\
              p2cg_nv N0 Nn (cs l) <= sq n`
  (LABEL_TAC "pt") THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST((cs:num->num) l)) / &7` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `&7`)) (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL (p2ce_std @ [`cs:num->num`; `(sq:num->num) n`; `l:num`; `z:real^3`])
                    P2GE_F_SUC_CHART) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST((cs:num->num) l)) / &6 /\
                    p2ce_mu rho (cs l) z = &1` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        USE_THEN "mu1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID];
      REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2ce_good] THEN
  EXISTS_TAC `rho(NUMFST((cs:num->num) l)) / &7 - norm(w0:real^3)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; p2cg_dm; IN_BALL_0] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x < r / &7 /\ &0 < r ==> x < r / &4`) THEN
    ASM_SIMP_TAC[];
    EXISTS_TAC `p2cg_nv N0 Nn ((cs:num->num) l)` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC P2CI_NEAR_EQ THEN
    MAP_EVERY EXISTS_TAC [`\n:num z:real^3. z`; `\z:real^3. z`;
                          `rho(NUMFST((cs:num->num) l)) / &7 - norm(w0:real^3)`;
                          `p2cg_nv N0 Nn ((cs:num->num) l)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC P2CI_NEAR_CONST THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_LT_01; SMOOTH_MAP_ON_ID];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "pt" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`(cs:num->num) l`; `(sq:num->num) n`]) P2GE_L_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[]]);;

(* Away from the closed patch kp b (cball(0,rho/6)) a step changes nothing. *)

let P2GE_FAR_BALL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp b c z0.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     z0 IN p2cg_dm rho c /\
     ~(kp c z0 IN IMAGE (kp b) (cball(vec 0,rho(NUMFST b) / &6)))
     ==> ?r. &0 < r /\
             !z. z IN ball(z0,r)
                 ==> ~(kp c z IN IMAGE (kp b) (cball(vec 0,rho(NUMFST b) / &6)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `Gl:num->real^3->real^3^3`; `kp:num->real^3->real^3`])
                P2GC_MANIFOLD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(b:num)`]) P2GB_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE ((kp:num->real^3->real^3) b) (cball(vec 0,rho(NUMFST(b:num)) / &6))` THEN
  SUBGOAL_THEN `closed_in (p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)) S` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN
    MATCH_MP_TAC IMAGE_COMPACT_IN THEN
    EXISTS_TAC `subtopology euclidean (p2cg_dm rho (b:num))` THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
      REWRITE_TAC[SUBSET; p2cg_dm; IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC P2CC_KP_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open {z | z IN p2cg_dm rho c /\
              (kp:num->real^3->real^3) c z IN
              topspace(p2cl_top (p2cg_dm rho) kp) DIFF S}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `p2cg_dm rho c` THEN
    REWRITE_TAC[p2cg_dm; OPEN_BALL] THEN
    MP_TAC(ISPECL [`(kp:num->real^3->real^3) c`;
                   `subtopology euclidean (p2cg_dm rho c)`;
                   `p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)) DIFF S`]
                  OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; p2cg_dm] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM p2cg_dm] THEN MATCH_MP_TAC P2CC_KP_CONTINUOUS THEN
      MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z0:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV] THEN
    EXISTS_TAC `c:num` THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  UNDISCH_TAC `ball(z0:real^3,r) SUBSET
               {z | z IN p2cg_dm rho c /\
                    (kp:num->real^3->real^3) c z IN
                    topspace(p2cl_top (p2cg_dm rho) kp) DIFF S}` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN ASM_MESON_TAC[]);;

let P2GE_GOOD_FAR = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp cs l c z0.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     z0 IN p2cg_dm rho c /\
     ~(kp c z0 IN IMAGE (kp (cs l)) (cball(vec 0,rho(NUMFST(cs l)) / &6))) /\
     p2ce_good top atlas h yc rho kp sq (\n. p2ce_F top atlas h yc rho kp cs (sq n) l) c z0
     ==> p2ce_good top atlas h yc rho kp sq
           (\n. p2ce_F top atlas h yc rho kp cs (sq n) (SUC l)) c z0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  MATCH_MP_TAC P2CE_GOOD_EQ THEN
  EXISTS_TAC `\n. p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                         (kp:num->real^3->real^3) cs ((sq:num->num) n) l` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL (p2ce_std @ [`(cs:num->num) l`; `c:num`; `z0:real^3`]) P2GE_FAR_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `0`] THEN ASM_REWRITE_TAC[LE_0] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN DISCH_TAC THEN
  REWRITE_TAC[P2CE_F_SUC] THEN
  SUBGOAL_THEN `~((kp:num->real^3->real^3) c z IN
                  IMAGE (kp ((cs:num->num) l)) (ball(vec 0,rho(NUMFST(cs l)) / &6)))`
  (fun th -> REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC(SET_RULE `!f:real^3->real^3 s t. s SUBSET t ==> x IN IMAGE f s ==> x IN IMAGE f t`) THEN
  REWRITE_TAC[BALL_SUBSET_CBALL]);;

(* ------------------------------------------------------------------------- *)
(* The invariant of the construction, the chart list at level j + 2 and the  *)
(* cover of the closure of W j, the base point (as in the induction over the *)
(* patches of cgemb; the cover and the base point use pc_p2c_lcgc).          *)
(* ------------------------------------------------------------------------- *)

let P2GE_INV = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp cs.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> !l c z0. z0 IN p2cg_dm rho c /\ kp c z0 IN p2ce_om rho kp cs l
                  ==> p2ce_good top atlas h yc rho kp sq
                        (\n. p2ce_F top atlas h yc rho kp cs (sq n) l) c z0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_KP_FACTS) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[p2ce_om; IN_UNIONS; IN_ELIM_THM; LT]; ALL_TAC] THEN
  POP_ASSUM(LABEL_TAC "ih") THEN MAP_EVERY X_GEN_TAC [`c:num`; `z0:real^3`] THEN
  REWRITE_TAC[P2CE_OM_SUC; IN_UNION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "or")) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST((cs:num->num) l)`]) P2GB_RHO_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(kp:num->real^3->real^3) c z0 IN
                 IMAGE (kp ((cs:num->num) l)) (cball(vec 0,rho(NUMFST(cs l)) / &6))` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) THEN
    SUBGOAL_THEN `(w0:real^3) IN p2cg_dm rho ((cs:num->num) l)` ASSUME_TAC THENL
     [UNDISCH_TAC `(w0:real^3) IN cball(vec 0,rho(NUMFST((cs:num->num) l)) / &6)` THEN
      REWRITE_TAC[p2cg_dm; IN_CBALL_0; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL (p2ce_std @ [`\n. p2ce_F (top:num->A topology) atlas
                                          (h:num->A->real^3^3) yc rho
                                          (kp:num->real^3->real^3) cs ((sq:num->num) n) (SUC l)`;
                                     `(cs:num->num) l`; `c:num`; `w0:real^3`; `z0:real^3`])
                        P2GE_GOOD_CHART) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(kp:num->real^3->real^3) c z0 IN p2ce_om rho kp cs l` THENL
     [MATCH_MP_TAC(ISPECL (p2ce_std @ [`cs:num->num`; `l:num`; `w0:real^3`])
                          P2GE_GOOD_BLEND) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(kp:num->real^3->real^3) c z0 IN p2ce_om rho kp cs l` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(kp:num->real^3->real^3) c z0 IN
                  IMAGE (kp ((cs:num->num) l)) (ball(vec 0,rho(NUMFST(cs l)) / &7))`
    MP_TAC THENL
     [REMOVE_THEN "or" MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(ISPECL (p2ce_std @ [`cs:num->num`; `l:num`; `w0:real^3`])
                          P2GE_GOOD_RESET) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `w0:real^3 = w1` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `z':real^3`))
                                                     (concl th))) THEN
      EXISTS_TAC `(cs:num->num) l` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(w1:real^3) IN ball(vec 0,rho(NUMFST((cs:num->num) l)) / &7)` THEN
        REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
        ASM_MESON_TAC[]];
      UNDISCH_TAC `(w1:real^3) IN ball(vec 0,rho(NUMFST((cs:num->num) l)) / &7)` THEN
      REWRITE_TAC[IN_BALL_0]];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL (p2ce_std @ [`cs:num->num`; `l:num`; `c:num`; `z0:real^3`])
                          P2GE_GOOD_FAR) THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "or" MP_TAC THEN
  MATCH_MP_TAC(TAUT `~b ==> (a \/ b ==> a)`) THEN
  UNDISCH_TAC `~((kp:num->real^3->real^3) c z0 IN
                 IMAGE (kp ((cs:num->num) l)) (cball(vec 0,rho(NUMFST(cs l)) / &6)))` THEN
  REWRITE_TAC[IN_IMAGE; IN_BALL_0; IN_CBALL_0; NOT_EXISTS_THM; CONTRAPOS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* The chart list at level j + 2 and the covering of the closure of W j. *)

let P2GE_COVER = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp j SUBSET
         p2ce_om rho kp (p2ce_cs P j) (P(j + 2))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GC_COVER_PIECES) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `(t:real^3->bool) SUBSET u ==> s SUBSET t ==> s SUBSET u`) THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[p2ce_om] THEN
  MATCH_MP_TAC(SET_RULE `!t:real^3->bool. s SUBSET t /\ t IN u ==> s SUBSET UNIONS u`) THEN
  EXISTS_TAC `IMAGE ((kp:num->real^3->real^3) (p2ce_cs P j (P(j + 2) - 1 - i)))
                    (ball(vec 0,rho(NUMFST(p2ce_cs P j (P(j + 2) - 1 - i))) / &7))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `p2ce_cs P j (P(j + 2) - 1 - i) = NUMPAIR (j + 2) i` SUBST1_TAC THENL
     [REWRITE_TAC[p2ce_cs] THEN AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[NUMPAIR_DEST] THEN
    MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `P(j + 2) - 1 - i` THEN
    REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* The base point. *)

let P2GE_XL_CHART = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp J.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> kp (NUMPAIR J 0) (vec 0) = p2cc_xl kp`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ge_ctx] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`J:num`]) P2GC_XL_CHART) THEN ASM_REWRITE_TAC[]);;

let P2GE_BASE = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> 0 < P(j + 2) /\
         ?N. !n. N <= n
                 ==> p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                            (p2cc_xl kp) = x(sq n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`0`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `0 < P(j + 2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`j + 1`]) P2GC_P_POS) THEN
    ASM_REWRITE_TAC[ARITH_RULE `SUC(j + 1) = j + 2`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `P(j + 2) = SUC(P(j + 2) - 1) /\
                p2ce_cs P j (P(j + 2) - 1) = NUMPAIR (j + 2) 0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[p2ce_cs] THEN CONJ_TAC THENL [ASM_ARITH_TAC; AP_TERM_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `p2cg_nv N0 Nn (NUMPAIR (j + 2) 0) + Nn(j + 2)` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `p2cg_nv N0 Nn (NUMPAIR (j + 2) 0) <= (sq:num->num) n /\ Nn(j + 2) <= sq n`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) o
    check (fun th -> is_eq(concl th) && lhs(concl th) = `(P:num->num)(j + 2)`)) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j + 2`]) P2GE_XL_CHART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(kp:num->real^3->real^3) (NUMPAIR (j + 2) 0) (vec 0) =
                kp (p2ce_cs P j (P(j + 2) - 1)) (vec 0)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL (p2ce_std @ [`p2ce_cs P j`; `(sq:num->num) n`; `P(j + 2) - 1`;
                             `vec 0:real^3`]) P2GE_F_SUC_CHART) THEN
  ASM_REWRITE_TAC[p2cg_dm; CENTRE_IN_BALL; NORM_0; NUMPAIR_DEST] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR (j + 2) 0`]) P2GE_MU_FACTS) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^3` o CONJUNCT1 o CONJUNCT2) THEN
  REWRITE_TAC[NORM_0] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMPAIR (j + 2) 0`; `(sq:num->num) n`]) P2GB_NCH_BASIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  REWRITE_TAC[p2cg_ctr; NUMPAIR_DEST] THEN
  UNDISCH_TAC `p2gb_levels top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc` THEN
  REWRITE_TAC[p2gb_levels] THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The metric fields, the transfer of lck_dist2 and its uniformity on the    *)
(* closure of W j (as for the pulled-back metrics of cgemb).                 *)
(* ------------------------------------------------------------------------- *)

let P2GE_G_FIELD = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc a k.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc /\
     p2cg_nv N0 Nn a <= k
     ==> metric_field (ball(vec 0,rho(NUMFST a))) (p2cg_G top atlas h yc k a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2GB_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                 `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2GE_SEQ_MFD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `NUMFST a` o CONJUNCT1 o REWRITE_RULE[p2gb_levels]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `(h:num->A->real^3^3) k`; `p2cg_ctr (yc:num->num->num->A) k a`;
                 `p2cg_frm (h:num->A->real^3^3) yc k a`; `(rho:num->real)(NUMFST a)`;
                 `(K:num->real)(NUMFST a)`] P2CU_EXPMETRIC_FACTS) THEN
  ASM_REWRITE_TAC[p2cg_G] THEN SIMP_TAC[]);;

(* The transfer lemma. *)

let P2GE_LCK_TRANSFER = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp
    k (Fm:real^3->A) (R:real^3->real^3) R' c z s m.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     p2cg_nv N0 Nn c <= k /\ &0 < s /\ ball(z,s) SUBSET p2cg_dm rho c /\
     diffeomorphism_on (ball(z,s)) (IMAGE R (ball(z,s))) R R' /\
     IMAGE R (ball(z,s)) SUBSET ball(vec 0,rho(NUMFST c)) /\
     (!w. w IN ball(z,s) ==> Fm(kp c w) = p2cg_nch top atlas h yc k c (R w))
     ==> lck_dist2 m
           (metric_local (p2cl_atlas (p2cg_dm rho) kp)
              (chart_at (p2cl_atlas (p2cg_dm rho) kp) (kp c z))
              (p2cl_metric (p2cg_dm rho) kp Gl))
           (\w. rfs_pullback (atlas k)
                  (Fm o chart_inv (chart_at (p2cl_atlas (p2cg_dm rho) kp) (kp c z)))
                  (h k) w)
           (SND(chart_at (p2cl_atlas (p2cg_dm rho) kp) (kp c z)) (kp c z)) =
         lck_dist2 m (Gl c) (mpullback R (p2cg_G top atlas h yc k c)) z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  SUBGOAL_THEN `(z:real^3) IN p2cg_dm rho c` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(z:real^3,s) SUBSET p2cg_dm rho c` THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> s SUBSET t ==> x IN t`) THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`; `kp:num->real^3->real^3`;
                 `c:num`; `z:real^3`] P2CL_CHART_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `open(p2cg_om rho D c i) /\
                p2cg_om rho D i c SUBSET p2cg_dm rho i /\
                (!v. v IN p2cg_om rho D i c
                     ==> p2cg_tr rho D i c v IN p2cg_om rho D c i) /\
                smooth_map_on (p2cg_om rho D i c) (p2cg_tr rho D i c) /\
                p2cg_tr rho D i c (p2cg_tr rho D c i z) = z`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)` THEN
    REWRITE_TAC[p2cl_system] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `U = ball(z:real^3,s) INTER p2cg_om rho D c i` THEN
  SUBGOAL_THEN `open (U:real^3->bool) /\ (z:real^3) IN U /\ U SUBSET p2cg_om rho D c i /\
                U SUBSET ball(z,s)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL; INTER_SUBSET; IN_INTER;
                                     CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`; `c:num`; `i:num`;
                 `U:real^3->bool`] P2CE_TR_DIFFEO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (p2cg_tr rho D i c) (IMAGE (p2cg_tr rho D c i) U) = U /\
                smooth_map_on (ball(z:real^3,s)) (R:real^3->real^3) /\
                open (IMAGE (R:real^3->real^3) (ball(z,s)))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `diffeomorphism_on (IMAGE (p2cg_tr rho D c i) U) U (p2cg_tr rho D i c)
                                   (p2cg_tr rho D c i)` THEN
    UNDISCH_TAC `diffeomorphism_on (ball(z:real^3,s)) (IMAGE (R:real^3->real^3) (ball(z,s))) R (R':real^3->real^3)` THEN
    SIMP_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  SUBGOAL_THEN `metric_field U ((Gl:num->real^3->real^3^3) c) /\
                metric_field U (mpullback (R:real^3->real^3)
                                 (p2cg_G top atlas (h:num->A->real^3^3) yc k c))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,&3 * rho(NUMFST(c:num)) / &8)` THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:real^3,s)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `p2cg_dm rho c` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[p2cg_dm] THEN MATCH_MP_TAC SUBSET_BALL THEN
      MP_TAC(ISPECL (p2cg_std @ [`NUMFST(c:num)`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC METRIC_FIELD_SUBSET THEN EXISTS_TAC `ball(z:real^3,s)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_PULLBACK THEN
      MAP_EVERY EXISTS_TAC [`IMAGE (R:real^3->real^3) (ball(z,s))`; `R':real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC METRIC_FIELD_SUBSET THEN
      EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST(c:num)))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC P2GE_G_FIELD THEN EXISTS_TAC `x:num->A` THEN
      MAP_EVERY EXISTS_TAC [`K:num->real`; `N0:num->num`; `B:num->num->real`;
                            `NB:num->num->num`; `P:num->num`; `Nn:num->num`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `lck_dist2 m (mpullback (p2cg_tr rho D i c) ((Gl:num->real^3->real^3^3) c))
                (mpullback (p2cg_tr rho D i c)
                   (mpullback (R:real^3->real^3)
                      (p2cg_G top atlas (h:num->A->real^3^3) yc k c)))
                (p2cg_tr rho D c i z)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`m:num`; `U:real^3->bool`; `IMAGE (p2cg_tr rho D c i) U`;
                   `p2cg_tr rho D i c`; `p2cg_tr rho D c i`; `(Gl:num->real^3->real^3^3) c`;
                   `mpullback (R:real^3->real^3) (p2cg_G top atlas (h:num->A->real^3^3) yc k c)`;
                   `p2cg_tr rho D c i z`] LCK_DIST2_PULLBACK) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; SIMP_TAC[]]] THEN
  MATCH_MP_TAC LCK_DIST2_LOCAL THEN EXISTS_TAC `IMAGE (p2cg_tr rho D c i) U` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^3) IN p2cg_om rho D i c /\ v IN p2cg_dm rho i /\
                p2cg_tr rho D i c v IN U` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[];
      UNDISCH_TAC `(v:real^3) IN IMAGE (p2cg_tr rho D c i) U` THEN
      UNDISCH_TAC `IMAGE (p2cg_tr rho D i c) (IMAGE (p2cg_tr rho D c i) U) = U` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`; `kp:num->real^3->real^3`;
                   `Gl:num->real^3->real^3^3`; `i:num`; `v:real^3`] P2CL_METRIC_LOCAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `c:num`; `v:real^3`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `Gl:num->real^3->real^3^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the pulled-back metric through the chart i *)
  ABBREV_TAC `Tq = p2cg_tr rho D i c` THEN
  SUBGOAL_THEN `(Tq:real^3->real^3) differentiable at v /\
                (R:real^3->real^3) differentiable at (Tq v) /\
                (R o Tq) v IN ball(vec 0:real^3,rho(NUMFST(c:num)))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `p2cg_om rho D i c` THEN
      EXPAND_TAC "Tq" THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2cl_system (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)` THEN
      REWRITE_TAC[p2cl_system] THEN SIMP_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `ball(z:real^3,s)` THEN
      ASM_REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
      REWRITE_TAC[o_THM] THEN
      UNDISCH_TAC `IMAGE (R:real^3->real^3) (ball(z,s)) SUBSET ball(vec 0,rho(NUMFST(c:num)))` THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> IMAGE (f:real^3->real^3) s SUBSET t ==> f x IN t`) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`atlas (k:num):((A->bool)#(A->real^3))->bool`;
                 `(Fm:real^3->A) o chart_inv (p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) i)`;
                 `p2cg_nch top atlas (h:num->A->real^3^3) yc k c o ((R:real^3->real^3) o (Tq:real^3->real^3))`;
                 `(h:num->A->real^3^3) k`; `IMAGE (p2cg_tr rho D c i) U`; `v:real^3`]
                P2CE_RFS_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v':real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v':real^3) IN p2cg_om rho D i c /\ v' IN p2cg_dm rho i /\
                  (Tq:real^3->real^3) v' IN U` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM SET_TAC[]; ASM SET_TAC[];
        UNDISCH_TAC `(v':real^3) IN IMAGE (p2cg_tr rho D c i) U` THEN
        UNDISCH_TAC `IMAGE (Tq:real^3->real^3) (IMAGE (p2cg_tr rho D c i) U) = U` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    MP_TAC(ISPECL [`p2cg_dm rho`; `p2cg_om rho D`; `p2cg_tr rho D`; `kp:num->real^3->real^3`;
                   `i:num`; `v':real^3`] P2CL_CHART_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(kp:num->real^3->real^3) i v' = kp c (Tq v')` SUBST1_TAC THENL
     [UNDISCH_TAC `p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)
                             (kp:num->real^3->real^3)` THEN
      REWRITE_TAC[p2cl_glue] THEN
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `c:num`; `v':real^3`; `(Tq:real^3->real^3) v'`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "Tq" THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`(top:num->A topology) k`; `(atlas:num->((A->bool)#(A->real^3))->bool) k`;
                 `ball(vec 0:real^3,rho(NUMFST(c:num)))`;
                 `p2cg_nch top atlas (h:num->A->real^3^3) yc k c`; `(R:real^3->real^3) o (Tq:real^3->real^3)`;
                 `(h:num->A->real^3^3) k`; `v:real^3`] P2CE_RFS_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2GE_SEQ_MFD) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC(ISPECL (p2cg_std @ [`c:num`; `k:num`]) P2GE_NCH_PARAM) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_AT THEN ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `mpullback ((R:real^3->real^3) o (Tq:real^3->real^3)) (p2cg_G top atlas (h:num->A->real^3^3) yc k c) v` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC P2CG_MPULLBACK_PT THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ISPECL (p2cg_std @ [`c:num`; `k:num`;
                                     `((R:real^3->real^3) o (Tq:real^3->real^3)) v`])
                        P2GE_G_RFS) THEN
    ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC P2CE_MPULLBACK_CHAIN THEN ASM_REWRITE_TAC[]]);;

(* The local estimate near a point where the maps are good. *)

let P2GE_GLIMIT_NEAR = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp c z0.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ z0 IN p2cg_dm rho c
     ==> p2ci_near z0
           (\n. (vectorize:real^3^3->real^(3,3)finite_prod) o
                p2cg_G top atlas h yc (sq n) c)
           (vectorize o Gl c)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:num` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `p2cg_G:(num->A topology)->(num->((A->bool)#(A->real^3))->bool)->(num->A->real^3^3)->(num->num->num->A)->num->num->real^3->real^3^3`)) (concl th))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pc"))) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(c:num)`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `ball(z0:real^3,rho(NUMFST(c:num)) / &8) SUBSET
                ball(vec 0,&3 * rho(NUMFST c) / &8) /\
                ball(z0:real^3,rho(NUMFST(c:num)) / &8) SUBSET ball(vec 0,rho(NUMFST c))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z0:real^3) IN p2cg_dm rho c` THEN
    REWRITE_TAC[p2cg_dm; SUBSET; IN_BALL_0; IN_BALL] THEN DISCH_TAC THEN
    CONJ_TAC THEN X_GEN_TAC `w:real^3` THEN
    MP_TAC(ISPECL [`z0:real^3`; `w:real^3`] DIST_TRIANGLE_LE) THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `z0:real^3`; `w:real^3`] DIST_TRIANGLE) THEN
    REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC P2CI_NEAR_OF_PARTIALS THEN EXISTS_TAC `rho(NUMFST(c:num)) / &8` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    EXISTS_TAC `p2cg_nv N0 Nn c` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,rho(NUMFST(c:num)))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`c:num`; `(sq:num->num) n`]) P2GE_G_FIELD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[];
      SIMP_TAC[metric_field]];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^3,&3 * rho(NUMFST(c:num)) / &8)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `metric_field (ball(vec 0:real^3,&3 * rho(NUMFST(c:num)) / &8))
                              ((Gl:num->real^3->real^3^3) c)` THEN
    SIMP_TAC[metric_field];
    X_GEN_TAC `l:num list` THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "pc" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real` o
                   C MP (ASSUME `ALL (\j. 1 <= j /\ j <= dimindex(:3)) l`) o SPEC `l:num list`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Kn:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let P2GE_LOCAL_LCK = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp
    (Fs:num->real^3->A) c z0 m eta.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     z0 IN p2cg_dm rho c /\ p2ce_good top atlas h yc rho kp sq Fs c z0 /\ &0 < eta
     ==> ?r N. &0 < r /\
               !n z. N <= n /\ z IN ball(z0,r)
                     ==> lck_dist2 m
                           (metric_local (p2cl_atlas (p2cg_dm rho) kp)
                              (chart_at (p2cl_atlas (p2cg_dm rho) kp) (kp c z))
                              (p2cl_metric (p2cg_dm rho) kp Gl))
                           (\w. rfs_pullback (atlas (sq n))
                                  (Fs n o chart_inv (chart_at (p2cl_atlas (p2cg_dm rho) kp)
                                                              (kp c z)))
                                  (h (sq n)) w)
                           (SND(chart_at (p2cl_atlas (p2cg_dm rho) kp) (kp c z)) (kp c z)) <
                         eta`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2cg_limit]) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(c:num)`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[p2ce_good] THEN
  DISCH_THEN(X_CHOOSE_THEN `rg:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `Ng:num` (LABEL_TAC "lg")) (LABEL_TAC "ng"))))) THEN
  USE_THEN "ng" (MP_TAC o MATCH_MP P2CE_NEAR_ID_DIFFEO) THEN
  DISCH_THEN(X_CHOOSE_THEN `rd:real` (X_CHOOSE_THEN `Nd:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd")))) THEN
  USE_THEN "ng" (MP_TAC o REWRITE_RULE[p2ci_near]) THEN
  DISCH_THEN(X_CHOOSE_THEN `ru:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `rho(NUMFST(c:num)) / &8`)))))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nu:num` (LABEL_TAC "nu")) THEN
  (* the lck estimate in the chart c *)
  MP_TAC(ISPECL [`ball(vec 0:real^3,&3 * rho(NUMFST(c:num)) / &8)`;
                 `(Gl:num->real^3->real^3^3) c`;
                 `\n:num. mpullback (\z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3)
                                           yc rho (sq n) c ((Fs:num->real^3->A) n
                                           ((kp:num->real^3->real^3) c z)))
                                    (p2cg_G top atlas h yc (sq n) c)`;
                 `z0:real^3`; `m:num`] P2CI_LCK_NEAR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      UNDISCH_TAC `(z0:real^3) IN p2cg_dm rho c` THEN REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL [`z0:real^3`;
                     `\n z. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho (sq n) c
                              ((Fs:num->real^3->A) n ((kp:num->real^3->real^3) c z))`;
                     `\z:real^3. z`;
                     `\n:num. p2cg_G (top:num->A topology) atlas (h:num->A->real^3^3) yc (sq n) c`;
                     `(Gl:num->real^3->real^3^3) c`] P2CI_NEAR_MPULLBACK) THEN
      REWRITE_TAC[P2CE_MPULLBACK_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPECL (p2ce_std @ [`c:num`; `z0:real^3`]) P2GE_GLIMIT_NEAR) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[p2ci_near] THEN
  DISCH_THEN(X_CHOOSE_THEN `rl:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `eta:real`)))))) THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO; NORM_LIFT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nl:num` (LABEL_TAC "nl")) THEN
  EXISTS_TAC `min rg (min rd (min ru rl)) / &2` THEN
  EXISTS_TAC `Ng + Nd + Nu + Nl + p2cg_nv N0 Nn c` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
  ABBREV_TAC `r = min rg (min rd (min ru rl)) / &2` THEN
  SUBGOAL_THEN `ball(z:real^3,r) SUBSET ball(z0,rg) /\ ball(z:real^3,r) SUBSET ball(z0,rd) /\
                ball(z:real^3,r) SUBSET ball(z0,ru) /\ (z:real^3) IN ball(z0,rl) /\ &0 < r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN ball(z0,r)` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `w:real^3` THEN DISCH_TAC) THEN
    TRY(MP_TAC(ISPECL [`z0:real^3`; `z:real^3`; `w:real^3`] DIST_TRIANGLE)) THEN
    EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `p2cg_nv N0 Nn c <= (sq:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "dd" (MP_TAC o SPECL [`n:num`; `ball(z:real^3,r)`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_BALL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `Ri:real^3->real^3`) THEN
  MP_TAC(ISPECL (p2ce_std @ [`(sq:num->num) n`; `(Fs:num->real^3->A) n`;
                             `\w. p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                                    (sq n) c ((Fs:num->real^3->A) n
                                    ((kp:num->real^3->real^3) c w))`;
                             `Ri:real^3->real^3`; `c:num`; `z:real^3`; `r:real`; `m:num`])
                P2GE_LCK_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^3,rg)` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN X_GEN_TAC `w:real^3` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(w:real^3) IN ball(z0,ru) /\ w IN p2cg_dm rho c` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      USE_THEN "nu" (MP_TAC o SPECL [`n:num`; `w:real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(w:real^3) IN p2cg_dm rho c` THEN REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN
      MP_TAC(ISPECL [`p2ce_L (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                        ((sq:num->num) n) c ((Fs:num->real^3->A) n
                        ((kp:num->real^3->real^3) c w))`; `w:real^3`] NORM_TRIANGLE_SUB) THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL (p2cg_std @ [`c:num`; `(sq:num->num) n`]) P2GE_L_FACTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `(Fs:num->real^3->A) n ((kp:num->real^3->real^3) c w)` o
                 CONJUNCT2) THEN
      ANTS_TAC THENL
       [USE_THEN "lg" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
        SIMP_TAC[]]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
  USE_THEN "nl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Uniformity on the compact closure of W j. *)

let P2GE_LCK_UNIFORM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j m eta.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ &0 < eta
     ==> ?N. !n y. N <= n /\
                   y IN p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp j
                   ==> lck_dist2 m
                         (metric_local (p2cl_atlas (p2cg_dm rho) kp)
                            (chart_at (p2cl_atlas (p2cg_dm rho) kp) y)
                            (p2cl_metric (p2cg_dm rho) kp Gl))
                         (\w. rfs_pullback (atlas (sq n))
                                (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)) o
                                 chart_inv (chart_at (p2cl_atlas (p2cg_dm rho) kp) y))
                                (h (sq n)) w)
                         (SND(chart_at (p2cl_atlas (p2cg_dm rho) kp) y) y) < eta`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2GC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL p2ce_std P2GC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC P2CE_COMPACT_EVENTUALLY THEN
  EXISTS_TAC `p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y0:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y0:real^3) IN topspace(p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3))`
  MP_TAC THENL
   [UNDISCH_TAC `(y0:real^3) IN p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp j` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^3) IN s ==> x IN t`) THEN
    REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL (p2ce_std @ [`\n. p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3)
                                     yc rho (kp:num->real^3->real^3) (p2ce_cs P j)
                                     ((sq:num->num) n) (P(j + 2))`;
                             `c:num`; `z0:real^3`; `m:num`; `eta:real`]) P2GE_LOCAL_LCK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2ce_std @ [`p2ce_cs P j`]) P2GE_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_COVER) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y0:real^3) IN p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp j` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `IMAGE ((kp:num->real^3->real^3) c) (ball(z0,min r (rho(NUMFST c) / &4 - norm(z0:real^3))))` THEN
  EXISTS_TAC `N:num` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC P2CL_OPEN_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
    UNDISCH_TAC `(z0:real^3) IN p2cg_dm rho c` THEN
    REWRITE_TAC[p2cg_dm; SUBSET; IN_BALL; IN_BALL_0] THEN DISCH_TAC THEN
    X_GEN_TAC `w:real^3` THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `z0:real^3`; `w:real^3`] DIST_TRIANGLE) THEN
    REWRITE_TAC[DIST_0] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[CENTRE_IN_BALL] THEN
    UNDISCH_TAC `(z0:real^3) IN p2cg_dm rho c` THEN REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN ball(z0,min r (rho(NUMFST(c:num)) / &4 - norm(z0:real^3)))` THEN
    REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Uniform goodness and injectivity at each level (as in cgemb).            *)
(* ------------------------------------------------------------------------- *)

let P2GE_GOOD_UNIFORM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp
    (Fs:num->real^3->A) c S.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     compact S /\ (!z. z IN S ==> p2ce_good top atlas h yc rho kp sq Fs c z)
     ==> ?lam N.
           &0 < lam /\
           (!n z. N <= n /\ z IN S
                  ==> ball(z,lam) SUBSET p2cg_dm rho c /\
                      (!w. w IN ball(z,lam)
                           ==> Fs n (kp c w) IN IMAGE (p2cg_nch top atlas h yc (sq n) c)
                                                      (ball(vec 0,rho(NUMFST c)))) /\
                      smooth_map_on (ball(z,lam))
                        (\w. p2ce_L top atlas h yc rho (sq n) c (Fs n (kp c w))) /\
                      (!w w'. w IN ball(z,lam) /\ w' IN ball(z,lam)
                              ==> norm(w - w') <=
                                  &2 * norm(p2ce_L top atlas h yc rho (sq n) c (Fs n (kp c w)) -
                                            p2ce_L top atlas h yc rho (sq n) c
                                              (Fs n (kp c w')))) /\
                      (!w. w IN ball(z,lam)
                           ==> ~(det(matrix(frechet_derivative
                                    (\w. p2ce_L top atlas h yc rho (sq n) c (Fs n (kp c w)))
                                    (at w))) = &0))) /\
           (!e. &0 < e
                ==> ?Ne. !n z w. Ne <= n /\ z IN S /\ w IN ball(z,lam)
                                 ==> norm(p2ce_L top atlas h yc rho (sq n) c
                                            (Fs n (kp c w)) - w) < e)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gd"))) THEN
  (* local data at each point *)
  SUBGOAL_THEN
   `!z0. z0 IN S
         ==> ?r M. &0 < r /\
                   (!n. M <= n
                        ==> ball(z0,r) SUBSET p2cg_dm rho c /\
                            (!w. w IN ball(z0,r)
                                 ==> (Fs:num->real^3->A) n (kp c w) IN
                                     IMAGE (p2cg_nch (top:num->A topology) atlas
                                              (h:num->A->real^3^3) yc (sq n) c)
                                           (ball(vec 0,rho(NUMFST c)))) /\
                            smooth_map_on (ball(z0,r))
                              (\w. p2ce_L top atlas h yc rho (sq n) c
                                     (Fs n ((kp:num->real^3->real^3) c w))) /\
                            (!w w'. w IN ball(z0,r) /\ w' IN ball(z0,r)
                                    ==> norm(w - w') <=
                                        &2 * norm(p2ce_L top atlas h yc rho (sq n) c
                                                    (Fs n (kp c w)) -
                                                  p2ce_L top atlas h yc rho (sq n) c
                                                    (Fs n (kp c w')))) /\
                            (!w. w IN ball(z0,r)
                                 ==> ~(det(matrix(frechet_derivative
                                          (\w. p2ce_L top atlas h yc rho (sq n) c
                                                 (Fs n (kp c w))) (at w))) = &0))) /\
                   (!e. &0 < e
                        ==> ?Ne. !n w. Ne <= n /\ w IN ball(z0,r)
                                       ==> norm(p2ce_L top atlas h yc rho (sq n) c
                                                  (Fs n (kp c w)) - w) < e)`
  MP_TAC THENL
   [X_GEN_TAC `z0:real^3` THEN DISCH_TAC THEN
    USE_THEN "gd" (MP_TAC o C MP (ASSUME `(z0:real^3) IN S`) o SPEC `z0:real^3`) THEN
    REWRITE_TAC[p2ce_good] THEN
    DISCH_THEN(X_CHOOSE_THEN `rg:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `Ng:num` (LABEL_TAC "lg")) (LABEL_TAC "ng"))))) THEN
    USE_THEN "ng" (MP_TAC o MATCH_MP P2CE_NEAR_ID_INJ) THEN
    DISCH_THEN(X_CHOOSE_THEN `ri:real` (X_CHOOSE_THEN `Ni:num`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))) THEN
    USE_THEN "ng" (MP_TAC o REWRITE_RULE[p2ci_near]) THEN
    DISCH_THEN(X_CHOOSE_THEN `ru:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "cl")))))) THEN
    EXISTS_TAC `min rg (min ri ru)` THEN EXISTS_TAC `Ng + Ni:num` THEN
    SUBGOAL_THEN `ball(z0:real^3,min rg (min ri ru)) SUBSET ball(z0,rg) /\
                  ball(z0:real^3,min rg (min ri ru)) SUBSET ball(z0,ri) /\
                  ball(z0:real^3,min rg (min ri ru)) SUBSET ball(z0,ru)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      USE_THEN "inj" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z0:real^3,rg)` THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN USE_THEN "lg" MATCH_MP_TAC THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ASM SET_TAC[]];
        MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^3,ri)` THEN
        ASM_REWRITE_TAC[];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `&2`)) (concl th))) THEN ASM SET_TAC[];
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
          can (find_term ((=) `det:real^3^3->real`)) (concl th) && is_forall(concl th))) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]]];
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      USE_THEN "cl" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Ne:num` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `w:real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->real` (X_CHOOSE_THEN `M:real^3->num` (LABEL_TAC "loc"))) THEN
  (* a finite subcover *)
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\z0:real^3. ball(z0,r z0 / &2)) S`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; OPEN_BALL; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(y:real^3) IN S`) o SPEC `y:real^3`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[EXISTS_FINITE_SUBSET_IMAGE] o
             ONCE_REWRITE_RULE[TAUT `a /\ b /\ c <=> b /\ a /\ c`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `T0:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\z0:real^3. r z0 / &2`; `T0:real^3->bool`] P2CE_FINITE_MIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
     [ASM SET_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `lam:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `IMAGE (M:real^3->num) T0` num_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_TAC `NM:num`) THEN
  SUBGOAL_THEN
   `!z:real^3. z IN S ==> ?z0. z0 IN T0 /\ ball(z,lam) SUBSET ball(z0,r z0) /\ z0 IN S`
  (LABEL_TAC "cov") THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `(S:real^3->bool) SUBSET UNIONS (IMAGE (\z0:real^3. ball(z0,r z0 / &2)) T0)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z0:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `(z:real^3) IN ball(z0,r z0 / &2)` THEN REWRITE_TAC[IN_BALL] THEN
    SUBGOAL_THEN `lam <= (r:real^3->real) z0 / &2` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `z0:real^3` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `lam:real`)) (concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`z0:real^3`; `z:real^3`; `w:real^3`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `NM:num`] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    USE_THEN "cov" (MP_TAC o C MP (ASSUME `(z:real^3) IN S`) o SPEC `z:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "loc" (MP_TAC o C MP (ASSUME `(z0:real^3) IN S`) o SPEC `z0:real^3`) THEN
    DISCH_THEN(MP_TAC o SPEC `n:num` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `NM:num` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(z0:real^3,r z0)` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `&2`)) (concl th))) THEN ASM SET_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `det:real^3^3->real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]]];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!z0:real^3. z0 IN T0
                  ==> ?Ne. !n w. Ne <= n /\ w IN ball(z0,r z0)
                                 ==> norm(p2ce_L (top:num->A topology) atlas
                                            (h:num->A->real^3^3) yc rho (sq n) c
                                            ((Fs:num->real^3->A) n
                                             ((kp:num->real^3->real^3) c w)) - w) < e`
    MP_TAC THENL
     [X_GEN_TAC `z0:real^3` THEN DISCH_TAC THEN
      USE_THEN "loc" (MP_TAC o SPEC `z0:real^3`) THEN ANTS_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `Nee:real->num` MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
      DISCH_TAC THEN EXISTS_TAC `(Nee:real->num) e` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
    DISCH_THEN(X_CHOOSE_THEN `Nf:real^3->num` (LABEL_TAC "nf")) THEN
    MP_TAC(ISPEC `IMAGE (Nf:real^3->num) T0` num_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_TAC `Ne:num`) THEN EXISTS_TAC `Ne:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    USE_THEN "cov" (MP_TAC o C MP (ASSUME `(z:real^3) IN S`) o SPEC `z:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC) THEN
    USE_THEN "nf" (MP_TAC o C MP (ASSUME `(z0:real^3) IN T0`) o SPEC `z0:real^3`) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `Ne:num` THEN ASM_SIMP_TAC[]; ASM SET_TAC[]]]);;

(* Small D-distance from a point of a chart gives a nearby point of the same chart. *)

let P2GE_DV_SMALL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp a z b w e.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     norm z < rho(NUMFST a) / &7 /\ w IN p2cg_dm rho b /\
     p2cg_dv D a z b w < e /\ e <= rho(NUMFST a) / &20
     ==> w IN p2cg_om rho D b a /\ p2cg_tr rho D b a w IN p2cg_dm rho a /\
         kp b w = kp a (p2cg_tr rho D b a w) /\
         norm(p2cg_tr rho D b a w - z) < sqrt(&2) * e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(a:num)`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(b:num)`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN cball(vec 0,rho(NUMFST(a:num)) / &2) /\
                (w:real^3) IN cball(vec 0,rho(NUMFST(b:num)) / &2) /\
                (vec 0:real^3) IN cball(vec 0,rho(NUMFST(a:num)) / &2) /\
                norm(w:real^3) < rho(NUMFST b) / &4`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN p2cg_dm rho b` THEN
    REWRITE_TAC[p2cg_dm; IN_BALL_0; IN_CBALL_0; NORM_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN p2cg_om rho D b a` ASSUME_TAC THENL
   [REWRITE_TAC[P2CG_IN_OM; IN_BALL_0] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `b:num`; `w:real^3`; `a:num`; `z:real^3`; `a:num`; `vec 0:real^3`])
                  P2GB_DV_TRI) THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `z:real^3`; `b:num`; `w:real^3`]) P2GB_DV_SYM) THEN
    MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                               `a:num`; `z:real^3`]) P2GB_DV_REFL0) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `b:num`; `a:num`; `w:real^3`]) P2GB_TR_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ABBREV_TAC `z' = p2cg_tr rho D b a w` THEN
  SUBGOAL_THEN `(z':real^3) IN p2cg_dm rho a` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[p2cg_dm]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `p2cl_glue (p2cg_dm rho) (p2cg_om rho D) (p2cg_tr rho D)
                           (kp:num->real^3->real^3)` THEN
    REWRITE_TAC[p2cl_glue] THEN
    DISCH_THEN(MP_TAC o SPECL [`b:num`; `a:num`; `w:real^3`; `z':real^3`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z':real^3) IN cball(vec 0,rho(NUMFST(a:num)) / &2) /\
                norm(z':real^3) < rho(NUMFST a) / &4` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(z':real^3) IN ball(vec 0,rho(NUMFST(a:num)) / &4)` THEN
    REWRITE_TAC[IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST(a:num)) / &4` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `z:real^3`; `z':real^3`]) P2GB_DV_LOWER) THEN
  MP_TAC(ISPECL (p2cg_std @ [`sq:num->num`; `D:num#num->real^(3,3)finite_sum->real^1`;
                             `a:num`; `z:real^3`; `b:num`; `w:real^3`; `a:num`; `z':real^3`])
                P2GB_DV_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`z:real^3`; `z':real^3`] NORM_SUB) THEN
  SUBGOAL_THEN `&0 < sqrt(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sqrt(&2) * p2cg_dv D a z a (z':real^3)` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* The pointwise injectivity argument for one pair of charts. *)

let P2GE_INJ_POINT = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp
    (Fm:real^3->A) k a b z w lam eps.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     p2cg_nv N0 Nn a <= k /\ p2cg_nv N0 Nn b <= k /\
     &0 < lam /\ &0 < eps /\ eps <= lam / &2 /\ eps <= rho(NUMFST a) / &20 /\
     norm z < rho(NUMFST a) / &7 /\ w IN p2cg_dm rho b /\
     (!v. v IN ball(z,lam)
          ==> Fm (kp a v) IN IMAGE (p2cg_nch top atlas h yc k a) (ball(vec 0,rho(NUMFST a)))) /\
     (!v v'. v IN ball(z,lam) /\ v' IN ball(z,lam)
             ==> norm(v - v') <=
                 &2 * norm(p2ce_L top atlas h yc rho k a (Fm (kp a v)) -
                           p2ce_L top atlas h yc rho k a (Fm (kp a v')))) /\
     norm(p2ce_L top atlas h yc rho k a (Fm (kp a z)) - z) < eps / &8 /\
     Fm (kp b w) IN IMAGE (p2cg_nch top atlas h yc k b) (ball(vec 0,rho(NUMFST b))) /\
     norm(p2ce_L top atlas h yc rho k b (Fm (kp b w)) - w) < eps / &8 /\
     abs(p2cg_dk top atlas h yc k a z b w - p2cg_dv D a z b w) < eps / &4 /\
     Fm (kp a z) = Fm (kp b w)
     ==> kp a z = kp b w`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "land") (CONJUNCTS_THEN2 (LABEL_TAC "lip") (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))))))))))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(a:num)`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`NUMFST(b:num)`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`]) P2GE_L_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "la1") (LABEL_TAC "la2")) THEN
  MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`]) P2GE_L_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lb1") (LABEL_TAC "lb2")) THEN
  SUBGOAL_THEN `(z:real^3) IN ball(z,lam)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `p2ce_L top atlas (h:num->A->real^3^3) yc rho k a ((Fm:real^3->A) ((kp:num->real^3->real^3) a z))
      IN ball(vec 0,rho(NUMFST(a:num))) /\
    p2cg_nch top atlas h yc k a (p2ce_L top atlas h yc rho k a (Fm (kp a z))) = Fm (kp a z)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "la2" MATCH_MP_TAC THEN USE_THEN "land" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p2ce_L top atlas (h:num->A->real^3^3) yc rho k b ((Fm:real^3->A) ((kp:num->real^3->real^3) b w))
      IN ball(vec 0,rho(NUMFST(b:num))) /\
    p2cg_nch top atlas h yc k b (p2ce_L top atlas h yc rho k b (Fm (kp b w))) = Fm (kp b w)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "lb2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `u = p2ce_L top atlas (h:num->A->real^3^3) yc rho k a
                    ((Fm:real^3->A) ((kp:num->real^3->real^3) a z))` THEN
  ABBREV_TAC `u' = p2ce_L top atlas (h:num->A->real^3^3) yc rho k b
                     ((Fm:real^3->A) ((kp:num->real^3->real^3) b w))` THEN
  SUBGOAL_THEN `norm(z:real^3) < rho(NUMFST(a:num)) /\ norm(u:real^3) < rho(NUMFST a) /\
                norm(w:real^3) < rho(NUMFST(b:num)) /\ norm(u':real^3) < rho(NUMFST b)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN p2cg_dm rho b` THEN
    UNDISCH_TAC `(u:real^3) IN ball(vec 0,rho(NUMFST(a:num)))` THEN
    UNDISCH_TAC `(u':real^3) IN ball(vec 0,rho(NUMFST(b:num)))` THEN
    REWRITE_TAC[p2cg_dm; IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the images coincide, so the chart distance of u and u' is 0 *)
  SUBGOAL_THEN `p2cg_dk top atlas (h:num->A->real^3^3) yc k a u b u' = &0` ASSUME_TAC THENL
   [REWRITE_TAC[p2cg_dk] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_DIST_REFL THEN
    MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                   `h:num->A->real^3^3`; `x:num->A`; `k:num`] P2GE_SEQ_MFD) THEN
    ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`]) P2GE_NCH_PARAM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MFD_PARAM_MAPS) THEN
    DISCH_THEN(X_CHOOSE_THEN `e':A->real^3` (MP_TAC o MATCH_MP OPEN_IN_SUBSET o
                                                 CONJUNCT1 o CONJUNCT2)) THEN
    UNDISCH_TAC `(Fm:real^3->A) ((kp:num->real^3->real^3) b w) IN
                 IMAGE (p2cg_nch top atlas (h:num->A->real^3^3) yc k b)
                       (ball(vec 0,rho(NUMFST(b:num))))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* hence dk at (z,w) is small, and so is dv *)
  SUBGOAL_THEN `p2cg_dv D a z b w < eps` ASSUME_TAC THENL
   [MP_TAC(ISPECL (p2cg_std @ [`k:num`; `a:num`; `z:real^3`; `a:num`; `u:real^3`;
                               `b:num`; `w:real^3`]) P2GB_DK_TRI) THEN
    MP_TAC(ISPECL (p2cg_std @ [`k:num`; `a:num`; `u:real^3`; `b:num`; `u':real^3`;
                               `b:num`; `w:real^3`]) P2GB_DK_TRI) THEN
    MP_TAC(ISPECL (p2cg_std @ [`a:num`; `k:num`; `z:real^3`; `u:real^3`]) P2GB_NCH_LIP) THEN
    MP_TAC(ISPECL (p2cg_std @ [`b:num`; `k:num`; `u':real^3`; `w:real^3`]) P2GB_NCH_LIP) THEN
    ASM_REWRITE_TAC[GSYM p2cg_dk] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `sqrt(&2) * norm(z - u:real^3) <= &3 / &2 * norm(z - u) /\
                  sqrt(&2) * norm(u' - w:real^3) <= &3 / &2 * norm(u' - w)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MP_TAC P2CG_SQRT2_LT THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`z:real^3`; `u:real^3`] NORM_SUB) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL (p2ce_std @ [`a:num`; `z:real^3`; `b:num`; `w:real^3`; `eps:real`])
                P2GE_DV_SMALL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `z' = p2cg_tr rho D b a w` THEN
  SUBGOAL_THEN `(z':real^3) IN ball(z,lam)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    SUBGOAL_THEN `sqrt(&2) * eps <= &3 / &2 * eps` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN MP_TAC P2CG_SQRT2_LT THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:real^3) = z'` (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `p2ce_L top atlas (h:num->A->real^3^3) yc rho k a ((Fm:real^3->A) ((kp:num->real^3->real^3) a z')) = u`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(Fm:real^3->A) ((kp:num->real^3->real^3) a z') =
                  p2cg_nch top atlas (h:num->A->real^3^3) yc k a u` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(kp:num->real^3->real^3) b w = kp a z'` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      USE_THEN "la1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "lip" (MP_TAC o SPECL [`z:real^3`; `z':real^3`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_MUL_RZERO; NORM_LE_0; VECTOR_SUB_EQ]);;

let P2GE_LEVEL_CHART_DATA = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j i.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ i < P(j + 2)
     ==> ?lam M Ne.
           &0 < lam /\
           (!n:num z.
              M <= n /\ z IN cball(vec 0,&2 * rho(j + 2) / &15)
              ==> (!w. w IN ball(z,lam)
                       ==> p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                             (kp (NUMPAIR (j + 2) i) w) IN
                           IMAGE (p2cg_nch top atlas h yc (sq n) (NUMPAIR (j + 2) i))
                                 (ball(vec 0,rho(j + 2)))) /\
                  (!w w'. w IN ball(z,lam) /\ w' IN ball(z,lam)
                          ==> norm(w - w') <=
                              &2 * norm(p2ce_L top atlas h yc rho (sq n) (NUMPAIR (j + 2) i)
                                          (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n)
                                             (P(j + 2)) (kp (NUMPAIR (j + 2) i) w)) -
                                        p2ce_L top atlas h yc rho (sq n) (NUMPAIR (j + 2) i)
                                          (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n)
                                             (P(j + 2)) (kp (NUMPAIR (j + 2) i) w')))) /\
                  smooth_map_on (ball(z,lam))
                    (\w. p2ce_L top atlas h yc rho (sq n) (NUMPAIR (j + 2) i)
                           (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                              (kp (NUMPAIR (j + 2) i) w))) /\
                  (!w. w IN ball(z,lam)
                       ==> ~(det(matrix(frechet_derivative
                                (\w. p2ce_L top atlas h yc rho (sq n) (NUMPAIR (j + 2) i)
                                       (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n)
                                          (P(j + 2)) (kp (NUMPAIR (j + 2) i) w)))
                                (at w))) = &0))) /\
           (!e n:num z w.
                       &0 < e /\ Ne e <= n /\ z IN cball(vec 0,&2 * rho(j + 2) / &15) /\
                       w IN ball(z,lam)
                       ==> norm(p2ce_L top atlas h yc rho (sq n) (NUMPAIR (j + 2) i)
                                  (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                                     (kp (NUMPAIR (j + 2) i) w)) - w) < e)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`\n. p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                                     (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n)
                                     (P(j + 2))`;
                             `NUMPAIR (j + 2) i`;
                             `cball(vec 0:real^3,&2 * rho(j + 2) / &15)`]) P2GE_GOOD_UNIFORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_CBALL] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2ce_std @ [`p2ce_cs P j`]) P2GE_INV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:real^3) IN cball(vec 0,&2 * rho(j + 2) / &15)` THEN
    REWRITE_TAC[p2cg_dm; IN_BALL_0; IN_CBALL_0; NUMPAIR_DEST] THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC P2CE_IN_OM_LEVEL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NUMPAIR_DEST] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `M:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "st")
      (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ne:real->num` (LABEL_TAC "cl")) THEN
  MAP_EVERY EXISTS_TAC [`lam:real`; `M:num`; `Ne:real->num`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `z:real^3`] THEN STRIP_TAC THEN
    REMOVE_THEN "st" (MP_TAC o SPECL [`n:num`; `z:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    USE_THEN "cl" (MP_TAC o C MP (ASSUME `&0 < e`) o SPEC `e:real`) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[]]);;

let P2GE_INJ_LEVEL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> ?N. !n i i' z w.
               N <= n /\ i < P(j + 2) /\ i' < P(j + 2) /\
               z IN cball(vec 0,&2 * rho(j + 2) / &15) /\
               w IN cball(vec 0,&2 * rho(j + 2) / &15) /\
               p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                      (kp (NUMPAIR (j + 2) i) z) =
               p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                      (kp (NUMPAIR (j + 2) i') w)
               ==> kp (NUMPAIR (j + 2) i) z = kp (NUMPAIR (j + 2) i') w`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_LEVEL_CHART_DATA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `lamf:num->real` (X_CHOOSE_THEN `Mf:num->num`
    (X_CHOOSE_THEN `Nef:num->real->num` (LABEL_TAC "un")))) THEN
  MP_TAC(ISPECL [`lamf:num->real`; `{i:num | i < P(j + 2)}`] P2CE_FINITE_MIN) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  ANTS_TAC THENL [USE_THEN "un" (fun th -> MESON_TAC[th]); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `eps = min (d / &2) (rho(j + 2) / &20)` THEN
  SUBGOAL_THEN `&0 < eps /\ eps <= d / &2 /\ eps <= rho(j + 2) / &20` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* uniform convergence of the chart distances, for each pair of charts *)
  SUBGOAL_THEN
   `!i i'. ?Nd. !n:num z w.
              Nd <= n /\ z IN cball(vec 0,rho(NUMFST(NUMPAIR (j + 2) i)) / &2) /\
              w IN cball(vec 0,rho(NUMFST(NUMPAIR (j + 2) i')) / &2)
              ==> abs(p2cg_dk top atlas (h:num->A->real^3^3) yc (sq n)
                        (NUMPAIR (j + 2) i) z (NUMPAIR (j + 2) i') w -
                      p2cg_dv D (NUMPAIR (j + 2) i) z (NUMPAIR (j + 2) i') w) < eps / &4`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC P2CG_D_UNIF THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nd:num->num->num` (LABEL_TAC "du")) THEN
  MP_TAC(ISPECL [`Mf:num->num`; `P(j + 2):num`] P2CE_NUM_BOUND) THEN
  DISCH_THEN(X_CHOOSE_TAC `B1:num`) THEN
  MP_TAC(ISPECL [`\i. (Nef:num->real->num) i (eps / &8)`; `P(j + 2):num`] P2CE_NUM_BOUND) THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B2:num`) THEN
  SUBGOAL_THEN `?B3. !i i'. i < P(j + 2) /\ i' < P(j + 2) ==> (Nd:num->num->num) i i' <= B3`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!i. ?Bi. !i'. i' < P(j + 2) ==> (Nd:num->num->num) i i' <= Bi` MP_TAC THENL
     [GEN_TAC THEN MATCH_ACCEPT_TAC(ISPECL [`(Nd:num->num->num) i`; `P(j + 2):num`]
                                          P2CE_NUM_BOUND);
      ALL_TAC] THEN
    REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `Bf:num->num`) THEN
    MP_TAC(ISPECL [`Bf:num->num`; `P(j + 2):num`] P2CE_NUM_BOUND) THEN
    DISCH_THEN(X_CHOOSE_TAC `B3:num`) THEN EXISTS_TAC `B3:num` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(Bf:num->num) i` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `B1 + B2 + B3 + p2cg_nv N0 Nn (NUMPAIR (j + 2) 0)` THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `i:num`; `i':num`; `z:real^3`; `w:real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!l. p2cg_nv N0 Nn (NUMPAIR (j + 2) l) <= (sq:num->num) n` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[p2cg_nv; NUMPAIR_DEST] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `B1 + B2 + B3 + p2cg_nv N0 Nn (NUMPAIR (j + 2) 0) <= n` THEN
    REWRITE_TAC[p2cg_nv; NUMPAIR_DEST] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Mf:num->num) i <= n /\ Mf i' <= n /\
                (Nef:num->real->num) i (eps / &8) <= n /\ Nef i' (eps / &8) <= n /\
                (Nd:num->num->num) i i' <= n` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THENL
     [EXISTS_TAC `B1:num`; EXISTS_TAC `B1:num`; EXISTS_TAC `B2:num`; EXISTS_TAC `B2:num`;
      EXISTS_TAC `B3:num`] THEN
    ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "un" (MP_TAC o C MP (ASSUME `(i:num) < P(j + 2)`) o SPEC `i:num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (MP_TAC o SPECL [`n:num`; `z:real^3`]) (LABEL_TAC "ci"))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lz") (CONJUNCTS_THEN2 (LABEL_TAC "lip") (K ALL_TAC))) THEN
  USE_THEN "un" (MP_TAC o C MP (ASSUME `(i':num) < P(j + 2)`) o SPEC `i':num`) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (MP_TAC o SPECL [`n:num`; `w:real^3`]) (LABEL_TAC "ci'"))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lw") (K ALL_TAC)) THEN
  MATCH_MP_TAC(ISPECL (p2ce_std @ [`p2ce_F top atlas (h:num->A->real^3^3) yc rho
                                      (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n)
                                      (P(j + 2))`;
                                   `(sq:num->num) n`;
                                   `NUMPAIR (j + 2) i`; `NUMPAIR (j + 2) i'`; `z:real^3`;
                                   `w:real^3`; `d:real`; `eps:real`]) P2GE_INJ_POINT) THEN
  ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
  SUBGOAL_THEN `(d:real) <= lamf (i:num) /\ d <= lamf (i':num) /\
                &0 < lamf i /\ &0 < lamf i'` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ball(z:real^3,d) SUBSET ball(z,lamf (i:num)) /\
                (z:real^3) IN ball(z,lamf i) /\ (w:real^3) IN ball(w,lamf (i':num))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ASM_REWRITE_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(z:real^3) IN cball(vec 0,&2 * rho(j + 2) / &15)` THEN
    REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `(w:real^3) IN cball(vec 0,&2 * rho(j + 2) / &15)` THEN
    REWRITE_TAC[p2cg_dm; IN_CBALL_0; IN_BALL_0; NUMPAIR_DEST] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN USE_THEN "lz" MATCH_MP_TAC THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`v:real^3`; `v':real^3`] THEN STRIP_TAC THEN
    USE_THEN "lip" MATCH_MP_TAC THEN ASM SET_TAC[];
    USE_THEN "ci" (MP_TAC o SPECL [`eps / &8`; `n:num`; `z:real^3`; `z:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    USE_THEN "lw" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "ci'" (MP_TAC o SPECL [`eps / &8`; `n:num`; `w:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    USE_THEN "du" MATCH_MP_TAC THEN ASM_REWRITE_TAC[NUMPAIR_DEST] THEN
    UNDISCH_TAC `(z:real^3) IN cball(vec 0,&2 * rho(j + 2) / &15)` THEN
    UNDISCH_TAC `(w:real^3) IN cball(vec 0,&2 * rho(j + 2) / &15)` THEN
    REWRITE_TAC[IN_CBALL_0] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The pieces are diffeomorphic images, their union (as in cgemb; the cover  *)
(* of the closure by pieces uses pc_p2c_lcgc).                               *)
(* ------------------------------------------------------------------------- *)

let P2GE_KP_PARAM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp c s.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\
     open s /\ s SUBSET p2cg_dm rho c
     ==> mfd_param (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp) s (kp c)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2GC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MFD_PARAM_RESTRICT THEN EXISTS_TAC `p2cg_dm rho c` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `chart_inv (p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) c)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `p2cg_dm rho c =
                  IMAGE (SND(p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) c))
                        (FST(p2cl_chart (p2cg_dm rho) kp c))`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[GSYM IMAGE_o] THEN
      MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> f x = x) ==> s = IMAGE f s`) THEN
      ASM_SIMP_TAC[o_THM];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                   `FST(p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) c)`;
                   `SND(p2cl_chart (p2cg_dm rho) (kp:num->real^3->real^3) c)`]
                  MFD_PARAM_CHART_INV) THEN
    ASM_REWRITE_TAC[PAIR];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC P2CL_CHART_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`p2cg_om rho D`; `p2cg_tr rho D`] THEN ASM_REWRITE_TAC[]]);;

(* One piece: the final map composed with the chart is a parametrization. *)

let P2GE_PIECE_PARAM = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j i.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ i < P(j + 2)
     ==> ?N. !n. N <= n
                 ==> mfd_param (top(sq n)) (atlas(sq n)) (ball(vec 0,&2 * rho(j + 2) / &15))
                       (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)) o
                        kp (NUMPAIR (j + 2) i))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_KP_FACTS) THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`; `i:num`]) P2GE_LEVEL_CHART_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lam:real` (X_CHOOSE_THEN `M:num` (X_CHOOSE_THEN `Ne:real->num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "st") (K ALL_TAC)))))) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_INJ_LEVEL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `NI:num` (LABEL_TAC "inj")) THEN
  EXISTS_TAC `M + NI + p2cg_nv N0 Nn (NUMPAIR (j + 2) i)` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!w w'. w IN ball(vec 0:real^3,&2 * rho(j + 2) / &15) /\
           w' IN ball(vec 0:real^3,&2 * rho(j + 2) / &15) /\
           p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                  (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n) (P(j + 2))
                  (kp (NUMPAIR (j + 2) i) w) =
           p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))
                  (kp (NUMPAIR (j + 2) i) w')
           ==> w = w'`
  (LABEL_TAC "inj1") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> can (find_term ((=) `z':real^3`)) (concl th))) THEN
    EXISTS_TAC `NUMPAIR (j + 2) i` THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(w:real^3) IN ball(vec 0,&2 * rho(j + 2) / &15)` THEN
      REWRITE_TAC[p2cg_dm; IN_BALL_0; NUMPAIR_DEST] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(w':real^3) IN ball(vec 0,&2 * rho(j + 2) / &15)` THEN
      REWRITE_TAC[p2cg_dm; IN_BALL_0; NUMPAIR_DEST] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "inj" MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY(ASM_ARITH_TAC) THEN
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `ball(vec 0:real^3,&2 * rho(j + 2) / &15)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL]];
    ALL_TAC] THEN
  ABBREV_TAC `s = ball(vec 0:real^3,&2 * rho(j + 2) / &15)` THEN
  ABBREV_TAC `a = NUMPAIR (j + 2) i` THEN
  ABBREV_TAC `Fm = p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                     (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n) (P(j + 2))` THEN
  SUBGOAL_THEN `p2cg_nv N0 Nn a <= (sq:num->num) n` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `NUMFST(a:num) = j + 2 /\ s SUBSET p2cg_dm rho a /\
                (!w:real^3. w IN s ==> w IN cball(vec 0,&2 * rho(j + 2) / &15)) /\
                open (s:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "s"] THEN
    REWRITE_TAC[NUMPAIR_DEST; p2cg_dm; SUBSET; IN_BALL_0; IN_CBALL_0; OPEN_BALL] THEN
    CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the pointwise data on s *)
  SUBGOAL_THEN
   `!w:real^3. w IN s
               ==> Fm (kp a w) IN IMAGE (p2cg_nch top atlas (h:num->A->real^3^3) yc ((sq:num->num) n) a)
                                        (ball(vec 0,rho(j + 2))) /\
                   (?t. open t /\ w IN t /\
                        smooth_map_on t (\w. p2ce_L top atlas h yc rho ((sq:num->num) n) a
                                               ((Fm:real^3->A) ((kp:num->real^3->real^3) a w)))) /\
                   ~(det(matrix(frechet_derivative
                          (\w. p2ce_L top atlas h yc rho ((sq:num->num) n) a (Fm (kp a w))) (at w))) = &0)`
  (LABEL_TAC "pt") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "st" (MP_TAC o SPECL [`n:num`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN ball(w,lam)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `IMAGE:(real^3->A)->(real^3->bool)->A->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `ball(w:real^3,lam)` THEN ASM_REWRITE_TAC[OPEN_BALL];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `det:real^3^3->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `R = \w. p2ce_L top atlas (h:num->A->real^3^3) yc rho ((sq:num->num) n) a
                        ((Fm:real^3->A) ((kp:num->real^3->real^3) a w))` THEN
  MP_TAC(ISPECL (p2cg_std @ [`a:num`; `(sq:num->num) n`]) P2GE_L_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "l1") (LABEL_TAC "l2")) THEN
  SUBGOAL_THEN
   `!w:real^3. w IN s
               ==> (R:real^3->real^3) w IN ball(vec 0,rho(j + 2)) /\
                   p2cg_nch top atlas (h:num->A->real^3^3) yc ((sq:num->num) n) a (R w) =
                   (Fm:real^3->A) ((kp:num->real^3->real^3) a w)`
  (LABEL_TAC "rw") THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN EXPAND_TAC "R" THEN REWRITE_TAC[] THEN
    USE_THEN "l2" MATCH_MP_TAC THEN
    USE_THEN "pt" (MP_TAC o C MP (ASSUME `(w:real^3) IN s`) o SPEC `w:real^3`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?R'. diffeomorphism_on s (IMAGE (R:real^3->real^3) s) R R'` MP_TAC THENL
   [MATCH_MP_TAC P2CE_INJ_DIFFEO THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "pt" (MP_TAC o C MP (ASSUME `(w:real^3) IN s`) o SPEC `w:real^3`) THEN
      SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`w:real^3`; `w':real^3`] THEN STRIP_TAC THEN
      USE_THEN "inj1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rw" (MP_TAC o C MP (ASSUME `(w:real^3) IN s`) o SPEC `w:real^3`) THEN
      USE_THEN "rw" (MP_TAC o C MP (ASSUME `(w':real^3) IN s`) o SPEC `w':real^3`) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      USE_THEN "pt" (MP_TAC o C MP (ASSUME `(w:real^3) IN s`) o SPEC `w:real^3`) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `R':real^3->real^3`) THEN
  MATCH_MP_TAC MFD_PARAM_EQ THEN
  EXISTS_TAC `p2cg_nch top atlas (h:num->A->real^3^3) yc ((sq:num->num) n) a o (R:real^3->real^3)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                   `h:num->A->real^3^3`; `x:num->A`; `(sq:num->num) n`] P2GE_SEQ_MFD) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC MFD_PARAM_PRECOMPOSE THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,rho(j + 2))`; `IMAGE (R:real^3->real^3) s`;
                          `R':real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `(sq:num->num) n`] P2GE_SEQ_MFD) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL (p2cg_std @ [`a:num`; `(sq:num->num) n`]) P2GE_NCH_PARAM) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]]);;

let P2GE_PIECE_DIFFEO = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j i.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ i < P(j + 2)
     ==> ?N. !n. N <= n
                 ==> ?G. mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                           (IMAGE (kp (NUMPAIR (j + 2) i)) (ball(vec 0,&2 * rho(j + 2) / &15)))
                           (top(sq n)) (atlas(sq n))
                           (IMAGE (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)))
                              (IMAGE (kp (NUMPAIR (j + 2) i))
                                     (ball(vec 0,&2 * rho(j + 2) / &15))))
                           (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))) G`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
    MP_TAC(MATCH_MP P2GE_PIECE_PARAM th)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N:num <= n`) o SPEC `n:num`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2GC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2cg_std @ [`j + 2`]) P2GB_RHO_POS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `s = ball(vec 0:real^3,&2 * rho(j + 2) / &15)` THEN
  ABBREV_TAC `Fm = p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                     (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n) (P(j + 2))` THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `e':A->real^3`) THEN
  MP_TAC(ISPECL (p2ce_std @ [`NUMPAIR (j + 2) i`; `s:real^3->bool`]) P2GE_KP_PARAM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[OPEN_BALL; p2cg_dm; SUBSET; IN_BALL_0; NUMPAIR_DEST] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[mfd_param] THEN DISCH_THEN(X_CHOOSE_TAC `k':real^3->real^3`) THEN
  SUBGOAL_THEN `smooth_manifold_atlas ((top:num->A topology) ((sq:num->num) n))
                  ((atlas:num->((A->bool)#(A->real^3))->bool) (sq n))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                   `h:num->A->real^3^3`; `x:num->A`; `(sq:num->num) n`] P2GE_SEQ_MFD) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
                 `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
                 `IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i)) s`;
                 `euclidean:(real^3)topology`; `open_set_atlas (:real^3)`; `s:real^3->bool`;
                 `(top:num->A topology) ((sq:num->num) n)`; `(atlas:num->((A->bool)#(A->real^3))->bool) ((sq:num->num) n)`;
                 `IMAGE ((Fm:real^3->A) o (kp:num->real^3->real^3) (NUMPAIR (j + 2) i)) s`;
                 `k':real^3->real^3`; `(kp:num->real^3->real^3) (NUMPAIR (j + 2) i)`;
                 `(Fm:real^3->A) o (kp:num->real^3->real^3) (NUMPAIR (j + 2) i)`;
                 `e':A->real^3`] MFD_DIFFEO_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MFD_EUCLIDEAN_ATLAS] THEN MATCH_MP_TAC MFD_DIFFEO_SYM THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(kp:num->real^3->real^3) (NUMPAIR (j + 2) i) o (e':A->real^3)` THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC MFD_DIFFEO_EQ THEN
  MAP_EVERY EXISTS_TAC [`((Fm:real^3->A) o (kp:num->real^3->real^3) (NUMPAIR (j + 2) i)) o
                         (k':real^3->real^3)`;
                        `(kp:num->real^3->real^3) (NUMPAIR (j + 2) i) o (e':A->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MFD_DIFFEO_MAPS o check (fun th ->
    can (find_term ((=) `k':real^3->real^3`)) (concl th) &&
    can (find_term ((=) `euclidean:(real^3)topology`)) (concl th) &&
    not (can (find_term ((=) `e':A->real^3`)) (concl th)))) THEN
  ASM_SIMP_TAC[]);;

(* The pieces cover the closure of W j. *)

let P2GE_COVER_PIECES = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp j SUBSET
         UNIONS {IMAGE (kp (NUMPAIR (j + 2) i)) (ball(vec 0,&2 * rho(j + 2) / &15)) |
                 i | i < P(j + 2)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ge_ctx] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GC_COVER_PIECES) THEN ASM_REWRITE_TAC[]);;

(* Gluing the pieces. *)

let P2GE_DIFFEO_UNION = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> ?N. !n. N <= n
                 ==> ?G. mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                           (UNIONS {IMAGE (kp (NUMPAIR (j + 2) i))
                                          (ball(vec 0,&2 * rho(j + 2) / &15)) |
                                    i | i < P(j + 2)})
                           (top(sq n)) (atlas(sq n))
                           (IMAGE (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)))
                              (UNIONS {IMAGE (kp (NUMPAIR (j + 2) i))
                                             (ball(vec 0,&2 * rho(j + 2) / &15)) |
                                       i | i < P(j + 2)}))
                           (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))) G`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2GC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_BASE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `!i. ?Np. i < P(j + 2)
             ==> !n. Np <= n
                     ==> ?G. mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                               (IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                                      (ball(vec 0,&2 * rho(j + 2) / &15)))
                               ((top:num->A topology) ((sq:num->num) n))
                               ((atlas:num->((A->bool)#(A->real^3))->bool) (sq n))
                               (IMAGE (p2ce_F top atlas (h:num->A->real^3^3) yc rho kp
                                         (p2ce_cs P j) (sq n) (P(j + 2)))
                                  (IMAGE (kp (NUMPAIR (j + 2) i))
                                         (ball(vec 0,&2 * rho(j + 2) / &15))))
                               (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))) G`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) < P(j + 2)` THENL
     [MP_TAC(ISPECL (p2ce_std @ [`j:num`; `i:num`]) P2GE_PIECE_DIFFEO) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_THEN `Np:num->num` (LABEL_TAC "pc")) THEN
  MP_TAC(ISPECL [`Np:num->num`; `P(j + 2):num`] P2CE_NUM_BOUND) THEN
  DISCH_THEN(X_CHOOSE_TAC `BP:num`) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_INJ_LEVEL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `NI:num` (LABEL_TAC "inj")) THEN
  EXISTS_TAC `BP + NI:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ABBREV_TAC `pc = \i. IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                             (ball(vec 0,&2 * rho(j + 2) / &15))` THEN
  ABBREV_TAC `U = UNIONS {(pc:num->real^3->bool) i | i | i < P(j + 2)}` THEN
  ABBREV_TAC `Fm = p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                     (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n) (P(j + 2))` THEN
  SUBGOAL_THEN `!i. IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                          (ball(vec 0,&2 * rho(j + 2) / &15)) = pc i`
  (LABEL_TAC "pcd") THENL
   [EXPAND_TAC "pc" THEN REWRITE_TAC[]; ALL_TAC] THEN
  USE_THEN "pcd" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  (* injectivity on U *)
  SUBGOAL_THEN `!p q. p IN U /\ q IN U /\ (Fm:real^3->A) p = Fm q ==> p = q`
  (LABEL_TAC "uinj") THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`p:real^3`; `q:real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i':num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(p:real^3) IN pc (i:num)` THEN UNDISCH_TAC `(q:real^3) IN pc (i':num)` THEN
    USE_THEN "pcd" (fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "inj" MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `ball(vec 0:real^3,&2 * rho(j + 2) / &15)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      MATCH_MP_TAC(SET_RULE `!s t x:real^3. s SUBSET t /\ x IN s ==> x IN t`) THEN
      EXISTS_TAC `ball(vec 0:real^3,&2 * rho(j + 2) / &15)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      UNDISCH_TAC `(Fm:real^3->A) p = Fm q` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Fm" THEN
      REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\q:A. @p:real^3. p IN U /\ (Fm:real^3->A) p = q` THEN
  (* each piece with the global inverse *)
  SUBGOAL_THEN
   `!i:num. i < P(j + 2)
        ==> mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
              ((pc:num->real^3->bool) i)
              ((top:num->A topology) ((sq:num->num) n))
              ((atlas:num->((A->bool)#(A->real^3))->bool) (sq n))
              (IMAGE (Fm:real^3->A) (pc i)) Fm (\q:A. @p:real^3. p IN U /\ Fm p = q)`
  (LABEL_TAC "pg") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "pc" (MP_TAC o C MP (ASSUME `(i:num) < P(j + 2)`) o SPEC `i:num`) THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `BP:num` THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `G0:A->real^3`) THEN
    MATCH_MP_TAC MFD_DIFFEO_EQ THEN MAP_EVERY EXISTS_TAC [`Fm:real^3->A`; `G0:A->real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `(sq:num->num) n`] P2GE_SEQ_MFD) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_DIFFEO_MAPS) THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `(p:real^3) IN U` ASSUME_TAC THENL
     [EXPAND_TAC "U" THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN X_GEN_TAC `p':real^3` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN USE_THEN "uinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* induction over the number of pieces *)
  SUBGOAL_THEN
   `!m. 1 <= m /\ m <= P(j + 2)
        ==> mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
              (UNIONS {(pc:num->real^3->bool) i | i | i < m})
              ((top:num->A topology) ((sq:num->num) n))
              ((atlas:num->((A->bool)#(A->real^3))->bool) (sq n))
              (IMAGE (Fm:real^3->A) (UNIONS {pc i | i | i < m})) Fm
              (\q:A. @p:real^3. p IN U /\ Fm p = q)`
  MP_TAC THENL
   [INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    ASM_CASES_TAC `m = 0` THENL
     [ASM_REWRITE_TAC[P2CE_UNIONS_LT_SUC; UNION_EMPTY] THEN
      USE_THEN "pg" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[P2CE_UNIONS_LT_SUC; IMAGE_UNION] THEN
    MATCH_MP_TAC MFD_DIFFEO_GLUE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`Fm:real^3->A`; `\q:A. @p:real^3. p IN U /\ (Fm:real^3->A) p = q`;
                          `Fm:real^3->A`; `\q:A. @p:real^3. p IN U /\ (Fm:real^3->A) p = q`] THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:num->A topology`; `atlas:num->((A->bool)#(A->real^3))->bool`;
                     `h:num->A->real^3^3`; `x:num->A`; `(sq:num->num) n`] P2GE_SEQ_MFD) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "pg" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `P(j + 2):num`) THEN ASM_REWRITE_TAC[LE_REFL] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "U" THEN REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The embeddings of W j for the general levels (as in the main theorem of   *)
(* cgemb; no completeness).                                                  *)
(* ------------------------------------------------------------------------- *)

let P2GE_EMBED_LEVEL = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp j m eta.
     p2ge_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp /\ &0 < eta
     ==> ?N. !n. N <= n
                 ==> (?G. mfd_diffeo (p2cl_top (p2cg_dm rho) kp) (p2cl_atlas (p2cg_dm rho) kp)
                            (p2gc_W rho P kp j) (top(sq n)) (atlas(sq n))
                            (IMAGE (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)))
                                   (p2gc_W rho P kp j))
                            (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2))) G) /\
                     p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n) (P(j + 2)) (p2cc_xl kp) =
                     x(sq n) /\
                     (!y. y IN p2cl_top (p2cg_dm rho) kp closure_of p2gc_W rho P kp j
                          ==> lck_dist2 m
                                (metric_local (p2cl_atlas (p2cg_dm rho) kp)
                                   (chart_at (p2cl_atlas (p2cg_dm rho) kp) y)
                                   (p2cl_metric (p2cg_dm rho) kp Gl))
                                (\w. rfs_pullback (atlas (sq n))
                                       (p2ce_F top atlas h yc rho kp (p2ce_cs P j) (sq n)
                                               (P(j + 2)) o
                                        chart_inv (chart_at (p2cl_atlas (p2cg_dm rho) kp) y))
                                       (h (sq n)) w)
                                (SND(chart_at (p2cl_atlas (p2cg_dm rho) kp) y) y) < eta)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2GC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL p2ce_std P2GC_MANIFOLD) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_DIFFEO_UNION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "du")) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_BASE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "bs") o CONJUNCT2) THEN
  MP_TAC(ISPECL (p2ce_std @ [`j:num`; `m:num`; `eta:real`]) P2GE_LCK_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N3:num` (LABEL_TAC "lk")) THEN
  EXISTS_TAC `N1 + N2 + N3:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "du" (MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `G:A->real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC MFD_DIFFEO_RESTRICT THEN
    EXISTS_TAC `UNIONS {IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                              (ball(vec 0,&2 * rho(j + 2) / &15)) | i | i < P(j + 2)}` THEN
    EXISTS_TAC `IMAGE (p2ce_F (top:num->A topology) atlas h yc rho (kp:num->real^3->real^3)
                         (p2ce_cs P j) ((sq:num->num) n) (P(j + 2)))
                      (UNIONS {IMAGE ((kp:num->real^3->real^3) (NUMPAIR (j + 2) i))
                                     (ball(vec 0,&2 * rho(j + 2) / &15)) | i | i < P(j + 2)})` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3) closure_of p2gc_W rho P kp j` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_OF_SUBSET THEN MATCH_MP_TAC OPEN_IN_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(ISPECL (p2ce_std @ [`j:num`]) P2GE_COVER_PIECES) THEN ASM_REWRITE_TAC[]];
    USE_THEN "bs" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN USE_THEN "lk" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* The embeddings for given general levels (P2GB_GLUED_LIMIT in place of   *)
(* the complete limit of P2CC_COMPLETE_LIMIT; no completeness).            *)

let P2GE_EMBED = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc.
     p2gb_seq top atlas h x /\ p2gb_levels top atlas h x rho K N0 B NB P Nn yc
     ==> ?(M:(real^3)topology) atlasM g xl (W:num->real^3->bool) (sq:num->num).
           hausdorff_space M /\ smooth_manifold_atlas M atlasM /\
           riemannian_metric atlasM g /\ xl IN topspace M /\
           (!k. open_in M (W k) /\ xl IN W k /\ compact_in M (M closure_of W k) /\
                M closure_of W k SUBSET W (SUC k)) /\
           UNIONS {W k | k IN (:num)} = topspace M /\
           (!m n. m < n ==> sq m < sq n) /\
           (!j. ?Fm:num->real^3->A.
                  (?N. !n. N <= n
                           ==> (?G. mfd_diffeo M atlasM (W j) (top(sq n)) (atlas(sq n))
                                      (IMAGE (Fm n) (W j)) (Fm n) G) /\
                               Fm n xl = x(sq n)) /\
                  (!m eta.
                     &0 < eta
                     ==> ?N. !n y. N <= n /\ y IN M closure_of W j
                                   ==> lck_dist2 m
                                         (metric_local atlasM (chart_at atlasM y) g)
                                         (\z. rfs_pullback (atlas(sq n))
                                                (Fm n o chart_inv (chart_at atlasM y))
                                                (h(sq n)) z)
                                         (SND(chart_at atlasM y) y) < eta))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP P2GB_GLUED_LIMIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `sq:num->num` (X_CHOOSE_THEN `D:num#num->real^(3,3)finite_sum->real^1`
    (X_CHOOSE_THEN `Gl:num->real^3->real^3^3` (X_CHOOSE_THEN `kp:num->real^3->real^3`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `p2ge_ctx top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[p2ge_ctx]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2GE_CTX_FACTS) THEN
  MP_TAC(ISPECL p2ce_std P2GC_EXHAUST) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`p2cl_top (p2cg_dm rho) (kp:num->real^3->real^3)`;
    `p2cl_atlas (p2cg_dm rho) (kp:num->real^3->real^3)`;
    `p2cl_metric (p2cg_dm rho) (kp:num->real^3->real^3) Gl`; `p2cc_xl kp`;
    `p2gc_W rho P (kp:num->real^3->real^3)`; `sq:num->num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `p2cg_dsys top atlas (h:num->A->real^3^3) yc rho sq D` THEN
    SIMP_TAC[p2cg_dsys];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN
  EXISTS_TAC `\n. p2ce_F (top:num->A topology) atlas (h:num->A->real^3^3) yc rho
                         (kp:num->real^3->real^3) (p2ce_cs P j) ((sq:num->num) n)
                         (P(j + 2))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL (p2ce_std @ [`j:num`; `0`; `&1`]) P2GE_EMBED_LEVEL) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N:num <= n`) o SPEC `n:num`) THEN
    SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`m:num`; `eta:real`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL (p2ce_std @ [`j:num`; `m:num`; `eta:real`]) P2GE_EMBED_LEVEL) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MP (ASSUME `N:num <= n`) o SPEC `n:num`) THEN
    DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The contexts of pc_p2c_cgemb are contexts of this unit,                  *)
(* with the thresholds N0 and NB raised to Nn (P2GB_OF_BALLS).               *)
(* ------------------------------------------------------------------------- *)

let P2GE_CTX_OF_BALLS = prove
 (`!top atlas (h:num->A->real^3^3) x rho K N0 B NB P Nn yc sq D Gl kp.
     p2ce_ctx top atlas h x rho K N0 B NB P Nn yc sq D Gl kp
     ==> p2ge_ctx top atlas h x rho K (\j. MAX (N0 j) (Nn j)) B
                  (\j m. MAX (NB j m) (Nn j)) P Nn yc sq D Gl kp`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2ce_ctx; p2ge_ctx] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p2gb_seq top atlas (h:num->A->real^3^3) x` ASSUME_TAC THENL
   [UNDISCH_TAC `p2cu_seq top atlas (h:num->A->real^3^3) x` THEN
    REWRITE_TAC[p2cu_seq; p2gb_seq] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2GB_OF_BALLS THEN ASM_REWRITE_TAC[]);;

