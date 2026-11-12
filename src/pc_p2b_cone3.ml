(* ========================================================================= *)
(* Unit pc_p2b_cone3: directions at the end E of a bad tube.  Comparison     *)
(* angles at E (p2bk_eang), rays (p2bk_isray), points of a ray by level      *)
(* (p2bk_rpt), and the angle at E of two rays (p2bk_theta, the supremum of   *)
(* the comparison angles along the rays; a monotone limit by P2BK_COS_MONO). *)
(* Its triangle inequality (Bridson-Haefliger I.1.14 with a planar           *)
(* comparison triangle), the finite packing of directions (MT Lemma 10.27:   *)
(* the rays cross the central sphere of one neck, pigeonhole on the unit     *)
(* sphere) and the uniform convergence of comparison angles (Claim U) give   *)
(* the asymptotic triangle inequality for comparison angles at E.            *)
(* ========================================================================= *)

needs "src/pc_p2b_cone2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The angle context, comparison angles at E, rays and their points by       *)
(* level.                                                                    *)
(* ========================================================================= *)

let p2bk_angctx = new_definition
 `p2bk_angctx (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
              (H:real^3->B) (eps:real) (z:num->B) (es:num->real^3->B)
              (r0:real) (c:real) (r1:real) <=>
    p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\
    (!y v w. y IN topspace top /\ ~collinear {vec 0,v,w}
             ==> &0 <= mfd_sectional atlas g y v w)`;;

(* The comparison angle at E of p and q (the triangle E, p, q). *)

let p2bk_eang = new_definition
 `p2bk_eang (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
            (z:num->B) (p:B) (q:B) =
    p2bk_cang (p2bk_dend (top,atlas) g z p) (p2bk_dend (top,atlas) g z q)
              (mfd_dist (top,atlas) g p q)`;;

(* A ray from x toward E with unit initial vector u. *)

let p2bk_isray = new_definition
 `p2bk_isray (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
             (z:num->B) (c:real) (x:B) (u:real^3) <=>
    x IN topspace top /\ p2bk_dend (top,atlas) g z x < c / &2 /\
    !L. L < p2bk_dend (top,atlas) g z x ==> p2bk_rayseg (top,atlas) g z x u L`;;

(* The point of the ray at level l (dE = l), for 0 < l <= dE x. *)

let p2bk_rpt = new_definition
 `p2bk_rpt (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
           (z:num->B) (x:B) (u:real^3) (l:real) =
    mfd_geo (top,atlas) g x u (p2bk_dend (top,atlas) g z x - l)`;;

let P2BK_ANGCTX_BASIC = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1
     ==> p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\
         p2bk_endchain (top,atlas) g H eps z es r0 /\ &0 < c /\
         hausdorff_space top /\ smooth_manifold_atlas top atlas /\
         riemannian_metric atlas g /\ &0 < eps /\ eps <= &1 / &100 /\
         (!y v w. y IN topspace top /\ ~collinear {vec 0,v,w}
                  ==> &0 <= mfd_sectional atlas g y v w) /\
         (!p q. p IN topspace top /\ q IN topspace top ==> mfd_joinable (top,atlas) p q)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_angctx] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  ASM_REWRITE_TAC[]);;

let P2BK_EANG_SYM = prove
 (`!top atlas (g:B->real^3^3) z p q.
     smooth_manifold_atlas top atlas
     ==> p2bk_eang (top,atlas) g z p q = p2bk_eang (top,atlas) g z q p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bk_eang; p2bk_cang] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `p:B`; `q:B`] MFD_DIST_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  BINOP_TAC THEN REAL_ARITH_TAC);;

(* The cosine of the comparison triangle lies in [-1,1] near E, so the       *)
(* comparison angle is a genuine angle with the law of cosines.             *)

let P2BK_EANG_COS = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 p q.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p IN topspace top /\ q IN topspace top
     ==> abs((p2bk_dend (top,atlas) g z p pow 2 + p2bk_dend (top,atlas) g z q pow 2 -
              mfd_dist (top,atlas) g p q pow 2) /
             (&2 * p2bk_dend (top,atlas) g z p * p2bk_dend (top,atlas) g z q)) <= &1 /\
         cos(p2bk_eang (top,atlas) g z p q) =
         (p2bk_dend (top,atlas) g z p pow 2 + p2bk_dend (top,atlas) g z q pow 2 -
          mfd_dist (top,atlas) g p q pow 2) /
         (&2 * p2bk_dend (top,atlas) g z p * p2bk_dend (top,atlas) g z q) /\
         &0 <= p2bk_eang (top,atlas) g z p q /\ p2bk_eang (top,atlas) g z p q <= pi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `p:B`]
    P2BK_DEND_POS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `q:B`]
    P2BK_DEND_POS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_DEND_LIPSCHITZ) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_DIST_VIA_END) THEN
  ASM_REWRITE_TAC[p2bk_eang; p2bk_cang] THEN
  ABBREV_TAC `A = p2bk_dend (top,atlas) (g:B->real^3^3) z p` THEN
  ABBREV_TAC `C = p2bk_dend (top,atlas) (g:B->real^3^3) z q` THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:B->real^3^3) p q` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(A - C) <= D` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(A - C) pow 2 <= D pow 2 /\ D pow 2 <= (A + C) pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    UNDISCH_TAC `abs(A - C) <= D` THEN UNDISCH_TAC `D <= A + C` THEN
    UNDISCH_TAC `&0 <= D` THEN UNDISCH_TAC `&0 < A` THEN UNDISCH_TAC `&0 < C` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * A * C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((A pow 2 + C pow 2 - D pow 2) / (&2 * A * C)) <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    UNDISCH_TAC `(A - C) pow 2 <= D pow 2` THEN UNDISCH_TAC `D pow 2 <= (A + C) pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COS_ACS; MATCH_MP_TAC ACS_BOUNDS] THEN
  UNDISCH_TAC `abs((A pow 2 + C pow 2 - D pow 2) / (&2 * A * C)) <= &1` THEN REAL_ARITH_TAC);;

let P2BK_ACS_ANTI = prove
 (`!x y. abs x <= &1 /\ abs y <= &1 /\ y <= x ==> acs x <= acs y`,
  MESON_TAC[ACS_MONO_LE_EQ]);;

let P2BK_ISRAY_EXISTS = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ x IN topspace top /\
     p2bk_dend (top,atlas) g z x < c / &2
     ==> ?u. p2bk_isray (top,atlas) g z c x u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[p2bk_isray] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC P2BK_RAY THEN
  MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`;
                        `c:real`; `r1:real`] THEN
  ASM_REWRITE_TAC[]);;

let P2BK_RPT = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u l.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ p2bk_isray (top,atlas) g z c x u /\
     &0 < l /\ l <= p2bk_dend (top,atlas) g z x
     ==> p2bk_rpt (top,atlas) g z x u l IN topspace top /\
         p2bk_dend (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l) = l /\
         mfd_dist (top,atlas) g x (p2bk_rpt (top,atlas) g z x u l) =
         p2bk_dend (top,atlas) g z x - l /\
         p2bk_dend (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l) < c / &2 /\
         mfd_tnorm g x u = &1 /\
         real_interval[&0,p2bk_dend (top,atlas) g z x - l] SUBSET
         mfd_geo_maxint (top,atlas) g x u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_isray] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `x:B`; `u:real^3`; `p2bk_dend (top,atlas) (g:B->real^3^3) z x - l`]
    P2BK_RAY_AT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < l` THEN
    UNDISCH_TAC `l <= p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[p2bk_rpt] THEN
  UNDISCH_TAC `l <= p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
  UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x < c / &2` THEN REAL_ARITH_TAC);;

let P2BK_RPT_TOP = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ p2bk_isray (top,atlas) g z c x u
     ==> p2bk_rpt (top,atlas) g z x u (p2bk_dend (top,atlas) g z x) = x /\
         &0 < p2bk_dend (top,atlas) g z x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[p2bk_isray] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[p2bk_rpt; REAL_SUB_REFL] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `x:B`; `u:real^3`] MFD_GEO_MAXIMAL) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC P2BK_DEND_POS THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[]]);;

let P2BK_RPT_DIST = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u l m.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ p2bk_isray (top,atlas) g z c x u /\
     &0 < l /\ l <= p2bk_dend (top,atlas) g z x /\ &0 < m /\ m <= p2bk_dend (top,atlas) g z x
     ==> mfd_dist (top,atlas) g (p2bk_rpt (top,atlas) g z x u l)
                                (p2bk_rpt (top,atlas) g z x u m) = abs(l - m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_isray]) THEN
  SUBGOAL_THEN
   `!a1 b1. &0 < b1 /\ b1 <= a1 /\ a1 <= p2bk_dend (top,atlas) (g:B->real^3^3) z x
          ==> mfd_dist (top,atlas) g (p2bk_rpt (top,atlas) g z x u a1)
                                     (p2bk_rpt (top,atlas) g z x u b1) = a1 - b1`
    (LABEL_TAC "aux") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `x:B`; `u:real^3`; `a1:real`] P2BK_RPT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < b1` THEN UNDISCH_TAC `b1 <= a1:real` THEN
      REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `x:B`; `u:real^3`; `b1:real`] P2BK_RPT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `b1 <= a1:real` THEN
      UNDISCH_TAC `a1 <= p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN REAL_ARITH_TAC;
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u a1`;
                   `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u b1`] P2BK_DEND_LIPSCHITZ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `x:B`; `u:real^3`; `p2bk_dend (top,atlas) (g:B->real^3^3) z x - a1`;
                   `p2bk_dend (top,atlas) (g:B->real^3^3) z x - b1`] P2BK_GEO_SEGMENT_DIST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `real_interval[&0,p2bk_dend (top,atlas) (g:B->real^3^3) z x - b1]` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
        UNDISCH_TAC `a1 <= p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN REAL_ARITH_TAC;
        UNDISCH_TAC `b1 <= a1:real` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM p2bk_rpt] THEN STRIP_TAC THEN
    UNDISCH_TAC `abs(a1 - b1) <=
                 mfd_dist (top,atlas) (g:B->real^3^3) (p2bk_rpt (top,atlas) g z x u a1)
                                                     (p2bk_rpt (top,atlas) g z x u b1)` THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) (p2bk_rpt (top,atlas) g z x u a1)
                   (p2bk_rpt (top,atlas) g z x u b1) <=
                 (p2bk_dend (top,atlas) g z x - b1) - (p2bk_dend (top,atlas) g z x - a1)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `m <= l \/ l <= m:real`) THENL
   [USE_THEN "aux" (MP_TAC o SPECL [`l:real`; `m:real`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN UNDISCH_TAC `m <= l:real` THEN REAL_ARITH_TAC;
    USE_THEN "aux" (MP_TAC o SPECL [`m:real`; `l:real`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u l`;
                   `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u m`] MFD_DIST_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `l <= m:real` THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Monotonicity of comparison angles at E along rays, and the angle at E of  *)
(* two rays (the supremum of the comparison angles).                         *)
(* ========================================================================= *)

let P2BK_EANG_MONO1 = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u q l l'.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1 /\ p2bk_isray (top,atlas) g z c x u /\
     q IN topspace top /\ p2bk_dend (top,atlas) g z q < c / &2 /\
     &0 < l' /\ l' <= l /\ l <= p2bk_dend (top,atlas) g z x
     ==> p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l) q <=
         p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l') q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  ASM_CASES_TAC `l':real = l` THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `l:real`] P2BK_RPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < l'` THEN UNDISCH_TAC `l' <= l:real` THEN
    REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `l':real`] P2BK_RPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `l' <= l:real` THEN
    UNDISCH_TAC `l <= p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u l`; `q:B`] P2BK_EANG_COS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u l'`; `q:B`] P2BK_EANG_COS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_isray]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `q:B`;
                 `p2bk_dend (top,atlas) (g:B->real^3^3) z x - l`;
                 `p2bk_dend (top,atlas) (g:B->real^3^3) z x - l'`] P2BK_COS_MONO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < l'` THEN UNDISCH_TAC `l' <= l:real` THEN
    UNDISCH_TAC `~(l':real = l)` THEN
    UNDISCH_TAC `l <= p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM p2bk_rpt] THEN DISCH_TAC] THEN
  REWRITE_TAC[p2bk_eang; p2bk_cang] THEN MATCH_MP_TAC P2BK_ACS_ANTI THEN
  ASM_REWRITE_TAC[]);;

let P2BK_EANG_MONO2 = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 y v p m m'.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1 /\ p2bk_isray (top,atlas) g z c y v /\
     p IN topspace top /\ p2bk_dend (top,atlas) g z p < c / &2 /\
     &0 < m' /\ m' <= m /\ m <= p2bk_dend (top,atlas) g z y
     ==> p2bk_eang (top,atlas) g z p (p2bk_rpt (top,atlas) g z y v m) <=
         p2bk_eang (top,atlas) g z p (p2bk_rpt (top,atlas) g z y v m')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `z:num->B`; `p:B`; `p2bk_rpt (top,atlas) (g:B->real^3^3) z y v m`]
    P2BK_EANG_SYM) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `z:num->B`; `p:B`; `p2bk_rpt (top,atlas) (g:B->real^3^3) z y v m'`]
    P2BK_EANG_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC P2BK_EANG_MONO1 THEN
  MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`;
                        `c:real`; `r1:real`] THEN
  ASM_REWRITE_TAC[]);;

(* The angle at E of the rays (x,u) and (y,v). *)

let p2bk_theta = new_definition
 `p2bk_theta (top:B topology,atlas:((B->bool)#(B->real^3))->bool) (g:B->real^3^3)
             (z:num->B) (x:B) (u:real^3) (y:B) (v:real^3) =
    sup {p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                                   (p2bk_rpt (top,atlas) g z y v m) |
         l,m | &0 < l /\ l <= p2bk_dend (top,atlas) g z x /\
               &0 < m /\ m <= p2bk_dend (top,atlas) g z y}`;;

let P2BK_THETA_BASIC = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u y v.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\
     p2bk_isray (top,atlas) g z c x u /\ p2bk_isray (top,atlas) g z c y v
     ==> (!l m. &0 < l /\ l <= p2bk_dend (top,atlas) g z x /\
                &0 < m /\ m <= p2bk_dend (top,atlas) g z y
                ==> p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                                             (p2bk_rpt (top,atlas) g z y v m) <=
                    p2bk_theta (top,atlas) g z x u y v) /\
         (!b. (!l m. &0 < l /\ l <= p2bk_dend (top,atlas) g z x /\
                     &0 < m /\ m <= p2bk_dend (top,atlas) g z y
                     ==> p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                                                  (p2bk_rpt (top,atlas) g z y v m) <= b)
              ==> p2bk_theta (top,atlas) g z x u y v <= b) /\
         &0 <= p2bk_theta (top,atlas) g z x u y v /\
         p2bk_theta (top,atlas) g z x u y v <= pi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  SUBGOAL_THEN
   `!l m. &0 < l /\ l <= p2bk_dend (top,atlas) (g:B->real^3^3) z x /\
          &0 < m /\ m <= p2bk_dend (top,atlas) g z y
          ==> &0 <= p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                                             (p2bk_rpt (top,atlas) g z y v m) /\
              p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                                       (p2bk_rpt (top,atlas) g z y v m) <= pi`
    (LABEL_TAC "rng") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `x:B`; `u:real^3`; `l:real`] P2BK_RPT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `y:B`; `v:real^3`; `m:real`] P2BK_RPT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u l`;
                   `p2bk_rpt (top,atlas) (g:B->real^3^3) z y v m`] P2BK_EANG_COS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`] P2BK_RPT_TOP) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `y:B`; `v:real^3`] P2BK_RPT_TOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[p2bk_theta] THEN
  ABBREV_TAC
   `S = {p2bk_eang (top,atlas) (g:B->real^3^3) z (p2bk_rpt (top,atlas) g z x u l)
                                                 (p2bk_rpt (top,atlas) g z y v m) |
         l,m | &0 < l /\ l <= p2bk_dend (top,atlas) g z x /\
               &0 < m /\ m <= p2bk_dend (top,atlas) g z y}` THEN
  SUBGOAL_THEN
   `!w. w IN S <=>
        ?l m. (&0 < l /\ l <= p2bk_dend (top,atlas) (g:B->real^3^3) z x /\
               &0 < m /\ m <= p2bk_dend (top,atlas) g z y) /\
              w = p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                                           (p2bk_rpt (top,atlas) g z y v m)`
    (LABEL_TAC "mem") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `S:real->bool` SUP) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z
                    (p2bk_rpt (top,atlas) g z x u (p2bk_dend (top,atlas) g z x))
                    (p2bk_rpt (top,atlas) g z y v (p2bk_dend (top,atlas) g z y))` THEN
      USE_THEN "mem" (fun th -> REWRITE_TAC[th]) THEN
      MAP_EVERY EXISTS_TAC [`p2bk_dend (top,atlas) (g:B->real^3^3) z x`;
                            `p2bk_dend (top,atlas) (g:B->real^3^3) z y`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      EXISTS_TAC `pi` THEN USE_THEN "mem" (fun th -> REWRITE_TAC[th]) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "rng" (MP_TAC o SPECL [`l:real`; `m:real`]) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  USE_THEN "mem" (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (LABEL_TAC "lub")) THEN
  SUBGOAL_THEN
   `!l m. &0 < l /\ l <= p2bk_dend (top,atlas) (g:B->real^3^3) z x /\
          &0 < m /\ m <= p2bk_dend (top,atlas) g z y
          ==> p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                                       (p2bk_rpt (top,atlas) g z y v m) <= sup S`
    (LABEL_TAC "ub2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "ub" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`l:real`; `m:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. (!l m. &0 < l /\ l <= p2bk_dend (top,atlas) (g:B->real^3^3) z x /\
               &0 < m /\ m <= p2bk_dend (top,atlas) g z y
               ==> p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                                            (p2bk_rpt (top,atlas) g z y v m) <= b)
        ==> sup S <= b`
    (LABEL_TAC "lub2") THENL
   [REPEAT STRIP_TAC THEN USE_THEN "lub" MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "ub2" ACCEPT_TAC;
    USE_THEN "lub2" ACCEPT_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z
                  (p2bk_rpt (top,atlas) g z x u (p2bk_dend (top,atlas) g z x))
                  (p2bk_rpt (top,atlas) g z y v (p2bk_dend (top,atlas) g z y))` THEN
    CONJ_TAC THENL
     [USE_THEN "rng" (MP_TAC o SPECL [`p2bk_dend (top,atlas) (g:B->real^3^3) z x`;
                                      `p2bk_dend (top,atlas) (g:B->real^3^3) z y`]) THEN
      ASM_SIMP_TAC[REAL_LE_REFL];
      USE_THEN "ub2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]];
    USE_THEN "lub2" MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    USE_THEN "rng" (MP_TAC o SPECL [`l:real`; `m:real`]) THEN ASM_SIMP_TAC[]]);;

(* The supremum is a monotone limit: deep enough along both rays the        *)
(* comparison angles are within e of it.                                     *)

let P2BK_THETA_APPROX = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u y v e.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1 /\
     p2bk_isray (top,atlas) g z c x u /\ p2bk_isray (top,atlas) g z c y v /\ &0 < e
     ==> ?l0 m0. &0 < l0 /\ l0 <= p2bk_dend (top,atlas) g z x /\
                 &0 < m0 /\ m0 <= p2bk_dend (top,atlas) g z y /\
                 !l m. &0 < l /\ l <= l0 /\ &0 < m /\ m <= m0
                       ==> p2bk_theta (top,atlas) g z x u y v - e <
                           p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                                                    (p2bk_rpt (top,atlas) g z y v m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `y:B`; `v:real^3`]
    P2BK_THETA_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub") (CONJUNCTS_THEN2 (LABEL_TAC "lub")
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?l0 m0. (&0 < l0 /\ l0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z x /\
             &0 < m0 /\ m0 <= p2bk_dend (top,atlas) g z y) /\
            p2bk_theta (top,atlas) g z x u y v - e <
            p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l0)
                                     (p2bk_rpt (top,atlas) g z y v m0)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~Q ==> F) ==> Q`) THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`;
                                     REAL_NOT_LT]) THEN
    DISCH_TAC THEN
    USE_THEN "lub" (MP_TAC o SPEC
      `p2bk_theta (top,atlas) (g:B->real^3^3) z x u y v - e`) THEN
    ANTS_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`l:real`; `m:real`]) THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`l0:real`; `m0:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `l0:real`] P2BK_RPT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `y:B`; `v:real^3`; `m:real`] P2BK_RPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `m <= m0:real` THEN
    UNDISCH_TAC `m0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z y` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`;
                 `p2bk_rpt (top,atlas) (g:B->real^3^3) z y v m`; `l0:real`; `l:real`]
    P2BK_EANG_MONO1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `y:B`; `v:real^3`;
                 `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u l0`; `m0:real`; `m:real`]
    P2BK_EANG_MONO2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z x u y v - e <
               p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l0)
                                        (p2bk_rpt (top,atlas) g z y v m0)` THEN
  UNDISCH_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z (p2bk_rpt (top,atlas) g z x u l0)
                 (p2bk_rpt (top,atlas) g z y v m0) <=
               p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l0)
                 (p2bk_rpt (top,atlas) g z y v m)` THEN
  UNDISCH_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z (p2bk_rpt (top,atlas) g z x u l0)
                 (p2bk_rpt (top,atlas) g z y v m) <=
               p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                 (p2bk_rpt (top,atlas) g z y v m)` THEN
  REAL_ARITH_TAC);;

let P2BK_THETA_SYM = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u y v.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\
     p2bk_isray (top,atlas) g z c x u /\ p2bk_isray (top,atlas) g z c y v
     ==> p2bk_theta (top,atlas) g z x u y v = p2bk_theta (top,atlas) g z y v x u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `y:B`; `v:real^3`]
    P2BK_THETA_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `y:B`; `v:real^3`; `x:B`; `u:real^3`]
    P2BK_THETA_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub2") (CONJUNCTS_THEN2 (LABEL_TAC "lub2")
    (K ALL_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub1") (CONJUNCTS_THEN2 (LABEL_TAC "lub1")
    (K ALL_TAC))) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [USE_THEN "lub1" MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `z:num->B`; `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u l`;
                   `p2bk_rpt (top,atlas) (g:B->real^3^3) z y v m`] P2BK_EANG_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "ub2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_THEN "lub2" MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `z:num->B`; `p2bk_rpt (top,atlas) (g:B->real^3^3) z y v l`;
                   `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u m`] P2BK_EANG_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "ub1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let P2BK_THETA_REFL = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ p2bk_isray (top,atlas) g z c x u
     ==> p2bk_theta (top,atlas) g z x u x u = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `x:B`; `u:real^3`]
    P2BK_THETA_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "lub")
    STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "lub" MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `l:real`] P2BK_RPT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `m:real`] P2BK_RPT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `l:real`; `m:real`] P2BK_RPT_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[p2bk_eang; p2bk_cang; REAL_POW2_ABS] THEN
  SUBGOAL_THEN `(l pow 2 + m pow 2 - (l - m) pow 2) / (&2 * l * m) = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `~(b = &0) /\ a = b ==> a / b = &1`) THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ENTIRE] THEN UNDISCH_TAC `&0 < l` THEN UNDISCH_TAC `&0 < m` THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    REWRITE_TAC[ACS_1; REAL_LE_REFL]]);;

(* ========================================================================= *)
(* The triangle inequality for angles of rays at E (Bridson-Haefliger        *)
(* I.1.14).  A planar comparison triangle with a point on its third side,    *)
(* and the law of cosines for comparison angles at E.                        *)
(* ========================================================================= *)

let P2BK_EANG_LAW = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 p q.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p IN topspace top /\ q IN topspace top
     ==> mfd_dist (top,atlas) g p q pow 2 =
         p2bk_dend (top,atlas) g z p pow 2 + p2bk_dend (top,atlas) g z q pow 2 -
         &2 * p2bk_dend (top,atlas) g z p * p2bk_dend (top,atlas) g z q *
         cos(p2bk_eang (top,atlas) g z p q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_EANG_COS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `p:B`]
    P2BK_DEND_POS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `q:B`]
    P2BK_DEND_POS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A = p2bk_dend (top,atlas) (g:B->real^3^3) z p` THEN
  ABBREV_TAC `C = p2bk_dend (top,atlas) (g:B->real^3^3) z q` THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:B->real^3^3) p q` THEN
  ABBREV_TAC `k = cos(p2bk_eang (top,atlas) (g:B->real^3^3) z p q)` THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  UNDISCH_TAC `&0 < A` THEN UNDISCH_TAC `&0 < C` THEN CONV_TAC REAL_FIELD);;

let P2BK_EANG_DIST_UPPER = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 p q b.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p IN topspace top /\ q IN topspace top /\
     p2bk_eang (top,atlas) g z p q <= b /\ b <= pi
     ==> mfd_dist (top,atlas) g p q <=
         sqrt(p2bk_dend (top,atlas) g z p pow 2 + p2bk_dend (top,atlas) g z q pow 2 -
              &2 * p2bk_dend (top,atlas) g z p * p2bk_dend (top,atlas) g z q * cos b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_EANG_COS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `p:B`]
    P2BK_DEND_POS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `q:B`]
    P2BK_DEND_POS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `cos b <= cos(p2bk_eang (top,atlas) (g:B->real^3^3) z p q)` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_MONO_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_EANG_LAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `A = p2bk_dend (top,atlas) (g:B->real^3^3) z p` THEN
  ABBREV_TAC `C = p2bk_dend (top,atlas) (g:B->real^3^3) z q` THEN
  ABBREV_TAC `k1 = cos(p2bk_eang (top,atlas) (g:B->real^3^3) z p q)` THEN
  ABBREV_TAC `k0 = cos b` THEN
  SUBGOAL_THEN `&0 <= A * C * (k1 - k0)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `k0 <= k1` THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let P2BK_EANG_DIST_LOWER = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 p q b.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p IN topspace top /\ q IN topspace top /\
     &0 <= b /\ b < p2bk_eang (top,atlas) g z p q
     ==> sqrt(p2bk_dend (top,atlas) g z p pow 2 + p2bk_dend (top,atlas) g z q pow 2 -
              &2 * p2bk_dend (top,atlas) g z p * p2bk_dend (top,atlas) g z q * cos b) <
         mfd_dist (top,atlas) g p q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_LSQRT THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_EANG_COS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `p:B`]
    P2BK_DEND_POS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `q:B`]
    P2BK_DEND_POS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_DEND_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `abs(p2bk_dend (top,atlas) (g:B->real^3^3) z p - p2bk_dend (top,atlas) g z q) <=
                 mfd_dist (top,atlas) g p q` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `cos(p2bk_eang (top,atlas) (g:B->real^3^3) z p q) < cos b` ASSUME_TAC THENL
   [MATCH_MP_TAC COS_MONO_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_EANG_LAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `A = p2bk_dend (top,atlas) (g:B->real^3^3) z p` THEN
  ABBREV_TAC `C = p2bk_dend (top,atlas) (g:B->real^3^3) z q` THEN
  ABBREV_TAC `k1 = cos(p2bk_eang (top,atlas) (g:B->real^3^3) z p q)` THEN
  ABBREV_TAC `k0 = cos b` THEN
  SUBGOAL_THEN `&0 < A * C * (k0 - k1)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `k1 < k0` THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* A planar triangle P, X, Y with |PX| = A, |PY| = C and angle al at P, and  *)
(* the point Z of the side XY seen from P at angle b from PX: |PZ| = T.      *)

let P2BK_PLANAR = prove
 (`!A C al b.
     &0 < A /\ &0 < C /\ &0 < b /\ b < al /\ al < pi
     ==> ?t0. &0 < t0 /\ t0 <= max A C /\
             sqrt(A pow 2 + t0 pow 2 - &2 * A * t0 * cos b) +
             sqrt(t0 pow 2 + C pow 2 - &2 * t0 * C * cos(al - b)) =
             sqrt(A pow 2 + C pow 2 - &2 * A * C * cos al)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sin b /\ &0 < sin(al - b) /\ &0 < sin al` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN
    UNDISCH_TAC `&0 < b` THEN UNDISCH_TAC `b < al` THEN UNDISCH_TAC `al < pi` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S = A * sin b + C * sin(al - b)` THEN
  SUBGOAL_THEN `&0 < A * sin b /\ &0 < C * sin(al - b)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN UNDISCH_TAC `&0 < A * sin b` THEN
    UNDISCH_TAC `&0 < C * sin(al - b)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `lam = (A * sin b) / S` THEN
  ABBREV_TAC `tt = (A * C * sin al) / S` THEN
  SUBGOAL_THEN `&0 < lam /\ lam < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
      SIMP_TAC[REAL_LT_LDIV_EQ; ASSUME `&0 < S`; REAL_MUL_LID] THEN
      EXPAND_TAC "S" THEN UNDISCH_TAC `&0 < C * sin(al - b)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < tt` ASSUME_TAC THENL
   [EXPAND_TAC "tt" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = vector[A; &0]:real^2` THEN
  ABBREV_TAC `Y = vector[C * cos al; C * sin al]:real^2` THEN
  ABBREV_TAC `Z = vector[tt * cos b; tt * sin b]:real^2` THEN
  SUBGOAL_THEN `Z = (&1 - lam) % X + lam % (Y:real^2)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "Y"; "Z"] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    MAP_EVERY EXPAND_TAC ["tt"; "lam"] THEN
    SUBGOAL_THEN `~(S = &0)` MP_TAC THENL
     [UNDISCH_TAC `&0 < S` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[SIN_SUB] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `X - Z = lam % (X - Y:real^2) /\ Z - Y = (&1 - lam) % (X - Y:real^2)`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(A pow 2 + tt pow 2 - &2 * A * tt * cos b) = norm(X - Z:real^2) /\
    sqrt(tt pow 2 + C pow 2 - &2 * tt * C * cos(al - b)) = norm(Z - Y:real^2) /\
    sqrt(A pow 2 + C pow 2 - &2 * A * C * cos al) = norm(X - Y:real^2)`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[vector_norm] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY EXPAND_TAC ["X"; "Y"; "Z"] THEN
    REWRITE_TAC[DOT_2; VECTOR_2; VECTOR_SUB_COMPONENT; COS_SUB] THEN
    MP_TAC(SPEC `b:real` SIN_CIRCLE) THEN MP_TAC(SPEC `al:real` SIN_CIRCLE) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(X:real^2) = A /\ norm(Y:real^2) = C /\ norm(Z:real^2) = tt`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_EQ_SQUARE] THEN
    MAP_EVERY EXPAND_TAC ["X"; "Y"; "Z"] THEN REWRITE_TAC[DOT_2; VECTOR_2] THEN
    SIMP_TAC[REAL_LT_IMP_LE; ASSUME `&0 < A`; ASSUME `&0 < C`; ASSUME `&0 < tt`] THEN
    MP_TAC(SPEC `b:real` SIN_CIRCLE) THEN MP_TAC(SPEC `al:real` SIN_CIRCLE) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  EXISTS_TAC `tt:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((&1 - lam) % X:real^2) + norm(lam % Y:real^2)` THEN CONJ_TAC THENL
     [UNDISCH_THEN `norm(Z:real^2) = tt` (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[NORM_TRIANGLE];
      ASM_REWRITE_TAC[NORM_MUL] THEN
      SUBGOAL_THEN `abs(&1 - lam) = &1 - lam /\ abs lam = lam` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `lam < &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&1 - lam) * max A C + lam * max A C` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_MAX_MAX] THEN
        UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `lam < &1` THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ASM_REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs(&1 - lam) = &1 - lam /\ abs lam = lam` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `&0 < lam` THEN UNDISCH_TAC `lam < &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

let P2BK_THETA_TRIANGLE = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x1 u1 x2 u2 x3 u3.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1 /\
     p2bk_isray (top,atlas) g z c x1 u1 /\ p2bk_isray (top,atlas) g z c x2 u2 /\
     p2bk_isray (top,atlas) g z c x3 u3
     ==> p2bk_theta (top,atlas) g z x1 u1 x3 u3 <=
         p2bk_theta (top,atlas) g z x1 u1 x2 u2 + p2bk_theta (top,atlas) g z x2 u2 x3 u3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x1:B`; `u1:real^3`; `x2:B`; `u2:real^3`]
    P2BK_THETA_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x2:B`; `u2:real^3`; `x3:B`; `u3:real^3`]
    P2BK_THETA_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x1:B`; `u1:real^3`; `x3:B`; `u3:real^3`]
    P2BK_THETA_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `b1 = p2bk_theta (top,atlas) (g:B->real^3^3) z x1 u1 x2 u2` THEN
  ABBREV_TAC `b2 = p2bk_theta (top,atlas) (g:B->real^3^3) z x2 u2 x3 u3` THEN
  ABBREV_TAC `th = p2bk_theta (top,atlas) (g:B->real^3^3) z x1 u1 x3 u3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub23")
    (CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ub12")
    (CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ABBREV_TAC `e = (th - (b1 + b2)) / &4` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN UNDISCH_TAC `b1 + b2 < th` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x1:B`; `u1:real^3`; `x3:B`; `u3:real^3`; `e:real`]
    P2BK_THETA_APPROX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l0:real` (X_CHOOSE_THEN `m0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "app"))))))) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x2:B`; `u2:real^3`] P2BK_RPT_TOP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = min l0 (p2bk_dend (top,atlas) (g:B->real^3^3) z x2 / &2)` THEN
  ABBREV_TAC `M = min m0 (p2bk_dend (top,atlas) (g:B->real^3^3) z x2 / &2)` THEN
  SUBGOAL_THEN `&0 < L /\ L <= l0 /\ L < p2bk_dend (top,atlas) (g:B->real^3^3) z x2 /\
                &0 < M /\ M <= m0 /\ M < p2bk_dend (top,atlas) g z x2`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["L"; "M"] THEN
    UNDISCH_TAC `&0 < l0` THEN UNDISCH_TAC `&0 < m0` THEN
    UNDISCH_TAC `&0 < p2bk_dend (top,atlas) (g:B->real^3^3) z x2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x1:B`; `u1:real^3`; `L:real`] P2BK_RPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `L <= l0` THEN
    UNDISCH_TAC `l0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z x1` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x3:B`; `u3:real^3`; `M:real`] P2BK_RPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `M <= m0` THEN
    UNDISCH_TAC `m0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z x3` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  ABBREV_TAC `pa = p2bk_rpt (top,atlas) (g:B->real^3^3) z x1 u1 L` THEN
  ABBREV_TAC `pc = p2bk_rpt (top,atlas) (g:B->real^3^3) z x3 u3 M` THEN
  USE_THEN "app" (MP_TAC o SPECL [`L:real`; `M:real`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `pa:B`; `pc:B`] P2BK_EANG_COS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(SPECL [`L:real`; `M:real`; `b1 + b2 + &2 * e`; `b1 + e`] P2BK_PLANAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `th - e < p2bk_eang (top,atlas) (g:B->real^3^3) z pa pc` THEN
    UNDISCH_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z pa pc <= pi` THEN
    UNDISCH_TAC `&0 <= b1` THEN UNDISCH_TAC `&0 <= b2` THEN UNDISCH_TAC `&0 < e` THEN
    EXPAND_TAC "e" THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `t0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z x2` ASSUME_TAC THENL
   [UNDISCH_TAC `t0 <= max L M` THEN UNDISCH_TAC `L < p2bk_dend (top,atlas) (g:B->real^3^3) z x2` THEN
    UNDISCH_TAC `M < p2bk_dend (top,atlas) (g:B->real^3^3) z x2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x2:B`; `u2:real^3`; `t0:real`] P2BK_RPT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `pb = p2bk_rpt (top,atlas) (g:B->real^3^3) z x2 u2 t0` THEN
  USE_THEN "ub12" (MP_TAC o SPECL [`L:real`; `t0:real`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `L <= l0` THEN
    UNDISCH_TAC `l0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z x1` THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  USE_THEN "ub23" (MP_TAC o SPECL [`t0:real`; `M:real`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `M <= m0` THEN
    UNDISCH_TAC `m0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z x3` THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `pa:B`; `pb:B`; `b1 + e`] P2BK_EANG_DIST_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z pa pb <= b1` THEN
    UNDISCH_TAC `th - e < p2bk_eang (top,atlas) (g:B->real^3^3) z pa pc` THEN
    UNDISCH_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z pa pc <= pi` THEN
    UNDISCH_TAC `&0 <= b2` THEN UNDISCH_TAC `&0 < e` THEN
    EXPAND_TAC "e" THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `pb:B`; `pc:B`; `(b1 + b2 + &2 * e) - (b1 + e)`] P2BK_EANG_DIST_UPPER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z pb pc <= b2` THEN
    UNDISCH_TAC `th - e < p2bk_eang (top,atlas) (g:B->real^3^3) z pa pc` THEN
    UNDISCH_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z pa pc <= pi` THEN
    UNDISCH_TAC `&0 <= b1` THEN UNDISCH_TAC `&0 < e` THEN
    EXPAND_TAC "e" THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `pa:B`; `pc:B`; `b1 + b2 + &2 * e`] P2BK_EANG_DIST_LOWER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `th - e < p2bk_eang (top,atlas) (g:B->real^3^3) z pa pc` THEN
    UNDISCH_TAC `&0 <= b1` THEN UNDISCH_TAC `&0 <= b2` THEN UNDISCH_TAC `&0 < e` THEN
    EXPAND_TAC "e" THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `pa:B`; `pb:B`; `pc:B`] MFD_DIST_TRIANGLE) THEN
  ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `sqrt(L pow 2 + t0 pow 2 - &2 * L * t0 * cos(b1 + e)) +
               sqrt(t0 pow 2 + M pow 2 - &2 * t0 * M * cos((b1 + b2 + &2 * e) - (b1 + e))) =
               sqrt(L pow 2 + M pow 2 - &2 * L * M * cos(b1 + b2 + &2 * e))` THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) pa pb <=
               sqrt(L pow 2 + t0 pow 2 - &2 * L * t0 * cos(b1 + e))` THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) pb pc <=
               sqrt(t0 pow 2 + M pow 2 - &2 * t0 * M * cos((b1 + b2 + &2 * e) - (b1 + e)))` THEN
  UNDISCH_TAC `sqrt(L pow 2 + M pow 2 - &2 * L * M * cos(b1 + b2 + &2 * e)) <
               mfd_dist (top,atlas) (g:B->real^3^3) pa pc` THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Tools for the packing of directions: the neck map is Lipschitz on the     *)
(* central sphere at the scale of the neck, pigeonhole on the unit sphere,   *)
(* and rays cross the central sphere of a deeper neck.                       *)
(* ========================================================================= *)

let P2BK_SEGMENT_SPHERE_NORM = prove
 (`!p q y:real^3.
     norm p = &1 /\ norm q = &1 /\ norm(p - q) < &1 / &2 /\ y IN segment[p,q]
     ==> &1 / &2 <= norm y /\ norm y <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(&1 - u) % p + u % q:real^3 = p - u % (p - q)` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(p:real^3) - norm(u % (p - q:real^3))` THEN
    REWRITE_TAC[NORM_ARITH `norm(x:real^3) - norm(y:real^3) <= norm(x - y)`] THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    SUBGOAL_THEN `abs u * norm(p - q:real^3) <= norm(p - q)` MP_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[NORM_POS_LE] THEN UNDISCH_TAC `&0 <= u` THEN UNDISCH_TAC `u <= &1` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `norm(p - q:real^3) < &1 / &2` THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((&1 - u) % p:real^3) + norm(u % q:real^3)` THEN
    REWRITE_TAC[NORM_TRIANGLE] THEN ASM_REWRITE_TAC[NORM_MUL] THEN
    UNDISCH_TAC `&0 <= u` THEN UNDISCH_TAC `u <= &1` THEN REAL_ARITH_TAC]);;

let P2BK_LIP_ARITH = prove
 (`!a b p h n. &0 <= a /\ a <= &101 / &100 /\ &0 <= b /\ b <= &3 / &2 /\
               &0 <= p /\ p <= &315 / &100 /\ &0 <= h /\ &1 / &2 <= n
               ==> a * h * (b * p) <= &10 * h * n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a * (b * p) <= &5` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&101 / &100 * (&3 / &2 * &315 / &100)` THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a * h * (b * p) = h * (a * (b * p))` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `h * &5` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `&10 * h * n = h * (&10 * n)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&1 / &2 <= n` THEN REAL_ARITH_TAC]);;

let P2BK_LIP_ARITH2 = prove
 (`!a s h n. &0 <= a /\ a <= &101 / &100 /\ &0 <= s /\ s <= &3 /\ &0 <= h /\ &0 <= n
             ==> a * h * (s * n) <= &10 * h * n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a * s <= &10` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&101 / &100 * &3` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `a * h * (s * n) = (a * s) * (h * n) /\ &10 * h * n = &10 * (h * n)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LE_MUL]);;

(* The neck map is 10 h-Lipschitz on the central sphere (h the neck scale). *)

let P2BK_NECK_SPHERE_LIP = prove
 (`!top atlas (g:B->real^3^3) eps (x:B) e p q.
     riemannian_metric atlas g /\ rfs_neck (top,atlas) g eps x e /\ eps <= &1 / &100 /\
     p IN sphere(vec 0,&1) /\ q IN sphere(vec 0,&1)
     ==> mfd_joinable (top,atlas) (e p) (e q) /\
         mfd_dist (top,atlas) g (e p) (e q) <=
         &10 * inv(sqrt(mfd_scalar atlas g x)) * norm(p - q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [rfs_neck]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_SPHERE_0]) THEN
  SUBGOAL_THEN `&0 <= inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
    UNDISCH_TAC `&0 < mfd_scalar atlas (g:B->real^3^3) x` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sqrt(&1 + eps) /\ sqrt(&1 + eps) <= &101 / &100` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN UNDISCH_TAC `&0 < eps` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN UNDISCH_TAC `eps <= &1 / &100` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN rfs_neck_dom eps /\ (q:real^3) IN rfs_neck_dom eps`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `eps:real` APX_UNIT_SPHERE_NECK_DOM) THEN ASM_REWRITE_TAC[SUBSET; IN_SPHERE_0] THEN
    DISCH_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 / &2 <= norm(p - q:real^3)` THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `eps:real`; `x:B`; `e:real^3->B`; `p:real^3`; `q:real^3`] APX_NECK_DIST_UPPER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `eps <= &1 / &100` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[APX_SVAL_UNIT; REAL_SUB_REFL; REAL_ABS_0; REAL_ADD_LID] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x)) *
                (sqrt(&2) * pi)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BK_LIP_ARITH THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
      MP_TAC PI_POS THEN REAL_ARITH_TAC;
      MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p,q] SUBSET rfs_neck_dom eps /\
                !y:real^3. y IN segment[p,q] ==> &1 / &2 <= norm y`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> a /\ b`) THEN CONJ_TAC THENL
     [DISCH_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`p:real^3`; `q:real^3`; `y:real^3`] P2BK_SEGMENT_SPHERE_NORM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
      REWRITE_TAC[rfs_neck_dom; annulus; IN_ELIM_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 / &2` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_EXP_NEG] THEN
        SUBGOAL_THEN `&2 < exp(inv(sqrt(&2) * eps))` MP_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1 + inv(sqrt(&2) * eps)` THEN
          REWRITE_TAC[REAL_EXP_LE_X] THEN
          SUBGOAL_THEN `&1 < inv(sqrt(&2) * eps)` MP_TAC THENL
           [MATCH_MP_TAC REAL_INV_1_LT THEN CONJ_TAC THENL
             [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
              MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
              MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&3 / &2 * eps` THEN CONJ_TAC THENL
               [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
                MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;
                UNDISCH_TAC `eps <= &1 / &100` THEN REAL_ARITH_TAC]];
            REAL_ARITH_TAC];
          DISCH_TAC THEN MATCH_MP_TAC REAL_LT_LINV THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          UNDISCH_TAC `&2 < exp(inv(sqrt(&2) * eps))` THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[REAL_ARITH `&1 < x <=> &0 < x - &1`] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(sqrt(&2) * eps)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC REAL_LT_MUL THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
          MP_TAC(SPEC `inv(sqrt(&2) * eps)` REAL_EXP_LE_X) THEN REAL_ARITH_TAC]];
      REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`p:real^3`; `q:real^3`; `y:real^3`] P2BK_SEGMENT_SPHERE_NORM) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (rfs_neck_dom eps:real^3->bool)`;
                 `open_set_atlas (rfs_neck_dom eps:real^3->bool)`;
                 `rfs_neck_dom eps:real^3->bool`; `\y:real^3. y`; `p:real^3`; `q:real^3`]
    GRGD_CHART_SEGMENT) THEN
  ASM_SIMP_TAC[OPEN_SET_ATLAS; APX_NECK_DOM_OPEN; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID] THEN
  ABBREV_TAC `cs = \t. chart_inv (rfs_neck_dom eps:real^3->bool,(\y:real^3. y))
                                 (p + t % (q - p))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cin") (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  SUBGOAL_THEN `(cs:real->real^3) (&0) = p /\ cs (&1) = q` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cs" THEN CONJ_TAC THENL
     [USE_THEN "cin" (MP_TAC o SPEC `&0`); USE_THEN "cin" (MP_TAC o SPEC `&1`)] THEN
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_POS; REAL_LE_REFL] THEN
    SIMP_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_LID;
             VECTOR_ARITH `p + (q - p):real^3 = q`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (rfs_neck_dom eps:real^3->bool)`;
                 `open_set_atlas (rfs_neck_dom eps:real^3->bool)`; `cylinder_flow (&0)`;
                 `rfs_neck_dom eps:real^3->bool`; `\y:real^3. y`; `p:real^3`; `q:real^3`;
                 `&0`; `&8`; `segment[p:real^3,q]`] GRGD_SEGMENT_LENGTH_UPPER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_SET_ATLAS; APX_NECK_DOM_OPEN; RFB_OPEN_SET_ATLAS_CASES; IMAGE_ID;
                 SUBSET_REFL; RFB_OPEN_SET_RIEMANNIAN; APX_NECK_CYL_FIELD] THEN
    MAP_EVERY X_GEN_TAC [`y:real^3`; `w:real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN rfs_neck_dom eps` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RFB_OPEN_SET_METRIC_LOCAL; APX_NECK_DOM_OPEN; APX_CYL0_QUAD] THEN
    REWRITE_TAC[GSYM NORM_POW_2; REAL_MUL_LZERO] THEN
    SUBGOAL_THEN `&1 / &2 <= norm(y:real^3)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&2 / norm(y:real^3) pow 2 <= &8` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < norm(y:real^3) pow 2 /\ &1 / &4 <= norm(y:real^3) pow 2`
        STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN UNDISCH_TAC `&1 / &2 <= norm(y:real^3)` THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) pow 2` THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        UNDISCH_TAC `&1 / &4 <= norm(y:real^3) pow 2` THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `x:B`; `e:real^3->B`; `cs:real->real^3`; `&0`; `&1`]
    APX_NECK_CURVE_LENGTH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `eps <= &1 / &100` THEN REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `(e:real^3->B) o (cs:real->real^3)`; `&0`; `&1`] MFD_DIST_LE_LENGTH) THEN
  ASM_REWRITE_TAC[o_THM] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                   `(e:real^3->B) o (cs:real->real^3)`; `&0`; `&1`] MFD_C1_CURVE_JOINABLE) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x)) *
              (sqrt(&8) * dist(p:real^3,q))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `mfd_length atlas (g:B->real^3^3) ((e:real^3->B) o (cs:real->real^3)) (&0) (&1)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&1 + eps) * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x)) *
                mfd_length (open_set_atlas (rfs_neck_dom eps)) (cylinder_flow (&0))
                  (cs:real->real^3) (&0) (&1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `mfd_length (open_set_atlas (rfs_neck_dom eps)) (cylinder_flow (&0))
                   (cs:real->real^3) (&0) (&1) <= sqrt(&8) * dist(p:real^3,q)` THEN
    REWRITE_TAC[];
    REWRITE_TAC[dist] THEN MATCH_MP_TAC P2BK_LIP_ARITH2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC]]);;

(* Pigeonhole on the unit sphere: among more than N points two are within   *)
(* sig of each other (N depends only on sig).                                *)

let P2BK_SPHERE_PIGEON = prove
 (`!sig. &0 < sig
         ==> ?N. !(S:A->bool) (p:A->real^3).
                   FINITE S /\ N < CARD S /\ (!j. j IN S ==> p j IN sphere(vec 0,&1))
                   ==> ?j j'. j IN S /\ j' IN S /\ ~(j = j') /\ norm(p j - p j') < sig`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `sphere(vec 0:real^3,&1)` COMPACT_IMP_TOTALLY_BOUNDED) THEN
  REWRITE_TAC[COMPACT_SPHERE] THEN DISCH_THEN(MP_TAC o SPEC `sig / &2`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0 < sig` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `CARD(k:real^3->bool)` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. ?c. (j:A) IN S ==> c IN k /\ (p:A->real^3) j IN ball(c,sig / &2)`
    MP_TAC THENL
   [X_GEN_TAC `j:A` THEN ASM_CASES_TAC `(j:A) IN S` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sphere(vec 0:real^3,&1) SUBSET UNIONS (IMAGE (\x. ball(x,sig / &2)) k)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `(p:A->real^3) j`) THEN ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `f:A->real^3`) THEN
  SUBGOAL_THEN `~(!j j'. (j:A) IN S /\ j' IN S /\ (f:A->real^3) j = f j' ==> j = j')`
    MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`f:A->real^3`; `S:A->bool`] CARD_IMAGE_INJ) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`IMAGE (f:A->real^3) S`; `k:real^3->bool`] CARD_SUBSET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `CARD(k:real^3->bool) < CARD(S:A->bool)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:A` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j':A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `j:A` th) THEN MP_TAC(SPEC `j':A` th)) THEN
  ASM_REWRITE_TAC[IN_BALL] THEN
  UNDISCH_TAC `(f:A->real^3) j = f j'` THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC NORM_ARITH);;

(* Points of the central sphere of a neck at y are at level dE y +/- 5 h. *)

let P2BK_SPHERE_LEVEL = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 (y:B) e w.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ rfs_neck (top,atlas) g eps y e /\
     w IN IMAGE e (sphere(vec 0,&1))
     ==> y IN topspace top /\ w IN topspace top /\
         abs(p2bk_dend (top,atlas) g z w - p2bk_dend (top,atlas) g z y) <=
         &5 * inv(sqrt(mfd_scalar atlas g y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `y:B`; `e:real^3->B`; `w:B`] P2BK_SPHERE_DIAM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MFD_JOINABLE_IN_TOPSPACE o
    check (fun th -> concl th = `mfd_joinable (top,atlas:((B->bool)#(B->real^3))->bool) y w`)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y:B`; `w:B`] P2BK_DEND_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) y w <= &5 * inv(sqrt(mfd_scalar atlas g y))` THEN
  REAL_ARITH_TAC);;

(* A ray from x crosses the central sphere of every sepneck at a point y     *)
(* much nearer to E than x.                                                  *)

let P2BK_RAY_CROSSES = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 x u y e.
     p2bk_nearctx (top,atlas) g H eps z es r0 c r1 /\ p2bk_isray (top,atlas) g z c x u /\
     p2bk_sepneck (top,atlas) g H eps y e /\
     p2bk_dend (top,atlas) g z y +
     &20 * (inv(sqrt(mfd_scalar atlas g y)) + inv(sqrt(mfd_scalar atlas g x))) <
     p2bk_dend (top,atlas) g z x
     ==> ?l. &0 < l /\ l <= p2bk_dend (top,atlas) g z x /\
             p2bk_rpt (top,atlas) g z x u l IN IMAGE e (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_nearctx]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  SUBGOAL_THEN `connected_space (top:B topology) /\
                mfd_param top atlas (annulus (&1) (&2)) (H:real^3->B) /\
                IMAGE H (annulus (&1) (&2)) = topspace top` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `p2bk_endchain (top,atlas) (g:B->real^3^3) H eps z es r0` THEN
    REWRITE_TAC[p2bk_endchain; p2bk_tube] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_isray]) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`] P2BK_NEAR_SEPNECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x < c / &2` THEN
    UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `e0:real^3->B`)] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) eps x e0 /\ rfs_neck (top,atlas) g eps y e`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bk_sepneck]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:B) IN IMAGE (e0:real^3->B) (sphere(vec 0,&1)) /\ &0 < mfd_scalar atlas (g:B->real^3^3) x /\
                &0 < mfd_scalar atlas g y`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[rfs_neck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `y:B`; `e:real^3->B`] P2BK_NECK_CLOSURE_DIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x)) /\
                &0 < inv(sqrt(mfd_scalar atlas g y))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y:B`; `e:real^3->B`] P2BK_DEND_NECK_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`eps:real`; `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y))`] P2BK_EXIT_FACTOR) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `hx = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) x))` THEN
  ABBREV_TAC `hy = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y))` THEN
  SUBGOAL_THEN `&99 * hy <= p2bk_dend (top,atlas) (g:B->real^3^3) z y` ASSUME_TAC THENL
   [UNDISCH_TAC `&99 * hy <= sqrt(&1 - eps) * hy * inv eps` THEN
    UNDISCH_TAC `sqrt(&1 - eps) * hy * inv eps <= p2bk_dend (top,atlas) (g:B->real^3^3) z y` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* y is on the E side of the neck at x, the spheres are disjoint, and x is  *)
  (* on the inner side of the neck at y                                       *)
  SUBGOAL_THEN `p2bk_out top H (e0:real^3->B) y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `x:B`; `e0:real^3->B`] P2BK_SEPNECK_SIDES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:B` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                     `x:B`; `e0:real^3->B`; `y:B`] P2BK_SPHERE_LEVEL) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y + &20 * (hy + hx) <
                   p2bk_dend (top,atlas) g z x` THEN
      UNDISCH_TAC `&0 < hy` THEN UNDISCH_TAC `&0 < hx` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `x:B`; `e0:real^3->B`; `y:B`] P2BK_DEND_CROSS_UPPER) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `y:B`; `x:B`] MFD_DIST_POS_LE) THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y + &20 * (hy + hx) <
                 p2bk_dend (top,atlas) g z x` THEN
    UNDISCH_TAC `&0 < hy` THEN UNDISCH_TAC `&0 < hx` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (e:real^3->B) (sphere(vec 0,&1))) (IMAGE (e0:real^3->B) (sphere(vec 0,&1)))`
    ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `DISJOINT (s:B->bool) t <=> !w. w IN s /\ w IN t ==> F`] THEN
    X_GEN_TAC `w:B` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `x:B`; `e0:real^3->B`; `w:B`] P2BK_SPHERE_LEVEL) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `y:B`; `e:real^3->B`; `w:B`] P2BK_SPHERE_LEVEL) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y + &20 * (hy + hx) <
                 p2bk_dend (top,atlas) g z x` THEN
    UNDISCH_TAC `&0 < hy` THEN UNDISCH_TAC `&0 < hx` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `x:B`; `e0:real^3->B`; `y:B`; `e:real^3->B`]
    P2BK_NEST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:B` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* a deep point of the ray is on the E side of the neck at y *)
  ABBREV_TAC `lp = (p2bk_dend (top,atlas) (g:B->real^3^3) z y - &10 * hy) / &2` THEN
  SUBGOAL_THEN `&0 < lp /\ lp < p2bk_dend (top,atlas) (g:B->real^3^3) z x` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lp" THEN
    UNDISCH_TAC `&99 * hy <= p2bk_dend (top,atlas) (g:B->real^3^3) z y` THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y + &20 * (hy + hx) <
                 p2bk_dend (top,atlas) g z x` THEN
    UNDISCH_TAC `&0 < hy` THEN UNDISCH_TAC `&0 < hx` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `lp:real`] P2BK_RPT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; STRIP_TAC] THEN
  SUBGOAL_THEN `p2bk_out top H (e:real^3->B) (p2bk_rpt (top,atlas) (g:B->real^3^3) z x u lp)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `y:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u lp` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                     `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                     `y:B`; `e:real^3->B`; `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u lp`]
        P2BK_SPHERE_LEVEL) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(p2bk_dend (top,atlas) (g:B->real^3^3) z y - &10 * hy) / &2 = lp` THEN
      UNDISCH_TAC `&99 * hy <= p2bk_dend (top,atlas) (g:B->real^3^3) z y` THEN
      UNDISCH_TAC `&0 < hy` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `y:B`; `e:real^3->B`; `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u lp`]
      P2BK_DEND_CROSS_UPPER) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `p2bk_rpt (top,atlas) (g:B->real^3^3) z x u lp`; `y:B`] MFD_DIST_POS_LE) THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `(p2bk_dend (top,atlas) (g:B->real^3^3) z y - &10 * hy) / &2 = lp` THEN
    UNDISCH_TAC `&99 * hy <= p2bk_dend (top,atlas) (g:B->real^3^3) z y` THEN
    UNDISCH_TAC `&0 < hy` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the ray segment from x to the deep point meets the sphere at y *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `x:B`; `u:real^3`] MFD_GEO_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u`;
                 `mfd_geo_maxint (top,atlas) (g:B->real^3^3) x u`; `&0`;
                 `p2bk_dend (top,atlas) (g:B->real^3^3) z x - lp`] MFD_GEODESIC_C1_CURVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `lp < p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN
    REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`;
                 `mfd_geo (top,atlas) (g:B->real^3^3) x u`; `&0`;
                 `p2bk_dend (top,atlas) (g:B->real^3^3) z x - lp`;
                 `IMAGE (e:real^3->B) (sphere(vec 0,&1))`] P2BK_CURVE_MEETS_SEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `lp < p2bk_dend (top,atlas) (g:B->real^3^3) z x` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `y:B`; `e:real^3->B`] P2BK_SEPNECK_SIDES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[GSYM p2bk_rpt];
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z x - t` THEN
  ASM_REWRITE_TAC[p2bk_rpt; REAL_ARITH `a - (a - t) = t:real`] THEN
  UNDISCH_TAC `&0 <= t` THEN UNDISCH_TAC `t <= p2bk_dend (top,atlas) (g:B->real^3^3) z x - lp` THEN
  UNDISCH_TAC `&0 < lp` THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Finite packing of directions at E (MT Lemma 10.27): rays pairwise at      *)
(* angle >= d at E are boundedly many.  All of them cross the central sphere *)
(* of one deep neck; two crossing points are close by the pigeonhole, so     *)
(* their comparison angle at E is small, while deep along the rays the       *)
(* comparison angles are close to the angles of the rays.                    *)
(* ========================================================================= *)

let P2BK_EANG_SMALL = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 p q a0 k.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p IN topspace top /\ q IN topspace top /\
     &0 < a0 /\ a0 <= p2bk_dend (top,atlas) g z p /\ a0 <= p2bk_dend (top,atlas) g z q /\
     &0 <= k /\ mfd_dist (top,atlas) g p q <= k * a0
     ==> &1 - k pow 2 / &2 <= cos(p2bk_eang (top,atlas) g z p q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_EANG_COS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`] P2BK_DEND_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A = p2bk_dend (top,atlas) (g:B->real^3^3) z p` THEN
  ABBREV_TAC `C = p2bk_dend (top,atlas) (g:B->real^3^3) z q` THEN
  ABBREV_TAC `D = mfd_dist (top,atlas) (g:B->real^3^3) p q` THEN
  DISCH_TAC THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(A - C) <= D` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A /\ &0 < C` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < a0` THEN UNDISCH_TAC `a0 <= A` THEN UNDISCH_TAC `a0 <= C` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `D pow 2 <= k pow 2 * (A * C)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(k * a0) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_LE_POW_2; REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * A * C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MP_TAC(SPEC `A - C:real` REAL_LE_POW_2) THEN
  UNDISCH_TAC `D pow 2 <= k pow 2 * (A * C)` THEN REAL_ARITH_TAC);;

let P2BK_COS_HALF = prove
 (`!d. &0 < d /\ d <= &1
       ==> &0 < &1 - cos(d / &2) /\ &1 - cos(d / &2) < &1 /\
           !a. &0 <= a /\ a <= pi /\ cos(d / &2) < cos a ==> a < d / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `d / &2 < pi / &2` ASSUME_TAC THENL
   [MP_TAC PI_APPROX_32 THEN UNDISCH_TAC `d <= &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `c < &1 ==> &0 < &1 - c`) THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM COS_0] THEN MATCH_MP_TAC COS_MONO_LT THEN
    UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `d / &2 < pi / &2` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `&0 < c ==> &1 - c < &1`) THEN MATCH_MP_TAC COS_POS_PI2 THEN
    UNDISCH_TAC `&0 < d` THEN UNDISCH_TAC `d / &2 < pi / &2` THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`d / &2`; `a:real`] COS_MONO_LE) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `cos(d / &2) < cos a` THEN REAL_ARITH_TAC]]);;

let P2BK_NECK_SCALE_LEVEL = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 (y:B) e.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ rfs_neck (top,atlas) g eps y e
     ==> &0 < inv(sqrt(mfd_scalar atlas g y)) /\
         &99 * inv(sqrt(mfd_scalar atlas g y)) <= p2bk_dend (top,atlas) g z y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ENDCHAIN_BASIC) THEN
  SUBGOAL_THEN `&0 < inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN MATCH_MP_TAC SQRT_POS_LT THEN ASM_MESON_TAC[rfs_neck];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y:B`; `e:real^3->B`] P2BK_DEND_NECK_LOWER) THEN
  MP_TAC(SPECL [`eps:real`; `inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y))`] P2BK_EXIT_FACTOR) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC);;

let P2BK_FINITE_POS_MIN = prove
 (`!(W:A->bool) f. FINITE W /\ (!t. t IN W ==> &0 < f t)
                   ==> ?m. &0 < m /\ !t. t IN W ==> m <= f t`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `W:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    EXISTS_TAC `inf (IMAGE (f:A->real) W)` THEN
    MP_TAC(ISPEC `IMAGE (f:A->real) W` INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_IMAGE] THEN
    ASM_MESON_TAC[]]);;

let P2BK_DIRECTIONS_PACK = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 d.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1 /\ &0 < d
     ==> ?N. !S. FINITE S /\
                 (!r. r IN S ==> p2bk_isray (top,atlas) g z c (FST r) (SND r)) /\
                 (!r r'. r IN S /\ r' IN S /\ ~(r = r')
                         ==> d <= p2bk_theta (top,atlas) g z (FST r) (SND r) (FST r') (SND r'))
                 ==> CARD S <= N`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  ABBREV_TAC `d1 = min d (&1)` THEN
  SUBGOAL_THEN `&0 < d1 /\ d1 <= d /\ d1 <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d1" THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `d1:real` P2BK_COS_HALF) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sg = &1 - cos(d1 / &2)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cosh"))) THEN
  MP_TAC(ISPEC `sg:real` (INST_TYPE [`:B#real^3`,`:A`] P2BK_SPHERE_PIGEON)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "pig")) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `S:(B#real^3)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rays") (LABEL_TAC "sep"))) THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  (* depths along pairs of rays where the comparison angles exceed d1/2 *)
  SUBGOAL_THEN
   `!r r'. ?l0. (r:B#real^3) IN S /\ r' IN S /\ ~(r = r')
                ==> &0 < l0 /\
                    !l m. &0 < l /\ l <= l0 /\ &0 < m /\ m <= l0
                          ==> d1 / &2 < p2bk_eang (top,atlas) (g:B->real^3^3) z
                                (p2bk_rpt (top,atlas) g z (FST r) (SND r) l)
                                (p2bk_rpt (top,atlas) g z (FST r') (SND r') m)`
    MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`r:B#real^3`; `r':B#real^3`] THEN
    ASM_CASES_TAC `(r:B#real^3) IN S /\ r' IN S /\ ~(r = r')` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `FST(r:B#real^3)`; `SND(r:B#real^3)`;
                   `FST(r':B#real^3)`; `SND(r':B#real^3)`; `d1 / &2`] P2BK_THETA_APPROX) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[] THEN UNDISCH_TAC `&0 < d1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l0:real` (X_CHOOSE_THEN `m0:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `min l0 m0` THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < l0` THEN UNDISCH_TAC `&0 < m0` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    USE_THEN "sep" (MP_TAC o SPECL [`r:B#real^3`; `r':B#real^3`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`l:real`; `m:real`]) THEN ANTS_TAC THENL
     [UNDISCH_TAC `&0 < l` THEN UNDISCH_TAC `&0 < m` THEN UNDISCH_TAC `l <= min l0 m0` THEN
      UNDISCH_TAC `m <= min l0 m0` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `d <= p2bk_theta (top,atlas) (g:B->real^3^3) z (FST(r:B#real^3)) (SND r)
                      (FST(r':B#real^3)) (SND r')` THEN
      UNDISCH_TAC `d1 <= d` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `L0:B#real^3->B#real^3->real` (LABEL_TAC "depth")) THEN
  (* a common depth s1 *)
  MP_TAC(ISPECL [`{(r,r') | (r:B#real^3) IN S /\ r' IN S /\ ~(r = r')}`;
                 `\q:(B#real^3)#(B#real^3). (L0:B#real^3->B#real^3->real) (FST q) (SND q)`]
    (INST_TYPE [`:(B#real^3)#(B#real^3)`,`:A`] P2BK_FINITE_POS_MIN)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(S:(B#real^3)->bool) CROSS S` THEN
      CONJ_TAC THENL [MATCH_MP_TAC FINITE_CROSS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_CROSS] THEN SIMP_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC; FST; SND] THEN REPEAT STRIP_TAC THEN
      USE_THEN "depth" (MP_TAC o SPECL [`r:B#real^3`; `r':B#real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    REWRITE_TAC[FORALL_IN_GSPEC; FST; SND] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC)] THEN
  (* the ray starts are at level >= t1 *)
  MP_TAC(ISPECL [`S:(B#real^3)->bool`;
                 `\r:B#real^3. p2bk_dend (top,atlas) (g:B->real^3^3) z (FST r)`]
    (INST_TYPE [`:B#real^3`,`:A`] P2BK_FINITE_POS_MIN)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC P2BK_DEND_POS THEN
    MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "rays" (MP_TAC o SPEC `t:B#real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; SIMP_TAC[p2bk_isray]];
    REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC)] THEN
  (* a deep sepneck *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `min (s1 / &2) (min (&3 / &5 * t1) (c / &2))`] P2BK_DEND_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < s1` THEN UNDISCH_TAC `&0 < t1` THEN
    UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `y:B`] P2BK_NEAR_SEPNECK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z y <
                                       min (s1 / &2) (min (&3 / &5 * t1) (c / &2))` THEN
    UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `e:real^3->B`)] THEN
  SUBGOAL_THEN `rfs_neck (top,atlas) (g:B->real^3^3) eps y e` ASSUME_TAC THENL
   [ASM_MESON_TAC[p2bk_sepneck]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y:B`; `e:real^3->B`] P2BK_NECK_SCALE_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `hy = inv(sqrt(mfd_scalar atlas (g:B->real^3^3) y))` THEN STRIP_TAC THEN
  ABBREV_TAC `ly = p2bk_dend (top,atlas) (g:B->real^3^3) z y` THEN
  (* every ray crosses the central sphere of the neck at y *)
  SUBGOAL_THEN
   `!r. ?l p. (r:B#real^3) IN S
              ==> &0 < l /\ l <= p2bk_dend (top,atlas) (g:B->real^3^3) z (FST r) /\
                  p IN sphere(vec 0,&1) /\
                  (e:real^3->B) p = p2bk_rpt (top,atlas) g z (FST r) (SND r) l`
    MP_TAC THENL
   [X_GEN_TAC `r:B#real^3` THEN ASM_CASES_TAC `(r:B#real^3) IN S` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "rays" (MP_TAC o SPEC `r:B#real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [p2bk_isray]) THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `FST(r:B#real^3)`] P2BK_NEAR_SEPNECK) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z (FST(r:B#real^3)) < c / &2` THEN
      UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_TAC `ex:real^3->B`)] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `FST(r:B#real^3)`; `ex:real^3->B`] P2BK_NECK_SCALE_LEVEL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[p2bk_sepneck]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `FST(r:B#real^3)`; `SND(r:B#real^3)`; `y:B`;
                   `e:real^3->B`] P2BK_RAY_CROSSES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:B#real^3` o check (fun th ->
        can (find_term ((=) `t1:real`)) (concl th) && is_forall(concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ly < min (s1 / &2) (min (&3 / &5 * t1) (c / &2))` THEN
      UNDISCH_TAC `&99 * hy <= ly` THEN
      UNDISCH_TAC `&99 * inv(sqrt(mfd_scalar atlas (g:B->real^3^3) (FST(r:B#real^3)))) <=
                   p2bk_dend (top,atlas) g z (FST r)` THEN
      UNDISCH_TAC `&0 < hy` THEN UNDISCH_TAC `&0 < t1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `lr:B#real^3->real` (X_CHOOSE_THEN `pr:B#real^3->real^3`
    (LABEL_TAC "cross"))) THEN
  (* two crossing points are close *)
  USE_THEN "pig" (MP_TAC o SPECL [`S:(B#real^3)->bool`; `pr:B#real^3->real^3`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "cross" (MP_TAC o SPEC `j:B#real^3`) THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `j:B#real^3` (X_CHOOSE_THEN `j':B#real^3` STRIP_ASSUME_TAC))] THEN
  USE_THEN "cross" (MP_TAC o SPEC `j:B#real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "cross" (MP_TAC o SPEC `j':B#real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "rays" (MP_TAC o SPEC `j:B#real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "rays" (MP_TAC o SPEC `j':B#real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `FST(j:B#real^3)`; `SND(j:B#real^3)`;
                 `(lr:B#real^3->real) j`] P2BK_RPT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `FST(j':B#real^3)`; `SND(j':B#real^3)`;
                 `(lr:B#real^3->real) j'`] P2BK_RPT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `w = p2bk_rpt (top,atlas) (g:B->real^3^3) z (FST(j:B#real^3)) (SND j) (lr j)` THEN
  ABBREV_TAC `w' = p2bk_rpt (top,atlas) (g:B->real^3^3) z (FST(j':B#real^3)) (SND j') (lr j')` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y:B`; `e:real^3->B`; `w:B`] P2BK_SPHERE_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_THEN `(e:real^3->B) (pr(j:B#real^3)) = w` (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `y:B`; `e:real^3->B`; `w':B`] P2BK_SPHERE_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_THEN `(e:real^3->B) (pr(j':B#real^3)) = w'` (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `eps:real`; `y:B`; `e:real^3->B`; `(pr:B#real^3->real^3) j`;
                 `(pr:B#real^3->real^3) j'`] P2BK_NECK_SPHERE_LIP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* deep enough: the comparison angle of w and w' exceeds d1/2 *)
  USE_THEN "depth" (MP_TAC o SPECL [`j:B#real^3`; `j':B#real^3`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(lr:B#real^3->real) j`; `(lr:B#real^3->real) j'`] o CONJUNCT2) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`j:B#real^3`; `j':B#real^3`] o check (fun th ->
      can (find_term ((=) `s1:real`)) (concl th) && is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(lr(j:B#real^3) - ly) <= &5 * hy` THEN
    UNDISCH_TAC `abs(lr(j':B#real^3) - ly) <= &5 * hy` THEN
    UNDISCH_TAC `ly < min (s1 / &2) (min (&3 / &5 * t1) (c / &2))` THEN
    UNDISCH_TAC `&99 * hy <= ly` THEN UNDISCH_TAC `&0 < hy` THEN
    UNDISCH_TAC `&0 < (lr:B#real^3->real) j` THEN UNDISCH_TAC `&0 < (lr:B#real^3->real) j'` THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  (* but the crossing points are close, so the angle is below d1/2 *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `w:B`; `w':B`; `&94 * hy`; `&10 * sg / &94`] P2BK_EANG_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < hy` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `abs(lr(j:B#real^3) - ly) <= &5 * hy` THEN UNDISCH_TAC `&99 * hy <= ly` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `abs(lr(j':B#real^3) - ly) <= &5 * hy` THEN UNDISCH_TAC `&99 * hy <= ly` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < sg` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&10 * hy * norm((pr:B#real^3->real^3) j - pr j')` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(&10 * sg / &94) * &94 * hy = &10 * hy * sg` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < hy` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `w:B`; `w':B`] P2BK_EANG_COS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  USE_THEN "cosh" (MP_TAC o SPEC `p2bk_eang (top,atlas) (g:B->real^3^3) z w w'`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `sg pow 2 <= sg` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    UNDISCH_TAC `&1 - (&10 * sg / &94) pow 2 / &2 <= cos(p2bk_eang (top,atlas) (g:B->real^3^3) z w w')` THEN
    UNDISCH_TAC `&1 - cos(d1 / &2) = sg` THEN UNDISCH_TAC `sg pow 2 <= sg` THEN
    UNDISCH_TAC `&0 < sg` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `d1 / &2 < p2bk_eang (top,atlas) (g:B->real^3^3) z w w'` THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* Maximal separated families of rays, the uniform convergence of comparison *)
(* angles at E (Claim U), and the asymptotic triangle inequality for         *)
(* comparison angles at E at comparable small scales.                        *)
(* ========================================================================= *)

let P2BK_ACS_UNIF = prove
 (`!e. &0 < e
       ==> ?d. &0 < d /\
               !x y. abs x <= &1 /\ abs y <= &1 /\ abs(x - y) < d
                     ==> abs(acs x - acs y) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`acs`; `real_interval[-- &1,&1]`] REAL_COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_ACS THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_uniformly_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:real`; `x:real`]) THEN ANTS_TAC THENL
   [UNDISCH_TAC `abs x <= &1` THEN UNDISCH_TAC `abs y <= &1` THEN
    UNDISCH_TAC `abs(x - y) < d` THEN REAL_ARITH_TAC;
    SIMP_TAC[]]);;

let P2BK_COS_GAP = prove
 (`!t. &2 * (&1 - cos t) <= t pow 2`,
  GEN_TAC THEN MP_TAC(SPEC `t / &2` COS_DOUBLE_SIN) THEN
  REWRITE_TAC[REAL_ARITH `&2 * t / &2 = t`] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPEC `t / &2` REAL_ABS_SIN_BOUND_LE) THEN REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
  REAL_ARITH_TAC);;

let P2BK_EANG_SAME_LEVEL = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 p q t.
     p2bk_endchain (top,atlas) g H eps z es r0 /\ p IN topspace top /\ q IN topspace top /\
     p2bk_dend (top,atlas) g z p = p2bk_dend (top,atlas) g z q /\
     p2bk_eang (top,atlas) g z p q <= t /\ t <= pi /\ &0 <= t
     ==> mfd_dist (top,atlas) g p q <= t * p2bk_dend (top,atlas) g z q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `p:B`; `q:B`; `t:real`] P2BK_EANG_DIST_UPPER) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`; `q:B`]
    P2BK_DEND_POS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `L = p2bk_dend (top,atlas) (g:B->real^3^3) z q` THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sqrt(L pow 2 + L pow 2 - &2 * L * L * cos t)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `L pow 2 * (&2 * (&1 - cos t)) <= L pow 2 * t pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2; P2BK_COS_GAP]; REAL_ARITH_TAC]);;

let P2BK_PAIRWISE_INSERT = prove
 (`!(Q:A->A->bool) a S.
     (!r r'. r IN a INSERT S /\ r' IN a INSERT S /\ Q r r' ==> Q r' r) /\
     (!r. r IN S ==> Q a r) /\
     (!r r'. r IN S /\ r' IN S /\ ~(r = r') ==> Q r r')
     ==> !r r'. r IN a INSERT S /\ r' IN a INSERT S /\ ~(r = r') ==> Q r r'`,
  REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

(* A maximal family of rays pairwise at angle >= d: every ray is within d   *)
(* of one of them.                                                           *)

let P2BK_MAXFAM = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 d.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1 /\ &0 < d
     ==> ?S. FINITE S /\
             (!r. r IN S ==> p2bk_isray (top,atlas) g z c (FST r) (SND r)) /\
             (!x u. p2bk_isray (top,atlas) g z c x u
                    ==> ?r. r IN S /\ p2bk_theta (top,atlas) g z x u (FST r) (SND r) < d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `d:real`] P2BK_DIRECTIONS_PACK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "pack")) THEN
  MP_TAC(ISPEC
   `\n. ?S:(B#real^3)->bool.
          FINITE S /\ CARD S = n /\
          (!r. r IN S ==> p2bk_isray (top,atlas) (g:B->real^3^3) z c (FST r) (SND r)) /\
          (!r r'. r IN S /\ r' IN S /\ ~(r = r')
                  ==> d <= p2bk_theta (top,atlas) g z (FST r) (SND r) (FST r') (SND r'))`
   num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN EXISTS_TAC `{}:(B#real^3)->bool` THEN
      REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; NOT_IN_EMPTY];
      EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN
      DISCH_THEN(X_CHOOSE_THEN `S:(B#real^3)->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `CARD(S:(B#real^3)->bool) = n` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      USE_THEN "pack" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `S:(B#real^3)->bool` STRIP_ASSUME_TAC) (LABEL_TAC "max"))) THEN
  EXISTS_TAC `S:(B#real^3)->bool` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `u:real^3`] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`;
                                   REAL_NOT_LT]) THEN
  DISCH_THEN(LABEL_TAC "far") THEN
  SUBGOAL_THEN `~((x:B,u:real^3) IN S)` ASSUME_TAC THENL
   [DISCH_TAC THEN USE_THEN "far" (MP_TAC o SPEC `(x:B,u:real^3)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[FST; SND]] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `x:B`; `u:real^3`] P2BK_THETA_REFL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "max" (MP_TAC o SPEC `SUC m`) THEN REWRITE_TAC[ARITH_RULE `~(SUC m <= m)`] THEN
  EXISTS_TAC `(x:B,u:real^3) INSERT S` THEN
  ASM_SIMP_TAC[FINITE_INSERT; CARD_CLAUSES] THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_INSERT; FST; SND] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
   [`\r r':B#real^3. d <= p2bk_theta (top,atlas) (g:B->real^3^3) z (FST r) (SND r)
                                         (FST r') (SND r')`;
    `(x:B,u:real^3)`; `S:(B#real^3)->bool`] P2BK_PAIRWISE_INSERT)) THEN
  REWRITE_TAC[FST; SND] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`r:B#real^3`; `r':B#real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `p2bk_isray (top,atlas) (g:B->real^3^3) z c (FST(r:B#real^3)) (SND r) /\
                  p2bk_isray (top,atlas) g z c (FST(r':B#real^3)) (SND r')`
      STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(r:B#real^3) IN (x,u) INSERT S` THEN
      UNDISCH_TAC `(r':B#real^3) IN (x,u) INSERT S` THEN REWRITE_TAC[IN_INSERT] THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FST; SND];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `FST(r:B#real^3)`; `SND(r:B#real^3)`;
                   `FST(r':B#real^3)`; `SND(r':B#real^3)`] P2BK_THETA_SYM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN USE_THEN "far" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let P2BK_DIST_QUAD = prove
 (`!top atlas (g:B->real^3^3) a b a' b'.
     smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
     (!p q. p IN topspace top /\ q IN topspace top ==> mfd_joinable (top,atlas) p q) /\
     a IN topspace top /\ b IN topspace top /\ a' IN topspace top /\ b' IN topspace top
     ==> abs(mfd_dist (top,atlas) g a b - mfd_dist (top,atlas) g a' b') <=
         mfd_dist (top,atlas) g a a' + mfd_dist (top,atlas) g b b'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `a:B`; `a':B`; `b:B`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `a':B`; `b':B`; `b:B`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `a':B`; `a:B`; `b':B`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `a:B`; `b:B`; `b':B`] MFD_DIST_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `b':B`; `b:B`] MFD_DIST_SYM) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `a':B`; `a:B`] MFD_DIST_SYM) THEN
  ASM_SIMP_TAC[] THEN REAL_ARITH_TAC);;

(* The comparison cosine moves little when the distance moves little, at    *)
(* comparable levels.                                                        *)

let P2BK_COS_PERTURB = prove
 (`!l m D D' k.
     &0 < l /\ &0 < m /\ l <= &2 * m /\ m <= &2 * l /\
     &0 <= D /\ D <= l + m /\ &0 <= D' /\ D' <= l + m /\
     &0 <= k /\ abs(D - D') <= k * (l + m)
     ==> abs((l pow 2 + m pow 2 - D pow 2) / (&2 * l * m) -
             (l pow 2 + m pow 2 - D' pow 2) / (&2 * l * m)) <= &9 / &2 * k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * l * m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l pow 2 + m pow 2 - D pow 2) / (&2 * l * m) -
                (l pow 2 + m pow 2 - D' pow 2) / (&2 * l * m) =
                ((D' - D) * (D' + D)) / (&2 * l * m)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &2 * l * m` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `abs((D' - D) * (D' + D)) <= (k * (l + m)) * (&2 * (l + m))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    UNDISCH_TAC `abs(D - D') <= k * (l + m)` THEN
    UNDISCH_TAC `&0 <= D` THEN UNDISCH_TAC `&0 <= D'` THEN UNDISCH_TAC `D <= l + m` THEN
    UNDISCH_TAC `D' <= l + m` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2 * m - l) * (l - m / &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `l <= &2 * m` THEN UNDISCH_TAC `m <= &2 * l` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= k * ((&9 / &2) * l * m - (l + m) pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 <= (&2 * m - l) * (l - m / &2)` THEN REAL_ARITH_TAC;
    UNDISCH_TAC `abs((D' - D) * (D' + D)) <= (k * (l + m)) * (&2 * (l + m))` THEN
    REAL_ARITH_TAC]);;

(* Claim U: at comparable small levels the comparison angle of two points    *)
(* on rays is within dl of the angle of the rays.                            *)

let P2BK_CLAIM_U = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 dl.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1 /\ &0 < dl
     ==> ?s0. &0 < s0 /\
              !x u y v l m.
                p2bk_isray (top,atlas) g z c x u /\ p2bk_isray (top,atlas) g z c y v /\
                &0 < l /\ l <= p2bk_dend (top,atlas) g z x /\
                &0 < m /\ m <= p2bk_dend (top,atlas) g z y /\
                l <= s0 /\ m <= s0 /\ l <= &2 * m /\ m <= &2 * l
                ==> p2bk_theta (top,atlas) g z x u y v <=
                    p2bk_eang (top,atlas) g z (p2bk_rpt (top,atlas) g z x u l)
                                             (p2bk_rpt (top,atlas) g z y v m) + dl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  MP_TAC(SPEC `dl / &2` P2BK_ACS_UNIF) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `zt:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "unif"))) THEN
  ABBREV_TAC `et = min (min (dl / &8) (zt / &10)) (&1)` THEN
  SUBGOAL_THEN `&0 < et /\ et <= dl / &8 /\ et <= zt / &10 /\ et <= &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "et" THEN UNDISCH_TAC `&0 < dl` THEN UNDISCH_TAC `&0 < zt` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `et <= pi` ASSUME_TAC THENL
   [MP_TAC PI_APPROX_32 THEN UNDISCH_TAC `et <= &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `et:real`] P2BK_MAXFAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:(B#real^3)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "frays") (LABEL_TAC "cover")))) THEN
  (* depths for all pairs of the net *)
  SUBGOAL_THEN
   `!f f'. ?l0. (f:B#real^3) IN S /\ f' IN S
                ==> &0 < l0 /\ l0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z (FST f) /\
                    l0 <= p2bk_dend (top,atlas) g z (FST f') /\
                    !l m. &0 < l /\ l <= l0 /\ &0 < m /\ m <= l0
                          ==> p2bk_theta (top,atlas) g z (FST f) (SND f) (FST f') (SND f') -
                              et <
                              p2bk_eang (top,atlas) g z
                                (p2bk_rpt (top,atlas) g z (FST f) (SND f) l)
                                (p2bk_rpt (top,atlas) g z (FST f') (SND f') m)`
    MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`f:B#real^3`; `f':B#real^3`] THEN
    ASM_CASES_TAC `(f:B#real^3) IN S /\ f' IN S` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
    USE_THEN "frays" (MP_TAC o SPEC `f:B#real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "frays" (MP_TAC o SPEC `f':B#real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `FST(f:B#real^3)`; `SND(f:B#real^3)`;
                   `FST(f':B#real^3)`; `SND(f':B#real^3)`; `et:real`] P2BK_THETA_APPROX) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l0:real` (X_CHOOSE_THEN `m0:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `min l0 m0` THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < l0` THEN UNDISCH_TAC `&0 < m0` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `l0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z (FST(f:B#real^3))` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `m0 <= p2bk_dend (top,atlas) (g:B->real^3^3) z (FST(f':B#real^3))` THEN
      REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `&0 < l` THEN UNDISCH_TAC `&0 < m` THEN UNDISCH_TAC `l <= min l0 m0` THEN
      UNDISCH_TAC `m <= min l0 m0` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `L0:B#real^3->B#real^3->real` (LABEL_TAC "depth")) THEN
  MP_TAC(ISPECL [`(S:(B#real^3)->bool) CROSS S`;
                 `\q:(B#real^3)#(B#real^3). (L0:B#real^3->B#real^3->real) (FST q) (SND q)`]
    (INST_TYPE [`:(B#real^3)#(B#real^3)`,`:A`] P2BK_FINITE_POS_MIN)) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC FINITE_CROSS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_CROSS; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`f:B#real^3`; `f':B#real^3`] THEN STRIP_TAC THEN
    USE_THEN "depth" (MP_TAC o SPECL [`f:B#real^3`; `f':B#real^3`]) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_CROSS; FST; SND] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s1"))) THEN
  EXISTS_TAC `s1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `u:real^3`; `y:B`; `v:real^3`; `l:real`; `m:real`] THEN
  STRIP_TAC THEN
  (* net rays close to (x,u) and (y,v) *)
  USE_THEN "cover" (MP_TAC o SPECL [`x:B`; `u:real^3`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `f:B#real^3` STRIP_ASSUME_TAC)] THEN
  USE_THEN "cover" (MP_TAC o SPECL [`y:B`; `v:real^3`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `f':B#real^3` STRIP_ASSUME_TAC)] THEN
  USE_THEN "frays" (MP_TAC o SPEC `f:B#real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "frays" (MP_TAC o SPEC `f':B#real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "depth" (MP_TAC o SPECL [`f:B#real^3`; `f':B#real^3`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dfp"))))] THEN
  USE_THEN "s1" (MP_TAC o SPECL [`f:B#real^3`; `f':B#real^3`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the four points *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `l:real`] P2BK_RPT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `y:B`; `v:real^3`; `m:real`] P2BK_RPT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `FST(f:B#real^3)`; `SND(f:B#real^3)`; `l:real`] P2BK_RPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `l <= s1` THEN UNDISCH_TAC `s1 <= (L0:B#real^3->B#real^3->real) f f'` THEN
    UNDISCH_TAC `(L0:B#real^3->B#real^3->real) f f' <=
                 p2bk_dend (top,atlas) (g:B->real^3^3) z (FST(f:B#real^3))` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `FST(f':B#real^3)`; `SND(f':B#real^3)`; `m:real`] P2BK_RPT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `m <= s1` THEN UNDISCH_TAC `s1 <= (L0:B#real^3->B#real^3->real) f f'` THEN
    UNDISCH_TAC `(L0:B#real^3->B#real^3->real) f f' <=
                 p2bk_dend (top,atlas) (g:B->real^3^3) z (FST(f':B#real^3))` THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  (* the comparison angle of the net points is close to the angle of the net rays *)
  USE_THEN "dfp" (MP_TAC o SPECL [`l:real`; `m:real`]) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `l <= s1` THEN UNDISCH_TAC `m <= s1` THEN
    UNDISCH_TAC `s1 <= (L0:B#real^3->B#real^3->real) f f'` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  (* the angles of the rays *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `FST(f:B#real^3)`; `SND(f:B#real^3)`;
                 `y:B`; `v:real^3`] P2BK_THETA_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `FST(f:B#real^3)`; `SND(f:B#real^3)`;
                 `FST(f':B#real^3)`; `SND(f':B#real^3)`; `y:B`; `v:real^3`] P2BK_THETA_TRIANGLE) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `FST(f':B#real^3)`; `SND(f':B#real^3)`; `y:B`; `v:real^3`]
    P2BK_THETA_SYM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REPEAT DISCH_TAC THEN
  (* the points are close to the net points *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `x:B`; `u:real^3`; `FST(f:B#real^3)`; `SND(f:B#real^3)`]
    P2BK_THETA_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`l:real`; `l:real`] o CONJUNCT1) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `l <= s1` THEN UNDISCH_TAC `s1 <= (L0:B#real^3->B#real^3->real) f f'` THEN
    UNDISCH_TAC `(L0:B#real^3->B#real^3->real) f f' <=
                 p2bk_dend (top,atlas) (g:B->real^3^3) z (FST(f:B#real^3))` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `y:B`; `v:real^3`; `FST(f':B#real^3)`; `SND(f':B#real^3)`]
    P2BK_THETA_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:real`; `m:real`] o CONJUNCT1) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `m <= s1` THEN UNDISCH_TAC `s1 <= (L0:B#real^3->B#real^3->real) f f'` THEN
    UNDISCH_TAC `(L0:B#real^3->B#real^3->real) f f' <=
                 p2bk_dend (top,atlas) (g:B->real^3^3) z (FST(f':B#real^3))` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  ABBREV_TAC `a = p2bk_rpt (top,atlas) (g:B->real^3^3) z x u l` THEN
  ABBREV_TAC `b = p2bk_rpt (top,atlas) (g:B->real^3^3) z y v m` THEN
  ABBREV_TAC `a' = p2bk_rpt (top,atlas) (g:B->real^3^3) z (FST(f:B#real^3)) (SND f) l` THEN
  ABBREV_TAC `b' = p2bk_rpt (top,atlas) (g:B->real^3^3) z (FST(f':B#real^3)) (SND f') m` THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `a:B`; `a':B`; `et:real`] P2BK_EANG_SAME_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; UNDISCH_TAC `&0 < et` THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z x u (FST(f:B#real^3)) (SND f)` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `b:B`; `b':B`; `et:real`] P2BK_EANG_SAME_LEVEL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; UNDISCH_TAC `&0 < et` THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z y v (FST(f':B#real^3)) (SND f')` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  (* the comparison cosines are close, hence the comparison angles *)
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `a:B`; `b:B`; `a':B`; `b':B`] P2BK_DIST_QUAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `a:B`; `b:B`] P2BK_DIST_VIA_END) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `a':B`; `b':B`] P2BK_DIST_VIA_END) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `a:B`; `b:B`] P2BK_DEND_LIPSCHITZ) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `a':B`; `b':B`] P2BK_DEND_LIPSCHITZ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`l:real`; `m:real`; `mfd_dist (top,atlas) (g:B->real^3^3) a b`;
                `mfd_dist (top,atlas) (g:B->real^3^3) a' b'`; `et:real`] P2BK_COS_PERTURB) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `abs(l - m) <= mfd_dist (top,atlas) (g:B->real^3^3) a b` THEN
    UNDISCH_TAC `abs(l - m) <= mfd_dist (top,atlas) (g:B->real^3^3) a' b'` THEN
    UNDISCH_TAC `abs(mfd_dist (top,atlas) (g:B->real^3^3) a b - mfd_dist (top,atlas) g a' b') <=
                 mfd_dist (top,atlas) g a a' + mfd_dist (top,atlas) g b b'` THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) a a' <= et * l` THEN
    UNDISCH_TAC `mfd_dist (top,atlas) (g:B->real^3^3) b b' <= et * m` THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `a:B`; `b:B`] P2BK_EANG_COS) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `a':B`; `b':B`] P2BK_EANG_COS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `abs(p2bk_eang (top,atlas) (g:B->real^3^3) z a' b' - p2bk_eang (top,atlas) g z a b)
                < dl / &2` ASSUME_TAC THENL
   [REWRITE_TAC[p2bk_eang; p2bk_cang] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "unif" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs((l pow 2 + m pow 2 - mfd_dist (top,atlas) (g:B->real^3^3) a b pow 2) /
                     (&2 * l * m) -
                     (l pow 2 + m pow 2 - mfd_dist (top,atlas) g a' b' pow 2) /
                     (&2 * l * m)) <= &9 / &2 * et` THEN
    UNDISCH_TAC `et <= zt / &10` THEN UNDISCH_TAC `&0 < zt` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `abs(p2bk_eang (top,atlas) (g:B->real^3^3) z a' b' - p2bk_eang (top,atlas) g z a b)
               < dl / &2` THEN
  UNDISCH_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z (FST(f:B#real^3)) (SND f)
                 (FST(f':B#real^3)) (SND f') - et < p2bk_eang (top,atlas) g z a' b'` THEN
  UNDISCH_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z (FST(f:B#real^3)) (SND f) y v <=
               p2bk_theta (top,atlas) g z (FST f) (SND f) (FST(f':B#real^3)) (SND f') +
               p2bk_theta (top,atlas) g z y v (FST f') (SND f')` THEN
  UNDISCH_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z x u y v <=
               p2bk_theta (top,atlas) g z x u (FST(f:B#real^3)) (SND f) +
               p2bk_theta (top,atlas) g z (FST f) (SND f) y v` THEN
  UNDISCH_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z x u (FST(f:B#real^3)) (SND f) < et` THEN
  UNDISCH_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z y v (FST(f':B#real^3)) (SND f') < et` THEN
  UNDISCH_TAC `et <= dl / &8` THEN REAL_ARITH_TAC);;

(* The asymptotic triangle inequality for comparison angles at E. *)

let P2BK_EANG_TRIANGLE_ASYM = prove
 (`!top atlas (g:B->real^3^3) H eps z es r0 c r1 dl.
     p2bk_angctx (top,atlas) g H eps z es r0 c r1 /\ &0 < dl
     ==> ?s0. &0 < s0 /\
              !a b q. a IN topspace top /\ b IN topspace top /\ q IN topspace top /\
                      p2bk_dend (top,atlas) g z a <= s0 /\
                      p2bk_dend (top,atlas) g z b <= s0 /\
                      p2bk_dend (top,atlas) g z q <= s0 /\
                      p2bk_dend (top,atlas) g z a <= &2 * p2bk_dend (top,atlas) g z b /\
                      p2bk_dend (top,atlas) g z b <= &2 * p2bk_dend (top,atlas) g z a /\
                      p2bk_dend (top,atlas) g z b <= &2 * p2bk_dend (top,atlas) g z q /\
                      p2bk_dend (top,atlas) g z q <= &2 * p2bk_dend (top,atlas) g z b
                      ==> p2bk_eang (top,atlas) g z a q <=
                          p2bk_eang (top,atlas) g z a b + p2bk_eang (top,atlas) g z b q + dl`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP P2BK_ANGCTX_BASIC) THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `dl / &2`] P2BK_CLAIM_U) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < dl` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "U"))) THEN
  EXISTS_TAC `min s1 (c / &4)` THEN CONJ_TAC THENL
   [UNDISCH_TAC `&0 < s1` THEN UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:B`; `b:B`; `q:B`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!p:B. p IN topspace top /\ p2bk_dend (top,atlas) (g:B->real^3^3) z p <= min s1 (c / &4)
          ==> ?w. p2bk_isray (top,atlas) g z c p w /\
                  p2bk_rpt (top,atlas) g z p w (p2bk_dend (top,atlas) g z p) = p /\
                  &0 < p2bk_dend (top,atlas) g z p`
    (LABEL_TAC "rayof") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                   `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                   `c:real`; `r1:real`; `p:B`] P2BK_ISRAY_EXISTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z p <= min s1 (c / &4)` THEN
      UNDISCH_TAC `&0 < c` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC P2BK_RPT_TOP THEN
      MAP_EVERY EXISTS_TAC [`H:real^3->B`; `eps:real`; `es:num->real^3->B`; `r0:real`;
                            `c:real`; `r1:real`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "rayof" (MP_TAC o SPEC `a:B`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `ua:real^3` STRIP_ASSUME_TAC)] THEN
  USE_THEN "rayof" (MP_TAC o SPEC `b:B`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `ub:real^3` STRIP_ASSUME_TAC)] THEN
  USE_THEN "rayof" (MP_TAC o SPEC `q:B`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `uq:real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `a:B`; `ua:real^3`; `q:B`; `uq:real^3`] P2BK_THETA_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`p2bk_dend (top,atlas) (g:B->real^3^3) z a`;
                             `p2bk_dend (top,atlas) (g:B->real^3^3) z q`] o CONJUNCT1) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:B topology`; `atlas:((B->bool)#(B->real^3))->bool`; `g:B->real^3^3`;
                 `H:real^3->B`; `eps:real`; `z:num->B`; `es:num->real^3->B`; `r0:real`;
                 `c:real`; `r1:real`; `a:B`; `ua:real^3`; `b:B`; `ub:real^3`; `q:B`; `uq:real^3`]
    P2BK_THETA_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  USE_THEN "U" (MP_TAC o SPECL [`a:B`; `ua:real^3`; `b:B`; `ub:real^3`;
                               `p2bk_dend (top,atlas) (g:B->real^3^3) z a`;
                               `p2bk_dend (top,atlas) (g:B->real^3^3) z b`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z a <= min s1 (c / &4)` THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z b <= min s1 (c / &4)` THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  USE_THEN "U" (MP_TAC o SPECL [`b:B`; `ub:real^3`; `q:B`; `uq:real^3`;
                               `p2bk_dend (top,atlas) (g:B->real^3^3) z b`;
                               `p2bk_dend (top,atlas) (g:B->real^3^3) z q`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z b <= min s1 (c / &4)` THEN
    UNDISCH_TAC `p2bk_dend (top,atlas) (g:B->real^3^3) z q <= min s1 (c / &4)` THEN
    REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  UNDISCH_TAC `p2bk_eang (top,atlas) (g:B->real^3^3) z a q <= p2bk_theta (top,atlas) g z a ua q uq` THEN
  UNDISCH_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z a ua q uq <=
               p2bk_theta (top,atlas) g z a ua b ub + p2bk_theta (top,atlas) g z b ub q uq` THEN
  UNDISCH_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z a ua b ub <=
               p2bk_eang (top,atlas) g z a b + dl / &2` THEN
  UNDISCH_TAC `p2bk_theta (top,atlas) (g:B->real^3^3) z b ub q uq <=
               p2bk_eang (top,atlas) g z b q + dl / &2` THEN
  REAL_ARITH_TAC);;

