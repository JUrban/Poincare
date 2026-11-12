(* ========================================================================= *)
(* pc_moi_s286: Moise 28.6.  Main theorem MOISE_286 : |- MOISE_286_STATEMENT *)
(* (pc_moi_core_stmt.ml).  Disjoint PL circles in the boundary torus of a PL *)
(* solid torus, none bounding a PL 2-cell there, are essential with a common *)
(* primitive displacement; in the cylinder cover they lift to periodic       *)
(* lines, and a PL exponential E maps the cylinder into the punctured plane, *)
(* where consecutive lifts are nested Jordan curves bounding a PL annulus    *)
(* (MOI_S5C_ANN2).                                                           *)
(* ========================================================================= *)

needs "src/pc_moi_s288_cov.ml";;
needs "src/pc_moi_s35_minc.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* A PL exponential E : real^2 -> real^2 DIFF {0}.  For t real and h      *)
(* real, E(t,h) = 2^floor(h) (1 + frac h) sig(psi(frac h, t)), where sig  *)
(* is the 8-periodic unit-speed map onto the square boundary and psi(u,.)  *)
(* is a PL reparametrisation fixing the odd integers.  On each cell        *)
(* [2a-1,2a+1] x [n,n+1] E is affine on three triangles (the trapezoid    *)
(* triangulation of a square annulus).  Key identities: E(t+8,h) = E(t,h), *)
(* E(t,h+1) = 2 E(t,h), and E is injective modulo (8,0).                   *)
(* ------------------------------------------------------------------------- *)

let moi_s86_psi = new_definition
 `moi_s86_psi (u:real) (t:real) =
    &2 * floor((t + &1) / &2) +
    ((t - &2 * floor((t + &1) / &2)) +
     max (--u) (min (t - &2 * floor((t + &1) / &2)) u)) / (&1 + u)`;;

let moi_s86_e = new_definition
 `moi_s86_e (x:real^2) =
    (&2 rpow floor(x$2) * (&1 + (x$2 - floor(x$2)))) %
    moi_s8c_sig (moi_s86_psi (x$2 - floor(x$2)) (x$1))`;;

let MOI_S86_PSI_CELL = prove
 (`!a u t. integer a /\ &2 * a - &1 <= t /\ t <= &2 * a + &1 /\ &0 <= u /\ u <= &1
           ==> moi_s86_psi u t =
               &2 * a + ((t - &2 * a) + max (--u) (min (t - &2 * a) u)) / (&1 + u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s86_psi] THEN
  SUBGOAL_THEN `&0 < &1 + u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t = &2 * a + &1` THENL
   [SUBGOAL_THEN `floor((t + &1) / &2) = a + &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN ASM_SIMP_TAC[INTEGER_CLOSED] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `max (--u) (min ((&2 * a + &1) - &2 * (a + &1)) u) = --u /\
                  max (--u) (min ((&2 * a + &1) - &2 * a) u) = u`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_max; real_min] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < &1 + u` THEN CONV_TAC REAL_FIELD;
    SUBGOAL_THEN `floor((t + &1) / &2) = a` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      REFL_TAC]]);;

let MOI_S86_E_CELL = prove
 (`!a n x:real^2.
     integer a /\ integer n /\
     &2 * a - &1 <= x$1 /\ x$1 <= &2 * a + &1 /\ n <= x$2 /\ x$2 <= n + &1
     ==> moi_s86_e x =
         (&2 rpow n * (&1 + (x$2 - n))) %
         moi_s8c_sig (&2 * a + ((x$1 - &2 * a) +
                                max (--(x$2 - n)) (min (x$1 - &2 * a) (x$2 - n))) /
                               (&1 + (x$2 - n)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s86_e] THEN
  ASM_CASES_TAC `(x:real^2)$2 = n + &1` THENL
   [SUBGOAL_THEN `floor((x:real^2)$2) = n + &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `&0`; `(x:real^2)$1`] MOI_S86_PSI_CELL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `max (--(&0)) (min ((x:real^2)$1 - &2 * a) (&0)) = &0 /\
                  max (--((n + &1) - n)) (min ((x:real^2)$1 - &2 * a) ((n + &1) - n)) =
                  x$1 - &2 * a`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[real_max; real_min] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 rpow (n + &1) = &2 rpow n * &2` SUBST1_TAC THENL
     [SIMP_TAC[RPOW_ADD; REAL_ARITH `&0 < &2`] THEN REWRITE_TAC[RPOW_POW; REAL_POW_1];
      ALL_TAC] THEN
    BINOP_TAC THENL [REAL_ARITH_TAC; AP_TERM_TAC THEN CONV_TAC REAL_FIELD];
    SUBGOAL_THEN `floor((x:real^2)$2) = n` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC MOI_S86_PSI_CELL THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S86_DIV_RANGE = prove
 (`!a N D. &0 < D /\ abs N <= D
           ==> &2 * a - &1 <= &2 * a + N / D /\ &2 * a + N / D <= &2 * a + &1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `&2 * a - &1 <= &2 * a + x <=> -- &1 <= x`;
              REAL_ARITH `&2 * a + x <= &2 * a + &1 <=> x <= &1`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC);;

let MOI_S86_E_CELL_AFF = prove
 (`!a n (A:real^2) B.
     integer a /\ integer n /\
     (!t. &2 * a - &1 <= t /\ t <= &2 * a + &1 ==> moi_s8c_sig t = t % A + B)
     ==> !x:real^2. &2 * a - &1 <= x$1 /\ x$1 <= &2 * a + &1 /\ n <= x$2 /\ x$2 <= n + &1
                    ==> moi_s86_e x =
                        (&2 rpow n) %
                        (((&1 + (x$2 - n)) * &2 * a +
                          ((x$1 - &2 * a) +
                           max (--(x$2 - n)) (min (x$1 - &2 * a) (x$2 - n)))) % A +
                         (&1 + (x$2 - n)) % B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `n:real`; `x:real^2`] MOI_S86_E_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + ((x:real^2)$2 - n)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(((x:real^2)$1 - &2 * a) + max (--(x$2 - n)) (min (x$1 - &2 * a) (x$2 - n))) <=
    &1 + (x$2 - n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_max; real_min] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM((fun th ->
    W(fun (_,w) -> MP_TAC(SPEC (rand(rand(lhs w))) th))) o
    check (fun th -> is_forall (concl th))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_S86_DIV_RANGE THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  UNDISCH_TAC `&0 < &1 + ((x:real^2)$2 - n)` THEN CONV_TAC REAL_FIELD);;

let MOI_S86_LIN = prove
 (`!c p q (A:real^2) B. linear (\x:real^2. c % ((p * x$2 + q * x$1) % A + x$2 % B))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[linear] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  CONJ_TAC THEN CONV_TAC REAL_RING);;

let moi_s86_tri = new_definition
 `moi_s86_tri (a:real) (n:real) (k:num) =
    interval[vector[&2 * a - &1; n]:real^2,vector[&2 * a + &1; n + &1]] INTER
    (if k = 0 then {x:real^2 | vector[&1;&1] dot x <= &2 * a + n}
     else if k = 1 then {x:real^2 | vector[-- &1;-- &1] dot x <= --(&2 * a + n)} INTER
                        {x:real^2 | vector[&1;-- &1] dot x <= &2 * a - n}
     else {x:real^2 | vector[-- &1;&1] dot x <= n - &2 * a})`;;

let MOI_S86_TRI_POLYTOPE = prove
 (`!a n k. polytope(moi_s86_tri a n k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s86_tri] THEN
  MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN REWRITE_TAC[POLYTOPE_INTERVAL] THEN
  REPEAT COND_CASES_TAC THEN
  SIMP_TAC[POLYHEDRON_INTER; POLYHEDRON_HALFSPACE_LE]);;

let MOI_S86_IN_TRI = prove
 (`!a n k x:real^2.
     x IN moi_s86_tri a n k <=>
     (&2 * a - &1 <= x$1 /\ x$1 <= &2 * a + &1 /\ n <= x$2 /\ x$2 <= n + &1) /\
     (if k = 0 then (x$1 - &2 * a) + (x$2 - n) <= &0
      else if k = 1 then --(x$2 - n) <= x$1 - &2 * a /\ x$1 - &2 * a <= x$2 - n
      else x$2 - n <= x$1 - &2 * a)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s86_tri; IN_INTER; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2] THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
  TRY(ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; DOT_2; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_S86_E_TRI_AFFINE = prove
 (`!a n k. integer a /\ integer n
           ==> ?l y. linear l /\
                     !x:real^2. x IN moi_s86_tri a n k ==> moi_s86_e x = l x + y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `a:real` MOI_S8C_SIG_AFFINE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^2` (X_CHOOSE_TAC `B:real^2`)) THEN
  MP_TAC(SPECL [`a:real`; `n:real`; `A:real^2`; `B:real^2`] MOI_S86_E_CELL_AFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[MOI_S86_IN_TRI] THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `\x:real^2. (&2 rpow n) %
                  (((&2 * a - &1) * x$2 + &1 * x$1) % (A:real^2) + x$2 % B)` THEN
    EXISTS_TAC `(&2 rpow n) % ((n - &2 * a * n) % (A:real^2) + (&1 - n) % B)` THEN
    CONJ_TAC THENL [REWRITE_TAC[MOI_S86_LIN]; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `max (--((x:real^2)$2 - n)) (min (x$1 - &2 * a) (x$2 - n)) = --(x$2 - n)`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_max; real_min] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    CONJ_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `\x:real^2. (&2 rpow n) %
                  (((&2 * a) * x$2 + &2 * x$1) % (A:real^2) + x$2 % B)` THEN
    EXISTS_TAC `(&2 rpow n) % ((--(&2 * a) - &2 * a * n) % (A:real^2) + (&1 - n) % B)` THEN
    CONJ_TAC THENL [REWRITE_TAC[MOI_S86_LIN]; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `max (--((x:real^2)$2 - n)) (min (x$1 - &2 * a) (x$2 - n)) = x$1 - &2 * a`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_max; real_min] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    CONJ_TAC THEN CONV_TAC REAL_RING;
    EXISTS_TAC `\x:real^2. (&2 rpow n) %
                  (((&2 * a + &1) * x$2 + &1 * x$1) % (A:real^2) + x$2 % B)` THEN
    EXISTS_TAC `(&2 rpow n) % ((--(&2 * a * n) - n) % (A:real^2) + (&1 - n) % B)` THEN
    CONJ_TAC THENL [REWRITE_TAC[MOI_S86_LIN]; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `max (--((x:real^2)$2 - n)) (min (x$1 - &2 * a) (x$2 - n)) = x$2 - n`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_max; real_min] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    CONJ_TAC THEN CONV_TAC REAL_RING]);;

let MOI_S86_E_PL = prove
 (`pl_map_on (:real^2) moi_s86_e`,
  ONCE_REWRITE_TAC[PL_MAP_ON_LOCAL] THEN REWRITE_TAC[IN_UNIV; INTER_UNIV] THEN
  X_GEN_TAC `x:real^2` THEN
  EXISTS_TAC `ball(x:real^2,&1 / &2)` THEN
  REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_ARITH `&0 < &1 / &2`] THEN
  ABBREV_TAC `a0 = floor(((x:real^2)$1 + &1) / &2)` THEN
  ABBREV_TAC `n0 = floor((x:real^2)$2)` THEN
  SUBGOAL_THEN `integer a0 /\ a0 <= ((x:real^2)$1 + &1) / &2 /\ (x$1 + &1) / &2 < a0 + &1 /\
                integer n0 /\ n0 <= x$2 /\ x$2 < n0 + &1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a0"; "n0"] THEN REWRITE_TAC[FLOOR]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE (\p:real#real#num. moi_s86_tri (FST p) (FST(SND p)) (SND(SND p)))
                        ({a0 - &1, a0, a0 + &1} CROSS {n0 - &1, n0, n0 + &1} CROSS {0,1,2}))` THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_BALL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`moi_s86_e`;
      `IMAGE (\p:real#real#num. moi_s86_tri (FST p) (FST(SND p)) (SND(SND p)))
             ({a0 - &1, a0, a0 + &1} CROSS {n0 - &1, n0, n0 + &1} CROSS {0,1,2})`]
      MOI_REAL_PIECEWISE_AFFINE_UNIONS) THEN
    ANTS_TAC THENL
     [SIMP_TAC[FINITE_IMAGE; FINITE_CROSS; FINITE_INSERT; FINITE_EMPTY] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS; IN_INSERT; NOT_IN_EMPTY;
                  FST; SND] THEN
      MAP_EVERY X_GEN_TAC [`a:real`; `n:real`; `k:num`] THEN STRIP_TAC THEN
      REWRITE_TAC[MOI_S86_TRI_POLYTOPE] THEN MATCH_MP_TAC MOI_S86_E_TRI_AFFINE THEN
      ASM_SIMP_TAC[INTEGER_CLOSED];
      SIMP_TAC[]];
    REWRITE_TAC[SUBSET; IN_BALL; IN_UNIONS; EXISTS_IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS;
                IN_INSERT; NOT_IN_EMPTY; FST; SND] THEN
    X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    ABBREV_TAC `a = floor(((z:real^2)$1 + &1) / &2)` THEN
    ABBREV_TAC `n = floor((z:real^2)$2)` THEN
    SUBGOAL_THEN `integer a /\ a <= ((z:real^2)$1 + &1) / &2 /\ (z$1 + &1) / &2 < a + &1 /\
                  integer n /\ n <= z$2 /\ z$2 < n + &1` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "n"] THEN REWRITE_TAC[FLOOR]; ALL_TAC] THEN
    SUBGOAL_THEN `abs((z:real^2)$1 - (x:real^2)$1) < &1 / &2 /\ abs(z$2 - x$2) < &1 / &2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `dist(x:real^2,z) < &1 / &2` THEN REWRITE_TAC[dist] THEN
      MP_TAC(ISPECL [`x - z:real^2`; `1`] COMPONENT_LE_NORM) THEN
      MP_TAC(ISPECL [`x - z:real^2`; `2`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a = a0 - &1 \/ a = a0 \/ a = a0 + &1) /\
                  (n = n0 - &1 \/ n = n0 \/ n = n0 + &1)` ASSUME_TAC THENL
     [MP_TAC(SPEC `a - a0:real` MOI_S8C_INT_SMALL) THEN
      MP_TAC(SPEC `n - n0:real` MOI_S8C_INT_SMALL) THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `n:real`] THEN
    ASM_CASES_TAC `((z:real^2)$1 - &2 * a) + (z$2 - n) <= &0` THENL
     [EXISTS_TAC `0`;
      ASM_CASES_TAC `(z:real^2)$1 - &2 * a <= z$2 - n` THENL
       [EXISTS_TAC `1`; EXISTS_TAC `2`]] THEN
    REWRITE_TAC[MOI_S86_IN_TRI] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S86_E_CONTINUOUS = prove
 (`!s. moi_s86_e continuous_on s`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[MOI_S86_E_PL]);;

let MOI_S86_PSI_PERIODIC = prove
 (`!u t m. integer m ==> moi_s86_psi u (t + &8 * m) = moi_s86_psi u t + &8 * m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s86_psi] THEN
  SUBGOAL_THEN `floor(((t + &8 * m) + &1) / &2) = floor((t + &1) / &2) + &4 * m`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ARITH `((t + &8 * m) + &1) / &2 = (t + &1) / &2 + &4 * m`] THEN
    MATCH_MP_TAC MOI_S8C_FLOOR_ADD THEN ASM_SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(t + &8 * m) - &2 * (f + &4 * m) = t - &2 * f`] THEN
  REAL_ARITH_TAC);;

let MOI_S86_SIG_EQ = prove
 (`!s s'. moi_s8c_sig s = moi_s8c_sig s' <=> integer((s - s') / &8)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `moi_s8c_psi`) THEN
    REWRITE_TAC[MOI_S8C_PSI_SIG; MOI_S4U_EX_EQ] THEN
    REWRITE_TAC[REAL_ARITH `s / &8 - s' / &8 = (s - s') / &8`];
    DISCH_TAC THEN
    SUBGOAL_THEN `s = s' + &8 * ((s - s') / &8)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_S8C_SIG_PERIODIC]]);;

let MOI_S86_PHI_MONO = prove
 (`!u w w'. &0 <= u /\ w < w'
            ==> w + max (--u) (min w u) < w' + max (--u) (min w' u)`,
  REWRITE_TAC[real_max; real_min] THEN REAL_ARITH_TAC);;

let MOI_S86_PSI_MONO = prove
 (`!u t t'. &0 <= u /\ u <= &1 /\ t < t' ==> moi_s86_psi u t < moi_s86_psi u t'`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a = floor((t + &1) / &2)` THEN
  ABBREV_TAC `a' = floor((t' + &1) / &2)` THEN
  SUBGOAL_THEN `integer a /\ a <= (t + &1) / &2 /\ (t + &1) / &2 < a + &1 /\
                integer a' /\ a' <= (t' + &1) / &2 /\ (t' + &1) / &2 < a' + &1`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "a'"] THEN REWRITE_TAC[FLOOR]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `u:real`; `t:real`] MOI_S86_PSI_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`a':real`; `u:real`; `t':real`] MOI_S86_PSI_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `a <= a'` ASSUME_TAC THENL
   [ASM_MESON_TAC[FLOOR_MONO; REAL_ARITH `t < t' ==> (t + &1) / &2 <= (t' + &1) / &2`];
    ALL_TAC] THEN
  ASM_CASES_TAC `a':real = a` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[REAL_LT_LADD] THEN ASM_SIMP_TAC[REAL_LT_DIV2_EQ] THEN
    MATCH_MP_TAC MOI_S86_PHI_MONO THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `a + &1 <= a'` ASSUME_TAC THENL
   [MP_TAC(SPECL [`a:real`; `a':real`] REAL_LT_INTEGERS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x < &1 /\ -- &1 <= y /\ a + &1 <= a'
                           ==> &2 * a + x < &2 * a' + y`) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[real_max; real_min] THEN ASM_REAL_ARITH_TAC);;

let MOI_S86_PSI_INJ = prove
 (`!u t t'. &0 <= u /\ u <= &1 /\ moi_s86_psi u t = moi_s86_psi u t' ==> t = t'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `~(t < t') /\ ~(t' < t) ==> t = t'`) THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`u:real`; `t:real`; `t':real`] MOI_S86_PSI_MONO);
    MP_TAC(SPECL [`u:real`; `t':real`; `t:real`] MOI_S86_PSI_MONO)] THEN
  ASM_REWRITE_TAC[REAL_LT_REFL]);;

let MOI_S86_PSI_ONTO = prove
 (`!u s. &0 <= u /\ u <= &1 ==> ?t. moi_s86_psi u t = s`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a = floor((s + &1) / &2)` THEN
  SUBGOAL_THEN `integer a /\ a <= (s + &1) / &2 /\ (s + &1) / &2 < a + &1`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "a" THEN REWRITE_TAC[FLOOR]; ALL_TAC] THEN
  ABBREV_TAC `v = (s - &2 * a) * (&1 + u)` THEN
  SUBGOAL_THEN `?w. -- &1 <= w /\ w <= &1 /\ w + max (--u) (min w u) = v` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `--(&1 + u) <= v /\ v <= &1 + u` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN
      REWRITE_TAC[REAL_ARITH `--(&1 + u) <= x * (&1 + u) <=> &0 <= (x + &1) * (&1 + u)`;
                  REAL_ARITH `x * (&1 + u) <= &1 + u <=> &0 <= (&1 - x) * (&1 + u)`] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `v <= --(&2 * u)` THENL
     [EXISTS_TAC `v + u` THEN REWRITE_TAC[real_max; real_min] THEN ASM_REAL_ARITH_TAC;
      ASM_CASES_TAC `v <= &2 * u` THENL
       [EXISTS_TAC `v / &2`; EXISTS_TAC `v - u`] THEN
      REWRITE_TAC[real_max; real_min] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `&2 * a + w` THEN
  MP_TAC(SPECL [`a:real`; `u:real`; `&2 * a + w`] MOI_S86_PSI_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(&2 * a + w) - &2 * a = w`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM(ASSUME `(s - &2 * a) * (&1 + u) = v`)] THEN
  SUBGOAL_THEN `&0 < &1 + u` MP_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let MOI_S86_E_PERIODIC = prove
 (`!x:real^2 m. integer m ==> moi_s86_e (x + m % vector[&8; &0]) = moi_s86_e x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s86_e; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x + m * &8 = x + &8 * m`] THEN
  ASM_SIMP_TAC[MOI_S86_PSI_PERIODIC; MOI_S8C_SIG_PERIODIC]);;

let MOI_S86_E_SCALE = prove
 (`!x:real^2. moi_s86_e (x + vector[&0; &1]) = &2 % moi_s86_e x`,
  GEN_TAC THEN
  REWRITE_TAC[moi_s86_e; VECTOR_ADD_COMPONENT; VECTOR_2; REAL_ADD_RID] THEN
  SUBGOAL_THEN `floor((x:real^2)$2 + &1) = floor(x$2) + &1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S8C_FLOOR_ADD THEN REWRITE_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(x + &1) - (f + &1) = x - f`] THEN
  SIMP_TAC[RPOW_ADD; REAL_ARITH `&0 < &2`; RPOW_POW; REAL_POW_1] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

let MOI_S86_SIG_MAXNORM = prove
 (`!s. max (abs((moi_s8c_sig s)$1)) (abs((moi_s8c_sig s)$2)) = &1`,
  GEN_TAC THEN MP_TAC(SPEC `s:real` MOI_S8C_SIG_IN) THEN
  REWRITE_TAC[MOI_S8C_SQ] THEN REAL_ARITH_TAC);;

let MOI_S86_RADIUS_POS = prove
 (`!h. &0 < &2 rpow floor h * (&1 + (h - floor h))`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
  SIMP_TAC[RPOW_POS_LT; REAL_ARITH `&0 < &2`] THEN
  MP_TAC(SPEC `h:real` FLOOR) THEN REAL_ARITH_TAC);;

let MOI_S86_MAX_LMUL = prove
 (`!r a b. &0 < r ==> max (r * a) (r * b) = r * max a b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_max] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN COND_CASES_TAC THEN REWRITE_TAC[]);;

let MOI_S86_E_RADIUS = prove
 (`!x:real^2. max (abs((moi_s86_e x)$1)) (abs((moi_s86_e x)$2)) =
              &2 rpow floor(x$2) * (&1 + (x$2 - floor(x$2)))`,
  GEN_TAC THEN REWRITE_TAC[moi_s86_e; VECTOR_MUL_COMPONENT] THEN
  MP_TAC(SPEC `(x:real^2)$2` MOI_S86_RADIUS_POS) THEN
  SPEC_TAC(`&2 rpow floor((x:real^2)$2) * (&1 + (x$2 - floor(x$2)))`,`r:real`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ARITH `&0 < r ==> abs r = r`; MOI_S86_MAX_LMUL;
               MOI_S86_SIG_MAXNORM; REAL_MUL_RID]);;

let MOI_S86_R_INJ = prove
 (`!h h'. &2 rpow floor h * (&1 + (h - floor h)) =
          &2 rpow floor h' * (&1 + (h' - floor h'))
          ==> h = h'`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!h h'. floor h < floor h'
           ==> &2 rpow floor h * (&1 + (h - floor h)) <
               &2 rpow floor h' * (&1 + (h' - floor h'))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `floor h + &1 <= floor h'` ASSUME_TAC THENL
     [MP_TAC(SPECL [`floor h`; `floor h'`] REAL_LT_INTEGERS) THEN
      REWRITE_TAC[FLOOR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&2 rpow (floor h + &1)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[RPOW_ADD; REAL_ARITH `&0 < &2`; RPOW_POW; REAL_POW_1] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN SIMP_TAC[RPOW_POS_LT; REAL_ARITH `&0 < &2`] THEN
      MP_TAC(SPEC `h:real` FLOOR) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 rpow floor h'` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[RPOW_POS_LT; REAL_LT_IMP_LE;
          REAL_ARITH `&0 < &2`] THEN
        MP_TAC(SPEC `h':real` FLOOR) THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `floor h = floor h'` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `~(x < y) /\ ~(y < x) ==> x = y`) THEN
    CONJ_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o MATCH_MP th)) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  UNDISCH_TAC `&2 rpow floor h * (&1 + (h - floor h)) =
               &2 rpow floor h' * (&1 + (h' - floor h'))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < &2 rpow floor h'` MP_TAC THENL
   [SIMP_TAC[RPOW_POS_LT; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

let MOI_S86_E_NONZERO = prove
 (`!x:real^2. ~(moi_s86_e x = vec 0)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `x:real^2` MOI_S86_E_RADIUS) THEN
  MP_TAC(SPEC `(x:real^2)$2` MOI_S86_RADIUS_POS) THEN
  ASM_REWRITE_TAC[VEC_COMPONENT; REAL_ABS_NUM] THEN REAL_ARITH_TAC);;

let MOI_S86_E_EQ = prove
 (`!x y:real^2. moi_s86_e x = moi_s86_e y <=> x$2 = y$2 /\ integer((x$1 - y$1) / &8)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2)$2 = (y:real^2)$2` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S86_R_INJ THEN
      REWRITE_TAC[GSYM MOI_S86_E_RADIUS] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s86_e x = moi_s86_e y` THEN
    ASM_REWRITE_TAC[moi_s86_e] THEN
    MP_TAC(SPEC `(y:real^2)$2` MOI_S86_RADIUS_POS) THEN
    ABBREV_TAC `r = &2 rpow floor((y:real^2)$2) * (&1 + (y$2 - floor(y$2)))` THEN
    DISCH_TAC THEN
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ; MOI_S86_SIG_EQ] THEN
    ABBREV_TAC `u = (y:real^2)$2 - floor(y$2)` THEN
    SUBGOAL_THEN `&0 <= u /\ u <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN MP_TAC(SPEC `(y:real^2)$2` FLOOR) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `m = (moi_s86_psi u ((x:real^2)$1) - moi_s86_psi u ((y:real^2)$1)) / &8` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2)$1 = (y:real^2)$1 + &8 * m` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_S86_PSI_INJ THEN EXISTS_TAC `u:real` THEN ASM_SIMP_TAC[MOI_S86_PSI_PERIODIC] THEN
      EXPAND_TAC "m" THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `((y + &8 * m) - y) / &8 = m`] THEN FIRST_ASSUM ACCEPT_TAC;
    STRIP_TAC THEN
    SUBGOAL_THEN `x:real^2 = y + (((x:real^2)$1 - (y:real^2)$1) / &8) % vector[&8; &0]`
    SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                  VECTOR_2] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[MOI_S86_E_PERIODIC]]]);;

let MOI_S86_E_ONTO = prove
 (`!y:real^2. ~(y = vec 0) ==> ?x. moi_s86_e x = y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `rho = max (abs((y:real^2)$1)) (abs(y$2))` THEN
  SUBGOAL_THEN `&0 < rho` ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN
    UNDISCH_TAC `~(y:real^2 = vec 0)` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `n = floor(log rho / log(&2))` THEN
  SUBGOAL_THEN `integer n /\ n <= log rho / log(&2) /\ log rho / log(&2) < n + &1`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "n" THEN REWRITE_TAC[FLOOR]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 rpow (log rho / log(&2)) = rho` ASSUME_TAC THENL
   [REWRITE_TAC[rpow; REAL_ARITH `&0 < &2`] THEN
    SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; EXP_LOG];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 rpow n <= rho /\ rho < &2 rpow n * &2` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&2 rpow (n + &1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_MONO_LT THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        SIMP_TAC[RPOW_ADD; REAL_ARITH `&0 < &2`; RPOW_POW; REAL_POW_1; REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 rpow n` ASSUME_TAC THENL
   [SIMP_TAC[RPOW_POS_LT; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
  ABBREV_TAC `u = rho / &2 rpow n - &1` THEN
  SUBGOAL_THEN `&0 <= u /\ u < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x - &1 <=> &1 <= x`; REAL_ARITH `x - &1 < &1 <=> x < &2`;
                 REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 / rho) % y:real^2) IN relative_frontier(interval[--vec 1,vec 1])`
  MP_TAC THENL
   [REWRITE_TAC[MOI_S8C_SQ; VECTOR_MUL_COMPONENT] THEN
    SUBGOAL_THEN `!a. abs(&1 / rho * a) = abs a / rho` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_SYM];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_EQ_LDIV_EQ; REAL_MUL_LID] THEN
    UNDISCH_TAC `max (abs((y:real^2)$1)) (abs(y$2)) = rho` THEN
    REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S8C_SIG_ONTO) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`u:real`; `s:real`] MOI_S86_PSI_ONTO) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `t:real`)] THEN
  EXISTS_TAC `vector[t; n + u]:real^2` THEN
  REWRITE_TAC[moi_s86_e; VECTOR_2] THEN
  SUBGOAL_THEN `floor(n + u) = n` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(n + u) - n = u`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&2 rpow n * (&1 + u) = rho` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN UNDISCH_TAC `&0 < &2 rpow n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < r ==> r * &1 / r = &1`; VECTOR_MUL_LID]);;

let MOI_S86_INT_MOD4 = prove
 (`!a. integer a
       ==> ?k r. integer k /\ (r = &0 \/ r = &1 \/ r = &2 \/ r = &3) /\ a = &4 * k + r`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `floor(a / &4)` THEN
  EXISTS_TAC `a - &4 * floor(a / &4)` THEN
  REWRITE_TAC[FLOOR; REAL_ARITH `a = &4 * k + (a - &4 * k)`] THEN
  MATCH_MP_TAC MOI_S8C_INT_CASES4 THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; FLOOR] THEN
  MP_TAC(SPEC `a / &4` FLOOR) THEN REAL_ARITH_TAC);;

let MOI_S86_SIG_EVEN = prove
 (`moi_s8c_sig(&0) = vector[&1;&0] /\ moi_s8c_sig(&2) = vector[&0;&1] /\
   moi_s8c_sig(&4) = vector[-- &1;&0] /\ moi_s8c_sig(&6) = vector[&0;-- &1]`,
  REPEAT CONJ_TAC THEN
  W(fun (_,w) -> MP_TAC(SPEC (rand(lhs w)) MOI_S8C_SIG_BASE)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[moi_s8c_sig0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

let MOI_S86_SIG_DOT0 = prove
 (`!r s. (r = &0 \/ r = &1 \/ r = &2 \/ r = &3) /\ &2 * r - &1 <= s /\ s <= &2 * r + &1
         ==> moi_s8c_sig(&2 * r) dot moi_s8c_sig s = &1`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s8c_sig s = moi_s8c_sig0 s` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S8C_SIG_BASE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV REAL_RAT_REDUCE_CONV))) THEN
  REWRITE_TAC[MOI_S86_SIG_EVEN; moi_s8c_sig0] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[DOT_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC);;

let MOI_S86_SIG_DOT = prove
 (`!a s. integer a /\ &2 * a - &1 <= s /\ s <= &2 * a + &1
         ==> moi_s8c_sig(&2 * a) dot moi_s8c_sig s = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:real` (X_CHOOSE_THEN `r:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) o
    MATCH_MP MOI_S86_INT_MOD4) THEN
  SUBGOAL_THEN `moi_s8c_sig(&2 * a) = moi_s8c_sig(&2 * r) /\
                moi_s8c_sig s = moi_s8c_sig (s - &8 * k)` (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `&2 * (&4 * k + r) = &2 * r + &8 * k`] THEN
      ASM_SIMP_TAC[MOI_S8C_SIG_PERIODIC];
      MP_TAC(SPECL [`s - &8 * k`; `k:real`] MOI_S8C_SIG_PERIODIC) THEN
      ASM_REWRITE_TAC[REAL_SUB_ADD]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S86_SIG_DOT0 THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S86_PSI_PIECE = prove
 (`!a u t. integer a /\ &2 * a - &1 <= t /\ t <= &2 * a + &1 /\ &0 <= u /\ u <= &1
           ==> &2 * a - &1 <= moi_s86_psi u t /\ moi_s86_psi u t <= &2 * a + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `u:real`; `t:real`] MOI_S86_PSI_CELL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_S86_DIV_RANGE THEN
  REWRITE_TAC[real_max; real_min] THEN REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_S86_E_DOT = prove
 (`!a x:real^2. integer a /\ &2 * a - &1 <= x$1 /\ x$1 <= &2 * a + &1
                ==> &0 < moi_s8c_sig(&2 * a) dot moi_s86_e x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s86_e; DOT_RMUL] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[MOI_S86_RADIUS_POS] THEN
  SUBGOAL_THEN `moi_s8c_sig (&2 * a) dot
                moi_s8c_sig (moi_s86_psi ((x:real^2)$2 - floor(x$2)) (x$1)) = &1`
  (fun th -> REWRITE_TAC[th; REAL_LT_01]) THEN
  MATCH_MP_TAC MOI_S86_SIG_DOT THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S86_PSI_PIECE THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `(x:real^2)$2` FLOOR) THEN REAL_ARITH_TAC);;

let MOI_S86_SEGMENT_HALFPLANE = prove
 (`!v p q:real^2. &0 < v dot p /\ &0 < v dot q ==> ~(vec 0 IN segment[p,q])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{z:real^2 | v dot z > &0}`; `p:real^2`; `q:real^2`]
    SEGMENT_SUBSET_CONVEX) THEN
  REWRITE_TAC[CONVEX_HALFSPACE_GT; IN_ELIM_THM; real_gt] THEN ASM_REWRITE_TAC[SUBSET] THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; DOT_RZERO; REAL_LT_REFL]);;

let MOI_S86_E_SEGMENT = prove
 (`!x y:real^2. x$1 = y$1 ==> ~(vec 0 IN segment[moi_s86_e x,moi_s86_e y])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `((x:real^2)$1 + &1) / &2` FLOOR) THEN
  ABBREV_TAC `a = floor(((x:real^2)$1 + &1) / &2)` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_s8c_sig(&2 * a)`; `moi_s86_e x`; `moi_s86_e y`]
    MOI_S86_SEGMENT_HALFPLANE) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S86_E_DOT THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S86_E_ZERO_LEVEL = prove
 (`!t. moi_s86_e (vector[t; &0]) = moi_s8c_sig t`,
  GEN_TAC THEN REWRITE_TAC[moi_s86_e; VECTOR_2] THEN
  SUBGOAL_THEN `floor(&0) = &0` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_REFL; RPOW_0; REAL_ADD_RID; REAL_MUL_LID; VECTOR_MUL_LID] THEN
  AP_TERM_TAC THEN REWRITE_TAC[moi_s86_psi; REAL_NEG_0; REAL_ADD_RID; REAL_DIV_1] THEN
  SUBGOAL_THEN `!w. max (&0) (min w (&0)) = &0` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[real_max; real_min] THEN GEN_TAC THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let MOI_S86_SQ_LOOP = prove
 (`!c. simple_path (\s. moi_s8c_sig (c + &8 * drop s)) /\
       pathfinish (\s. moi_s8c_sig (c + &8 * drop s)) =
       pathstart (\s. moi_s8c_sig (c + &8 * drop s)) /\
       path_image (\s. moi_s8c_sig (c + &8 * drop s)) =
       relative_frontier(interval[--vec 1:real^2,vec 1])`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\s. moi_s8c_sig (c + &8 * drop s)) =
                moi_s86_e o (\s. vector[c + &8 * drop s; &0])` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; MOI_S86_E_ZERO_LEVEL]; ALL_TAC] THEN
  SUBGOAL_THEN `path (moi_s86_e o (\s. vector[c + &8 * drop s; &0]:real^2))` ASSUME_TAC THENL
   [REWRITE_TAC[path] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    REWRITE_TAC[MOI_S86_E_CONTINUOUS] THEN
    SUBGOAL_THEN `(\s. vector[c + &8 * drop s; &0]:real^2) =
                  (\s. vector[c; &0] + drop s % vector[&8; &0])` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; VECTOR_2] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[simple_path; path_image] THEN
  REWRITE_TAC[pathstart; pathfinish; o_THM; MOI_S86_E_ZERO_LEVEL; DROP_VEC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; MOI_S86_SIG_EQ] THEN STRIP_TAC THEN
    SUBGOAL_THEN `drop s - drop t = &0 \/ drop s - drop t = &1 \/ drop s - drop t = -- &1`
    MP_TAC THENL
     [MP_TAC(SPEC `drop s - drop t` MOI_S8C_INT_SMALL) THEN
      UNDISCH_TAC `integer(((c + &8 * drop s) - (c + &8 * drop t)) / &8)` THEN
      REWRITE_TAC[REAL_ARITH `((c + &8 * x) - (c + &8 * y)) / &8 = x - y`] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC];
    MP_TAC(SPECL [`c:real`; `&1`] MOI_S8C_SIG_PERIODIC) THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM; MOI_S86_E_ZERO_LEVEL; MOI_S8C_SIG_IN];
      REWRITE_TAC[SUBSET; IN_IMAGE; o_THM; MOI_S86_E_ZERO_LEVEL] THEN
      X_GEN_TAC `y:real^2` THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_S8C_SIG_ONTO) THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `lift(((t0 - c) / &8) - floor((t0 - c) / &8))` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
      MP_TAC(SPEC `(t0 - c) / &8` FLOOR) THEN STRIP_TAC THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `y:real^2`)) THEN
      REWRITE_TAC[MOI_S86_SIG_EQ] THEN
      REWRITE_TAC[REAL_ARITH `(t0 - (c + &8 * ((t0 - c) / &8 - f))) / &8 = f`] THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_S86_LINEPATH_8 = prove
 (`!p:real^2 s. linepath(p,p + vector[&8;&0]) s = vector[p$1 + &8 * drop s; p$2]`,
  REWRITE_TAC[linepath; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REAL_ARITH_TAC);;

let MOI_S86_ZERO_INSIDE_SQ = prove
 (`Cx(&0) IN inside(relative_frontier(interval[--vec 1:real^2,vec 1]))`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  SUBGOAL_THEN `~(interior(interval[--vec 1:real^2,vec 1]) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_NE_EMPTY; VECTOR_NEG_COMPONENT;
                VEC_COMPONENT] THEN
    GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; INSIDE_FRONTIER_EQ_INTERIOR;
               BOUNDED_INTERVAL; CONVEX_INTERVAL] THEN
  REWRITE_TAC[INTERIOR_INTERVAL; IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  GEN_TAC THEN DISCH_TAC THEN REAL_ARITH_TAC);;

let MOI_S86_WINDING = prove
 (`!g:real^1->real^2.
     path g /\ pathfinish g = pathstart g + vector[&8; &0]
     ==> path (moi_s86_e o g) /\
         pathfinish (moi_s86_e o g) = pathstart (moi_s86_e o g) /\
         ~(winding_number(moi_s86_e o g,Cx(&0)) = Cx(&0))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `path (moi_s86_e o (g:real^1->real^2))` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[MOI_S86_E_CONTINUOUS];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathfinish (moi_s86_e o (g:real^1->real^2)) = pathstart (moi_s86_e o g)`
  ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`pathstart (g:real^1->real^2)`; `&1`] MOI_S86_E_PERIODIC) THEN
    REWRITE_TAC[INTEGER_CLOSED; VECTOR_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p = pathstart (g:real^1->real^2)` THEN
  SUBGOAL_THEN
   `winding_number(moi_s86_e o g,Cx(&0)) =
    winding_number(moi_s86_e o linepath(p,p + vector[&8;&0]),Cx(&0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_PATHS THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[MOI_S86_E_CONTINUOUS; SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_DELETE] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; MOI_S86_E_NONZERO] THEN
    MATCH_MP_TAC HOMOTOPIC_PATHS_LINEAR THEN
    ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH; SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(SPEC `(p:real^2)$1` MOI_S86_SQ_LOOP) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `winding_number(moi_s86_e o linepath(p,p + vector[&8;&0]),Cx(&0)) =
    winding_number((\s. moi_s8c_sig ((p:real^2)$1 + &8 * drop s)),Cx(&0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC WINDING_NUMBER_HOMOTOPIC_LOOPS THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[PATH_LINEPATH; MOI_S86_E_CONTINUOUS];
      REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH] THEN
      MP_TAC(SPECL [`p:real^2`; `&1`] MOI_S86_E_PERIODIC) THEN
      REWRITE_TAC[INTEGER_CLOSED; VECTOR_MUL_LID];
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      REWRITE_TAC[o_THM; MOI_S86_LINEPATH_8; GSYM MOI_S86_E_ZERO_LEVEL] THEN
      MATCH_MP_TAC(SET_RULE `!a:complex s. ~(a IN s) ==> s SUBSET (:complex) DELETE a`) THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC MOI_S86_E_SEGMENT THEN
      REWRITE_TAC[VECTOR_2]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(\s. moi_s8c_sig ((p:real^2)$1 + &8 * drop s))`
    SIMPLE_CLOSED_PATH_WINDING_NUMBER_INSIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN (MP_TAC o SPEC `Cx(&0)`)) THEN
  REWRITE_TAC[MOI_S86_ZERO_INSIDE_SQ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CX_INJ; COMPLEX_NEG_EQ_0] THEN REAL_ARITH_TAC);;

let MOI_S86_JORDAN = prove
 (`!g:real^1->real^2.
     path g /\ pathfinish g = pathstart g + vector[&8; &0] /\
     (!s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
            (g s)$2 = (g t)$2 /\ integer(((g s)$1 - (g t)$1) / &8)
            ==> s = t \/ (s = vec 0 /\ t = vec 1) \/ (s = vec 1 /\ t = vec 0))
     ==> simple_path (moi_s86_e o g) /\
         pathfinish (moi_s86_e o g) = pathstart (moi_s86_e o g) /\
         Cx(&0) IN inside(path_image (moi_s86_e o g))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `g:real^1->real^2` MOI_S86_WINDING) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simple_path (moi_s86_e o (g:real^1->real^2))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[simple_path; o_THM; MOI_S86_E_EQ] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(Cx(&0) IN path_image (moi_s86_e o (g:real^1->real^2)))` ASSUME_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_COMPOSE; IN_IMAGE; GSYM COMPLEX_VEC_0] THEN
    MESON_TAC[MOI_S86_E_NONZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx(&0) IN outside(path_image (moi_s86_e o (g:real^1->real^2))))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`moi_s86_e o (g:real^1->real^2)`; `Cx(&0)`]
      WINDING_NUMBER_ZERO_IN_OUTSIDE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `path_image (moi_s86_e o (g:real^1->real^2))` INSIDE_UNION_OUTSIDE) THEN
  MAP_EVERY UNDISCH_TAC
   [`~(Cx(&0) IN path_image (moi_s86_e o (g:real^1->real^2)))`;
    `~(Cx(&0) IN outside(path_image (moi_s86_e o (g:real^1->real^2))))`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Members of the family in the torus model: essential, parametrised      *)
(* with a nonzero displacement of which every loop in them has a multiple. *)
(* ------------------------------------------------------------------------- *)

let moi_s86_binv = new_definition
 `moi_s86_binv =
    @binv. homeomorphism (pl_torus_model,
                          sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                         (moi_s8c_bpsi,binv)`;;

let MOI_S86_BINV = prove
 (`homeomorphism (pl_torus_model,sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
                 (moi_s8c_bpsi,moi_s86_binv)`,
  REWRITE_TAC[moi_s86_binv] THEN CONV_TAC SELECT_CONV THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN REWRITE_TAC[MOI_S8C_BPSI_FACTS] THEN
  MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN REWRITE_TAC[MOI_S4U_TORUS_MODEL]);;

let MOI_S86_ESSENTIAL_MODEL = prove
 (`!c:real^(2,2)finite_sum->bool.
     c SUBSET pl_torus_model /\ pl_sphere 1 c /\
     ~(?d. d SUBSET pl_torus_model /\ pl_cell_with_boundary 2 d c)
     ==> ?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET c /\
             ~homotopic_loops pl_torus_model k (linepath(pathstart k,pathstart k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM;
    TAUT `~(a /\ b /\ c /\ ~d) <=> a /\ b /\ c ==> d`]) THEN
  UNDISCH_TAC `~(?d. d SUBSET pl_torus_model /\
                     pl_cell_with_boundary 2 d (c:real^(2,2)finite_sum->bool))` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8C_MODEL_DISK THEN ASM_REWRITE_TAC[]);;

let MOI_S86_DISP_EQ_ON = prove
 (`!g h:real^1->real^(2,2)finite_sum.
     path g /\ path h /\ pathfinish g = pathstart g /\
     path_image g SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
     (!t. t IN interval[vec 0,vec 1] ==> g t = h t)
     ==> moi_s4u_disp g = moi_s4u_disp h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `path_image (h:real^1->real^(2,2)finite_sum) = path_image g /\
                pathstart h = pathstart g /\ pathfinish h = pathfinish g`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[path_image; pathstart; pathfinish] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN ASM_MESON_TAC[];
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->real^(2,2)finite_sum`; `h:real^1->real^(2,2)finite_sum`]
    MOI_S4U_DISP_HOMOTOPIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[]);;

let MOI_S86_PARAM = prove
 (`!c:real^(2,2)finite_sum->bool.
     c SUBSET pl_torus_model /\ pl_sphere 1 c /\
     (?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET c /\
          ~homotopic_loops pl_torus_model k (linepath(pathstart k,pathstart k)))
     ==> ?g. simple_path g /\ pathfinish g = pathstart g /\ path_image g = c /\
             integer((moi_s4u_disp (moi_s8c_bpsi o g))$1) /\
             integer((moi_s4u_disp (moi_s8c_bpsi o g))$2) /\
             ~(moi_s4u_disp (moi_s8c_bpsi o g) = vec 0) /\
             (!h. path h /\ pathfinish h = pathstart h /\ path_image h SUBSET c
                  ==> ?m. integer m /\
                          moi_s4u_disp (moi_s8c_bpsi o h) =
                          m % moi_s4u_disp (moi_s8c_bpsi o g))`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^1->real^(2,2)finite_sum` STRIP_ASSUME_TAC))) THEN
  MP_TAC MOI_S86_BINV THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE moi_s8c_bpsi c SUBSET
                sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE moi_s8c_bpsi pl_torus_model =
       sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
      `(c:real^(2,2)finite_sum->bool) SUBSET pl_torus_model`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE moi_s8c_bpsi c homeomorphic sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:(2,2)finite_sum`,`:N`] HOMEOMORPHIC_TRANS) THEN
    EXISTS_TAC `c:real^(2,2)finite_sum->bool` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`moi_s8c_bpsi`; `moi_s86_binv`] THEN
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC
       [`pl_torus_model`; `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`] THEN
      ASM_REWRITE_TAC[MOI_S86_BINV];
      MATCH_MP_TAC MOI_S4U_PL_SPHERE1_CIRCLE THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE moi_s8c_bpsi (c:real^(2,2)finite_sum->bool)` MOI_S4U_TT_CURVE_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^1->real^(2,2)finite_sum` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path (g0:real^1->real^(2,2)finite_sum)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `path_image (g0:real^1->real^(2,2)finite_sum) SUBSET
                sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1]
                    ==> (g0:real^1->real^(2,2)finite_sum) t IN
                        sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (g0:real^1->real^(2,2)finite_sum) SUBSET
                 sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  EXISTS_TAC `moi_s86_binv o (g0:real^1->real^(2,2)finite_sum)` THEN
  SUBGOAL_THEN `path (moi_s86_binv o (g0:real^1->real^(2,2)finite_sum))` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (moi_s86_binv o (g0:real^1->real^(2,2)finite_sum)) = c`
  ASSUME_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`!x:real^(2,2)finite_sum. x IN pl_torus_model ==> moi_s86_binv (moi_s8c_bpsi x) = x`;
      `(c:real^(2,2)finite_sum->bool) SUBSET pl_torus_model`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4u_disp (moi_s8c_bpsi o moi_s86_binv o
                              (g0:real^1->real^(2,2)finite_sum)) =
                moi_s4u_disp g0` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_S86_DISP_EQ_ON THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `pl_torus_model` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC(ASSUME `!y. y IN sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)
                               ==> moi_s8c_bpsi (moi_s86_binv y) = y`) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `g0:real^1->real^(2,2)finite_sum` MOI_S4U_LOOP_LIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `simple_path (moi_s86_binv o (g0:real^1->real^(2,2)finite_sum))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[simple_path; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`] THEN STRIP_TAC THEN
    UNDISCH_TAC `simple_path (g0:real^1->real^(2,2)finite_sum)` THEN
    REWRITE_TAC[simple_path] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `moi_s8c_bpsi` o check (fun th ->
      is_eq (concl th) && can (find_term ((=) `moi_s86_binv`)) (lhs(concl th)))) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN CONJ_TAC THENL
   [(* the displacement is nonzero: else the essential loop k would be null-homotopic *)
    DISCH_TAC THEN
    UNDISCH_TAC `~homotopic_loops pl_torus_model k
                    (linepath(pathstart k,pathstart (k:real^1->real^(2,2)finite_sum)))` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `path_image (k:real^1->real^(2,2)finite_sum) SUBSET pl_torus_model /\
                  pathstart k IN pl_torus_model` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `k:real^1->real^(2,2)finite_sum` PATHSTART_IN_PATH_IMAGE) THEN
      MAP_EVERY UNDISCH_TAC
       [`path_image (k:real^1->real^(2,2)finite_sum) SUBSET c`;
        `(c:real^(2,2)finite_sum->bool) SUBSET pl_torus_model`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `homotopic_loops (sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1))
        (moi_s8c_bpsi o (k:real^1->real^(2,2)finite_sum))
        (linepath(moi_s8c_bpsi(pathstart k),moi_s8c_bpsi(pathstart k)))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `path (moi_s8c_bpsi o (k:real^1->real^(2,2)finite_sum)) /\
                    path_image (moi_s8c_bpsi o k) SUBSET IMAGE moi_s8c_bpsi c /\
                    pathfinish (moi_s8c_bpsi o k) = pathstart (moi_s8c_bpsi o k)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[PATH_IMAGE_COMPOSE; PATHSTART_COMPOSE; PATHFINISH_COMPOSE] THEN
        ASM_SIMP_TAC[IMAGE_SUBSET] THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `pl_torus_model` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `moi_s8c_bpsi (pathstart (k:real^1->real^(2,2)finite_sum)) IN
                    sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`IMAGE moi_s8c_bpsi pl_torus_model =
           sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
          `pathstart (k:real^1->real^(2,2)finite_sum) IN pl_torus_model`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`moi_s8c_bpsi o (k:real^1->real^(2,2)finite_sum)`;
                     `linepath(moi_s8c_bpsi(pathstart (k:real^1->real^(2,2)finite_sum)),
                               moi_s8c_bpsi(pathstart k))`] MOI_S4U_DISP_HOMOTOPIC) THEN
      ASM_REWRITE_TAC[PATH_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                      PATH_IMAGE_LINEPATH; SEGMENT_REFL; SING_SUBSET] THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `IMAGE moi_s8c_bpsi c SUBSET
                     sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)` THEN
        UNDISCH_TAC `path_image (moi_s8c_bpsi o (k:real^1->real^(2,2)finite_sum)) SUBSET
                     IMAGE moi_s8c_bpsi c` THEN
        REWRITE_TAC[PATHSTART_COMPOSE] THEN SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[MOI_S4U_DISP_CONST] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `moi_s8c_bpsi o (k:real^1->real^(2,2)finite_sum)` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `moi_s4u_disp`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      UNDISCH_TAC `moi_s4u_disp (g0:real^1->real^(2,2)finite_sum) = vec 0` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`moi_s8c_bpsi o (k:real^1->real^(2,2)finite_sum)`;
                   `linepath(moi_s8c_bpsi(pathstart (k:real^1->real^(2,2)finite_sum)),
                             moi_s8c_bpsi(pathstart k))`;
                   `moi_s86_binv`;
                   `sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
                   `pl_torus_model`] HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    SUBGOAL_THEN `moi_s86_binv o linepath(moi_s8c_bpsi(pathstart (k:real^1->real^(2,2)finite_sum)),
                                          moi_s8c_bpsi(pathstart k)) =
                  linepath(pathstart k,pathstart k)` SUBST1_TAC THENL
     [REWRITE_TAC[LINEPATH_REFL; FUN_EQ_THM; o_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_TRANS THEN
    EXISTS_TAC `moi_s86_binv o moi_s8c_bpsi o (k:real^1->real^(2,2)finite_sum)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_LOOPS_EQ THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(ASSUME `!x:real^(2,2)finite_sum. x IN pl_torus_model
                               ==> moi_s86_binv (moi_s8c_bpsi x) = x`) THEN
    UNDISCH_TAC `path_image (k:real^1->real^(2,2)finite_sum) SUBSET pl_torus_model` THEN
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    (* the multiple property *)
    X_GEN_TAC `h:real^1->real^(2,2)finite_sum` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `moi_s4u_disp`)) (concl th))) THEN
    REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `pl_torus_model` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`path_image (h:real^1->real^(2,2)finite_sum) SUBSET c`;
      `(c:real^(2,2)finite_sum->bool) SUBSET pl_torus_model`] THEN
    SET_TAC[]]);;

let MOI_S86_BPSI_LOOP = prove
 (`!g:real^1->real^(2,2)finite_sum.
     path g /\ pathfinish g = pathstart g /\ path_image g SUBSET pl_torus_model
     ==> path (moi_s8c_bpsi o g) /\
         pathfinish (moi_s8c_bpsi o g) = pathstart (moi_s8c_bpsi o g) /\
         path_image (moi_s8c_bpsi o g) = IMAGE moi_s8c_bpsi (path_image g) /\
         path_image (moi_s8c_bpsi o g) SUBSET
         sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
         (simple_path g ==> simple_path (moi_s8c_bpsi o g))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S86_BINV THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `path (moi_s8c_bpsi o (g:real^1->real^(2,2)finite_sum))` ASSUME_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `pl_torus_model` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE moi_s8c_bpsi pl_torus_model =
       sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`;
      `path_image (g:real^1->real^(2,2)finite_sum) SUBSET pl_torus_model`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simple_path; o_THM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(g:real^1->real^(2,2)finite_sum) x IN pl_torus_model /\ g y IN pl_torus_model`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `path_image (g:real^1->real^(2,2)finite_sum) SUBSET pl_torus_model` THEN
    REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `moi_s86_binv` o check (fun th ->
    is_eq(concl th) && can (find_term ((=) `moi_s8c_bpsi`)) (lhs(concl th)))) THEN
  ASM_SIMP_TAC[]);;

let MOI_S86_INT_UNIT = prove
 (`!m m'. integer m /\ integer m' /\ m' * m = &1 ==> m = &1 \/ m = -- &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m':real`; `m:real`] INTEGER_ABS_MUL_EQ_1) THEN
  ASM_REWRITE_TAC[REAL_ABS_NUM] THEN REAL_ARITH_TAC);;

let MOI_S86_COMMON_DISP = prove
 (`!g g':real^1->real^(2,2)finite_sum.
     simple_path g /\ pathfinish g = pathstart g /\ path_image g SUBSET pl_torus_model /\
     simple_path g' /\ pathfinish g' = pathstart g' /\ path_image g' SUBSET pl_torus_model /\
     DISJOINT (path_image g) (path_image g') /\
     ~(moi_s4u_disp (moi_s8c_bpsi o g) = vec 0) /\
     ~(moi_s4u_disp (moi_s8c_bpsi o g') = vec 0)
     ==> moi_s4u_disp (moi_s8c_bpsi o g') = moi_s4u_disp (moi_s8c_bpsi o g) \/
         moi_s4u_disp (moi_s8c_bpsi o g') = --(moi_s4u_disp (moi_s8c_bpsi o g))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^1->real^(2,2)finite_sum` MOI_S86_BPSI_LOOP) THEN
  MP_TAC(ISPEC `g':real^1->real^(2,2)finite_sum` MOI_S86_BPSI_LOOP) THEN
  ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC MOI_S86_BINV THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  ABBREV_TAC `p = moi_s8c_bpsi o (g:real^1->real^(2,2)finite_sum)` THEN
  ABBREV_TAC `p' = moi_s8c_bpsi o (g':real^1->real^(2,2)finite_sum)` THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE moi_s8c_bpsi (path_image (g:real^1->real^(2,2)finite_sum)))
             (IMAGE moi_s8c_bpsi (path_image (g':real^1->real^(2,2)finite_sum))) /\
    DISJOINT (IMAGE moi_s8c_bpsi (path_image (g':real^1->real^(2,2)finite_sum)))
             (IMAGE moi_s8c_bpsi (path_image (g:real^1->real^(2,2)finite_sum)))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`DISJOINT (path_image (g:real^1->real^(2,2)finite_sum)) (path_image g')`;
      `path_image (g:real^1->real^(2,2)finite_sum) SUBSET pl_torus_model`;
      `path_image (g':real^1->real^(2,2)finite_sum) SUBSET pl_torus_model`;
      `!x:real^(2,2)finite_sum. x IN pl_torus_model ==> moi_s86_binv (moi_s8c_bpsi x) = x`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q q':real^1->real^(2,2)finite_sum.
                  simple_path q /\ pathfinish q = pathstart q /\
                  path_image q SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
                  ~(moi_s4u_disp q = vec 0) /\
                  simple_path q' /\ pathfinish q' = pathstart q' /\
                  path_image q' SUBSET sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1) /\
                  DISJOINT (path_image q) (path_image q')
                  ==> ?m. integer m /\ moi_s4u_disp q' = m % moi_s4u_disp q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4U_TT_PRIMITIVE THEN
    MP_TAC(ISPEC `q':real^1->real^(2,2)finite_sum` MOI_S4U_LOOP_LIFT) THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4U_TT_PARALLEL THEN ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (path_image (q:real^1->real^(2,2)finite_sum)) (path_image q')`;
      `path_image (q':real^1->real^(2,2)finite_sum) SUBSET
       sphere(vec 0:real^2,&1) PCROSS sphere(vec 0:real^2,&1)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`p:real^1->real^(2,2)finite_sum`; `p':real^1->real^(2,2)finite_sum`] th) THEN
    MP_TAC(SPECL [`p':real^1->real^(2,2)finite_sum`; `p:real^1->real^(2,2)finite_sum`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `m = &1 \/ m = -- &1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S86_INT_UNIT THEN EXISTS_TAC `m':real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(moi_s4u_disp (p:real^1->real^(2,2)finite_sum) = vec 0)` THEN
    UNDISCH_TAC `moi_s4u_disp (p:real^1->real^(2,2)finite_sum) =
                 m' % moi_s4u_disp (p':real^1->real^(2,2)finite_sum)` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM VECTOR_MUL_LID] THEN
    REWRITE_TAC[VECTOR_MUL_RCANCEL] THEN MESON_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `moi_s4u_disp (p':real^1->real^(2,2)finite_sum)`)) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LNEG]]);;

let MOI_S86_NU_INTEGER = prove
 (`!D w:real^2. integer(D$1) /\ integer(D$2) /\ integer(w$1) /\ integer(w$2)
                ==> integer(moi_s4u_nu D w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s4u_nu] THEN ASM_SIMP_TAC[INTEGER_CLOSED]);;

let MOI_S86_BASIS = prove
 (`!D:real^2.
     integer(D$1) /\ integer(D$2) /\ ~(D = vec 0) /\
     (!w:real^2. integer(w$1) /\ integer(w$2) /\ moi_s4u_nu D w = &0
                 ==> ?m. integer m /\ w = m % D)
     ==> ?E:real^2. integer(E$1) /\ integer(E$2) /\ &0 < moi_s4u_nu D E /\
                    !w:real^2. integer(w$1) /\ integer(w$2)
                               ==> ?m n. integer m /\ integer n /\ w = m % D + n % E`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?k. 0 < k /\ ?w:real^2. integer(w$1) /\ integer(w$2) /\ moi_s4u_nu D w = &k`
  MP_TAC THENL
   [SUBGOAL_THEN `?w:real^2. integer(w$1) /\ integer(w$2) /\ &0 < moi_s4u_nu D w`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(D:real^2 = vec 0)` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT; DE_MORGAN_THM] THEN
      STRIP_TAC THENL
       [ASM_CASES_TAC `&0 < (D:real^2)$1` THENL
         [EXISTS_TAC `vector[&0; &1]:real^2`;
          EXISTS_TAC `vector[&0; -- &1]:real^2`] THEN
        SIMP_TAC[moi_s4u_nu; VECTOR_2; INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
        ASM_CASES_TAC `&0 < (D:real^2)$2` THENL
         [EXISTS_TAC `vector[-- &1; &0]:real^2`;
          EXISTS_TAC `vector[&1; &0]:real^2`] THEN
        SIMP_TAC[moi_s4u_nu; VECTOR_2; INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPEC `moi_s4u_nu D (w:real^2)` INTEGER_POS) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; MOI_S86_NU_INTEGER] THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN EXISTS_TAC `k:num` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_MESON_TAC[];
      EXISTS_TAC `w:real^2` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `E:real^2` STRIP_ASSUME_TAC))
    ASSUME_TAC)) THEN
  EXISTS_TAC `E:real^2` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
  X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN
  ABBREV_TAC `a = moi_s4u_nu D (w:real^2)` THEN
  SUBGOAL_THEN `integer a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC MOI_S86_NU_INTEGER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q = floor(a / &k)` THEN
  SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `integer q /\ &0 <= a - q * &k /\ a - q * &k < &k` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `a / &k` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_LE] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ];
      REWRITE_TAC[REAL_ARITH `a - q * k < k <=> a < (q + &1) * k`] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4u_nu D (w - q % E:real^2) = a - q * &k` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S4U_NU_LINEAR] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `a - q * &k = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPEC `a - q * &k` INTEGER_POS) THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
    REWRITE_TAC[NOT_IMP; NOT_CLAUSES] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `w - q % E:real^2` THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; INTEGER_CLOSED];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w - q % E:real^2` o check (fun th ->
    is_forall (concl th) && can (find_term ((=) `moi_s4u_nu`)) (concl th) &&
    can (find_term ((=) `D:real^2`)) (concl th))) THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; INTEGER_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`m:real`; `q:real`] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `w - q % E:real^2 = m % D` THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Planar order of scaled Jordan curves around 0: sc n k is the image      *)
(* of k under multiplication by 2^n, mu k the maximum norm on k.  Scaled   *)
(* copies of a Jordan curve around 0 that are pairwise disjoint are        *)
(* nested increasingly; a point z <> 0 lies inside exactly the copies with *)
(* index at least some n.                                                   *)
(* ------------------------------------------------------------------------- *)

let moi_s86_sc = new_definition
 `moi_s86_sc (n:real) (s:real^2->bool) = IMAGE (\z. (&2 rpow n) % z) s`;;

let moi_s86_mu = new_definition
 `moi_s86_mu (s:real^2->bool) = sup (IMAGE (\z. norm z) s)`;;

let MOI_S86_RPOW2_POS = prove
 (`!n. &0 < &2 rpow n`,
  GEN_TAC THEN MATCH_MP_TAC RPOW_POS_LT THEN REAL_ARITH_TAC);;

let MOI_S86_MU = prove
 (`!s:real^2->bool. compact s /\ ~(s = {})
       ==> (?y. y IN s /\ norm y = moi_s86_mu s) /\
           (!y. y IN s ==> norm y <= moi_s86_mu s)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real^2. norm z`; `s:real^2->bool`] CONTINUOUS_ATTAINS_SUP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM o_DEF; ETA_AX; CONTINUOUS_ON_LIFT_NORM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s86_mu s = norm(y:real^2)` SUBST1_TAC THENL
   [REWRITE_TAC[moi_s86_mu] THEN MATCH_MP_TAC REAL_SUP_UNIQUE THEN
    REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S86_SC_LINEAR = prove
 (`!n. linear (\z:real^2. (&2 rpow n) % z) /\
       (!x y:real^2. (&2 rpow n) % x = (&2 rpow n) % y ==> x = y) /\
       (!y:real^2. ?x. (&2 rpow n) % x = y)`,
  GEN_TAC THEN MP_TAC(SPEC `n:real` MOI_S86_RPOW2_POS) THEN DISCH_TAC THEN
  REWRITE_TAC[LINEAR_SCALING] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ];
    GEN_TAC THEN EXISTS_TAC `inv(&2 rpow n) % (y:real^2)` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let MOI_S86_SC_INSIDE = prove
 (`!n s. inside(moi_s86_sc n s) = moi_s86_sc n (inside s) /\
         outside(moi_s86_sc n s) = moi_s86_sc n (outside s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s86_sc] THEN
  MP_TAC(SPEC `n:real` MOI_S86_SC_LINEAR) THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC INSIDE_LINEAR_IMAGE; MATCH_MP_TAC OUTSIDE_LINEAR_IMAGE] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S86_SC_ADD = prove
 (`!m n s. moi_s86_sc m (moi_s86_sc n s) = moi_s86_sc (m + n) s`,
  REWRITE_TAC[moi_s86_sc; GSYM IMAGE_o; o_DEF; VECTOR_MUL_ASSOC] THEN
  SIMP_TAC[RPOW_ADD; REAL_ARITH `&0 < &2`]);;

let MOI_S86_SC_ZERO = prove
 (`!s. moi_s86_sc (&0) s = s`,
  REWRITE_TAC[moi_s86_sc; RPOW_0; VECTOR_MUL_LID; IMAGE_ID]);;

let MOI_S86_SC_IN = prove
 (`!n s z. z IN moi_s86_sc n s <=> inv(&2 rpow n) % z IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s86_sc; IN_IMAGE] THEN
  MP_TAC(SPEC `n:real` MOI_S86_RPOW2_POS) THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    DISCH_TAC THEN EXISTS_TAC `inv(&2 rpow n) % (z:real^2)` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let MOI_S86_SC_MU = prove
 (`!n s. compact s /\ ~(s = {}) ==> moi_s86_mu (moi_s86_sc n s) = &2 rpow n * moi_s86_mu s`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `n:real` MOI_S86_RPOW2_POS) THEN DISCH_TAC THEN
  MP_TAC(SPEC `s:real^2->bool` MOI_S86_MU) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^2. x IN s ==> norm x <= norm(y:real^2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `norm(y:real^2)`)) THEN
  REWRITE_TAC[moi_s86_mu; moi_s86_sc; GSYM IMAGE_o; o_DEF] THEN
  MATCH_MP_TAC REAL_SUP_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `b:real` THEN DISCH_TAC THEN EXISTS_TAC `y:real^2` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S86_CIRCLE_BASIC = prove
 (`!k:real^2->bool.
     k homeomorphic sphere(vec 0:real^2,&1)
     ==> compact k /\ closed k /\ bounded k /\ ~(k = {})`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact(k:real^2->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP HOMEOMORPHIC_COMPACTNESS th]) THEN
    REWRITE_TAC[COMPACT_SPHERE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_IMP_BOUNDED] THEN DISCH_TAC THEN
  UNDISCH_TAC `(k:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
  ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY] THEN
  REWRITE_TAC[SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC);;

let MOI_S86_SC_JORDAN = prove
 (`!n k:real^2->bool.
     k homeomorphic sphere(vec 0:real^2,&1) /\ vec 0 IN inside k
     ==> moi_s86_sc n k homeomorphic sphere(vec 0:real^2,&1) /\
         vec 0 IN inside(moi_s86_sc n k) /\ ~(vec 0 IN moi_s86_sc n k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_S86_SC_INSIDE; MOI_S86_SC_IN; VECTOR_MUL_RZERO] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:2`,`:N`] HOMEOMORPHIC_TRANS) THEN
    EXISTS_TAC `k:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[moi_s86_sc] THEN
    MATCH_MP_TAC HOMEOMORPHIC_SCALING THEN
    MP_TAC(SPEC `n:real` MOI_S86_RPOW2_POS) THEN REAL_ARITH_TAC;
    MP_TAC(ISPEC `k:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `vec 0 IN inside(k:real^2->bool)` THEN SET_TAC[]]);;

let MOI_S86_NEST_MU = prove
 (`!k k':real^2->bool.
     compact k /\ ~(k = {}) /\ ~(vec 0 IN k) /\ compact k' /\ ~(k' = {}) /\
     k SUBSET inside k'
     ==> moi_s86_mu k < moi_s86_mu k'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:real^2->bool` MOI_S86_MU) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) (K ALL_TAC)) THEN
  MP_TAC(SPEC `k':real^2->bool` MOI_S86_MU) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC) THEN
  SUBGOAL_THEN `inside k' SUBSET cball(vec 0:real^2,moi_s86_mu k')` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_CBALL; SUBSET; IN_CBALL_0] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^2) IN inside k'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open(inside(k':real^2->bool))` MP_TAC THENL
   [MATCH_MP_TAC OPEN_INSIDE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < norm(y:real^2)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `t = e / (&2 * norm(y:real^2))` THEN
  SUBGOAL_THEN `&0 < t /\ t * norm(y:real^2) = e / &2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < norm(y:real^2)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `((&1 + t) % y:real^2) IN ball(y,e)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `y - (&1 + t) % y:real^2 = --(t % y)`;
                NORM_NEG; NORM_MUL] THEN
    REWRITE_TAC[MATCH_MP (REAL_ARITH `&0 < t ==> abs t = t`) (ASSUME `&0 < t`)] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((&1 + t) % y:real^2) <= moi_s86_mu k'` MP_TAC THENL
   [REWRITE_TAC[GSYM IN_CBALL_0] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL] THEN
  REWRITE_TAC[MATCH_MP (REAL_ARITH `&0 < t ==> abs(&1 + t) = &1 + t`) (ASSUME `&0 < t`)] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `norm(y:real^2)`)) THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S86_SC_NEST = prove
 (`!k:real^2->bool m n.
     k homeomorphic sphere(vec 0:real^2,&1) /\ vec 0 IN inside k /\
     m < n /\ DISJOINT (moi_s86_sc m k) (moi_s86_sc n k)
     ==> moi_s86_sc m k SUBSET inside(moi_s86_sc n k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:real`; `k:real^2->bool`] MOI_S86_SC_JORDAN) THEN
  MP_TAC(SPECL [`n:real`; `k:real^2->bool`] MOI_S86_SC_JORDAN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_s86_sc m k`; `moi_s86_sc n k`] MOI_S5C_JORDAN_NEST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `vec 0:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(SPEC `k:real^2->bool` MOI_S86_CIRCLE_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(vec 0 IN (k:real^2->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `vec 0 IN inside(k:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. compact (moi_s86_sc j k) /\ ~(moi_s86_sc j k = {})` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[moi_s86_sc] THEN ASM_SIMP_TAC[COMPACT_SCALING; IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < moi_s86_mu k` ASSUME_TAC THENL
   [MP_TAC(SPEC `k:real^2->bool` MOI_S86_MU) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) (K ALL_TAC)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `norm(y:real^2)`)) THEN
    REWRITE_TAC[NORM_POS_LT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 rpow m * moi_s86_mu k < &2 rpow n * moi_s86_mu k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RPOW_MONO_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`moi_s86_sc n k`; `moi_s86_sc m k`] MOI_S86_NEST_MU) THEN
  ASM_SIMP_TAC[MOI_S86_SC_MU] THEN ASM_REAL_ARITH_TAC);;

let MOI_S86_JORDAN_FACTS = prove
 (`!k:real^2->bool.
     k homeomorphic sphere(vec 0:real^2,&1) /\ vec 0 IN inside k
     ==> compact k /\ ~(k = {}) /\ ~(vec 0 IN k) /\ &0 < moi_s86_mu k /\
         inside k SUBSET ball(vec 0,moi_s86_mu k) /\
         ?e. &0 < e /\ ball(vec 0,e) SUBSET inside k`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:real^2->bool` MOI_S86_CIRCLE_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(vec 0 IN (k:real^2->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^2->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `vec 0 IN inside(k:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `k:real^2->bool` MOI_S86_MU) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `norm(y:real^2)`)) THEN
    REWRITE_TAC[NORM_POS_LT] THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM INTERIOR_CBALL] THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    ASM_SIMP_TAC[OPEN_INSIDE] THEN MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_CBALL; SUBSET; IN_CBALL_0] THEN ASM_SIMP_TAC[];
    MP_TAC(ISPEC `k:real^2->bool` OPEN_INSIDE) THEN ASM_REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^2`) THEN ASM_REWRITE_TAC[]]);;

let MOI_S86_INV_MUL_LT = prove
 (`!a x b. &0 < a ==> (inv a * x < b <=> x < a * b)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ] THEN REAL_ARITH_TAC);;

let MOI_S86_SC_LEAST = prove
 (`!k:real^2->bool z.
     k homeomorphic sphere(vec 0:real^2,&1) /\ vec 0 IN inside k /\ ~(z = vec 0) /\
     (!m n. integer m /\ integer n /\ ~(m = n)
            ==> DISJOINT (moi_s86_sc m k) (moi_s86_sc n k))
     ==> ?n. integer n /\
             !m. integer m ==> (z IN inside(moi_s86_sc m k) <=> n <= m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `k:real^2->bool` MOI_S86_JORDAN_FACTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `&0 < norm(z:real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  (* bounds through the scaling *)
  SUBGOAL_THEN `!m. z IN inside(moi_s86_sc m k) ==> norm(z:real^2) < &2 rpow m * moi_s86_mu k`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MOI_S86_SC_INSIDE; MOI_S86_SC_IN] THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(inv(&2 rpow m) % z:real^2) < moi_s86_mu k` MP_TAC THENL
     [REWRITE_TAC[GSYM IN_BALL_0] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `m:real` MOI_S86_RPOW2_POS) THEN DISCH_TAC THEN
    ASM_SIMP_TAC[NORM_MUL; REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`;
                 MOI_S86_INV_MUL_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m. norm(z:real^2) < &2 rpow m * e ==> z IN inside(moi_s86_sc m k)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MOI_S86_SC_INSIDE; MOI_S86_SC_IN] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(inv(&2 rpow m) % z:real^2) IN ball(vec 0,e)` MP_TAC THENL
     [MP_TAC(SPEC `m:real` MOI_S86_RPOW2_POS) THEN DISCH_TAC THEN
      ASM_SIMP_TAC[IN_BALL_0; NORM_MUL; REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`;
                   MOI_S86_INV_MUL_LT];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* monotonicity *)
  SUBGOAL_THEN `!m m'. integer m /\ integer m' /\ m <= m' /\ z IN inside(moi_s86_sc m k)
                       ==> z IN inside(moi_s86_sc m' k)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `m:real = m'` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_s86_sc m k SUBSET inside(moi_s86_sc m' k)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S86_SC_NEST THEN ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`moi_s86_sc m k`; `moi_s86_sc m' k`] MOI_S5C_NESTED_INSIDE) THEN
    ASM_SIMP_TAC[MOI_S86_SC_JORDAN] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  (* a lower bound b and a member index *)
  MP_TAC(SPECL [`&2`; `max (moi_s86_mu k / norm(z:real^2)) (norm(z:real^2) / e)`]
    REAL_ARCH_POW) THEN
  REWRITE_TAC[REAL_ARITH `&1 < &2`; REAL_MAX_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!m. integer m /\ m <= -- &N ==> ~(z IN inside(moi_s86_sc m k))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:real` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `moi_s86_mu k`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_NOT_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 rpow (-- &N) * moi_s86_mu k` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[RPOW_NEG; RPOW_POW] THEN
      SUBGOAL_THEN `&0 < &2 pow N` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `moi_s86_mu k < &2 pow N * norm(z:real^2)` ASSUME_TAC THENL
       [MP_TAC(SPECL [`moi_s86_mu k`; `&2 pow N`; `norm(z:real^2)`] REAL_LT_LDIV_EQ) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `z IN inside(moi_s86_sc (&N) k)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `e:real`)) (concl th))) THEN
    REWRITE_TAC[RPOW_POW] THEN
    UNDISCH_TAC `norm(z:real^2) / e < &2 pow N` THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ];
    ALL_TAC] THEN
  (* the least index *)
  SUBGOAL_THEN `?j. z IN inside(moi_s86_sc (-- &N + &j) k)` MP_TAC THENL
   [EXISTS_TAC `N + N:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `--x + x + x = x`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `j0:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `-- &N + &j0` THEN SIMP_TAC[INTEGER_CLOSED] THEN
  X_GEN_TAC `m:real` THEN DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `-- &N < m` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(m <= x) ==> x < m`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:real` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `-- &N`)) (concl th) &&
        not (can (find_term ((=) `j0:num`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPEC `m - -- &N` INTEGER_POS) THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
    DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `j0:num`)) (concl th))) THEN
    SUBGOAL_THEN `-- &N + &j = m` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[NOT_LT; GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `m':real`)) (concl th))) THEN
    EXISTS_TAC `-- &N + &j0` THEN ASM_SIMP_TAC[INTEGER_CLOSED]]);;

let MOI_S86_SC_FACTS = prove
 (`!n k:real^2->bool.
     k homeomorphic sphere(vec 0:real^2,&1) /\ vec 0 IN inside k
     ==> moi_s86_sc n k homeomorphic sphere(vec 0:real^2,&1) /\
         vec 0 IN inside(moi_s86_sc n k) /\ ~(vec 0 IN moi_s86_sc n k) /\
         compact(moi_s86_sc n k) /\ ~(moi_s86_sc n k = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:real`; `k:real^2->bool`] MOI_S86_SC_JORDAN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `moi_s86_sc n k` MOI_S86_CIRCLE_BASIC) THEN ASM_SIMP_TAC[]);;

let MOI_S86_MU_ORDER = prove
 (`!c1 c2:real^2->bool.
     c1 homeomorphic sphere(vec 0:real^2,&1) /\ vec 0 IN inside c1 /\
     c2 homeomorphic sphere(vec 0:real^2,&1) /\ vec 0 IN inside c2 /\
     (c1 = c2 \/ DISJOINT c1 c2)
     ==> (c1 SUBSET inside c2 ==> moi_s86_mu c1 < moi_s86_mu c2) /\
         (moi_s86_mu c1 <= moi_s86_mu c2 ==> c1 = c2 \/ c1 SUBSET inside c2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  MP_TAC(SPEC `c1:real^2->bool` MOI_S86_JORDAN_FACTS) THEN
  MP_TAC(SPEC `c2:real^2->bool` MOI_S86_JORDAN_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!d1 d2:real^2->bool.
                  compact d1 /\ ~(d1 = {}) /\ ~(vec 0 IN d1) /\ compact d2 /\ ~(d2 = {}) /\
                  d1 SUBSET inside d2 ==> moi_s86_mu d1 < moi_s86_mu d2`
  ASSUME_TAC THENL [REWRITE_TAC[MOI_S86_NEST_MU]; ALL_TAC] THEN
  CONJ_TAC THENL [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `c1:real^2->bool = c2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT (c1:real^2->bool) c2` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c1:real^2->bool`; `c2:real^2->bool`] MOI_S5C_JORDAN_NEST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `vec 0:real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c2:real^2->bool`; `c1:real^2->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_S86_FINITE_ARGMIN = prove
 (`!(s:A->bool) (f:A->real). FINITE s /\ ~(s = {})
       ==> (?a. a IN s /\ !x. x IN s ==> f a <= f x) /\
           (?a. a IN s /\ !x. x IN s ==> f x <= f a)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPEC `IMAGE (f:A->real) s` INF_FINITE);
    MP_TAC(ISPEC `IMAGE (f:A->real) s` SUP_FINITE)] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_IMAGE] THEN
  MESON_TAC[]);;

let MOI_S86_RPOW2_SHIFT = prove
 (`!x. &2 rpow x = &2 * &2 rpow (x - &1)`,
  GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_ARITH `x = (x - &1) + &1`] THEN
  SIMP_TAC[RPOW_ADD; REAL_ARITH `&0 < &2`; RPOW_POW; REAL_POW_1] THEN REAL_ARITH_TAC);;

let MOI_S86_CONSEC = prove
 (`!(gg:A->bool) (K:A->real^2->bool) z.
     FINITE gg /\ 2 <= CARD gg /\
     (!i. i IN gg ==> K i homeomorphic sphere(vec 0:real^2,&1) /\ vec 0 IN inside(K i)) /\
     (!i j m n. i IN gg /\ j IN gg /\ integer m /\ integer n /\ ~(i = j /\ m = n)
                ==> DISJOINT (moi_s86_sc m (K i)) (moi_s86_sc n (K j))) /\
     ~(z = vec 0) /\
     (!i n. i IN gg /\ integer n ==> ~(z IN moi_s86_sc n (K i)))
     ==> ?a b p q. a IN gg /\ b IN gg /\ ~(a = b) /\ integer p /\ integer q /\
                   moi_s86_sc p (K a) SUBSET inside(moi_s86_sc q (K b)) /\
                   z IN inside(moi_s86_sc q (K b)) /\ z IN outside(moi_s86_sc p (K a)) /\
                   (!i n. i IN gg /\ integer n
                          ==> ~(moi_s86_sc p (K a) SUBSET inside(moi_s86_sc n (K i)) /\
                                moi_s86_sc n (K i) SUBSET inside(moi_s86_sc q (K b))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. i IN gg
        ==> ?n. integer n /\
                !m. integer m ==> (z IN inside(moi_s86_sc m ((K:A->real^2->bool) i)) <=> n <= m)`
  MP_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S86_SC_LEAST THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `nn:A->real`) THEN
  (* basic facts on all curves *)
  SUBGOAL_THEN
   `!i n. i IN gg
          ==> moi_s86_sc n ((K:A->real^2->bool) i) homeomorphic sphere(vec 0:real^2,&1) /\
              vec 0 IN inside(moi_s86_sc n (K i)) /\ ~(vec 0 IN moi_s86_sc n (K i)) /\
              compact(moi_s86_sc n (K i)) /\ ~(moi_s86_sc n (K i) = {})`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S86_SC_FACTS THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j m n. i IN gg /\ j IN gg /\ integer m /\ integer n
              ==> (moi_s86_sc m ((K:A->real^2->bool) i) SUBSET inside(moi_s86_sc n (K j))
                   ==> moi_s86_mu (moi_s86_sc m (K i)) < moi_s86_mu (moi_s86_sc n (K j))) /\
                  (moi_s86_mu (moi_s86_sc m (K i)) <= moi_s86_mu (moi_s86_sc n (K j))
                   ==> (i = j /\ m = n) \/
                       moi_s86_sc m (K i) SUBSET inside(moi_s86_sc n (K j)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`moi_s86_sc m ((K:A->real^2->bool) i)`; `moi_s86_sc n ((K:A->real^2->bool) j)`]
      MOI_S86_MU_ORDER) THEN
    ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `i:A = j /\ m:real = n` THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `DISJOINT (moi_s86_sc m ((K:A->real^2->bool) i)) (moi_s86_sc n (K j))`
    ASSUME_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(moi_s86_sc m ((K:A->real^2->bool) i) = moi_s86_sc n (K j))` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `DISJOINT (moi_s86_sc m ((K:A->real^2->bool) i))
                                           (moi_s86_sc n (K j))` THEN
      ASM_REWRITE_TAC[SET_RULE `!s:real^2->bool. DISJOINT s s <=> s = {}`] THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the scaled maximum norms *)
  SUBGOAL_THEN
   `!i n. i IN gg
          ==> moi_s86_mu (moi_s86_sc n ((K:A->real^2->bool) i)) =
              &2 rpow n * moi_s86_mu (K i) /\ &0 < moi_s86_mu (K i)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPEC `(K:A->real^2->bool) i` MOI_S86_JORDAN_FACTS) THEN ASM_SIMP_TAC[] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MOI_S86_SC_MU];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(gg:A->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `2 <= CARD(gg:A->bool)` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gg:A->bool`;
                 `\i:A. moi_s86_mu (moi_s86_sc (nn i) ((K:A->real^2->bool) i))`]
    MOI_S86_FINITE_ARGMIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) (K ALL_TAC)) THEN
  MP_TAC(ISPECL [`gg:A->bool`;
                 `\i:A. moi_s86_mu (moi_s86_sc (nn i - &1) ((K:A->real^2->bool) i))`]
    MOI_S86_FINITE_ARGMIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC)) THEN
  RULE_ASSUM_TAC BETA_RULE THEN
  SUBGOAL_THEN `integer((nn:A->real) a) /\ integer((nn:A->real) b)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `z IN inside(moi_s86_sc ((nn:A->real) b) ((K:A->real^2->bool) b)) /\
                ~(z IN inside(moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `b:A` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `nn:A->real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "inside")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `(nn:A->real) b`) THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      FIRST_X_ASSUM(MP_TAC o SPEC `a:A` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `nn:A->real`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "inside")) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `(nn:A->real) a - &1`) THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `b:A`; `(nn:A->real) a - &1`; `(nn:A->real) b`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  (* the comparison of the two chosen curves *)
  SUBGOAL_THEN `moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a) SUBSET
                inside(moi_s86_sc ((nn:A->real) b) (K b))` ASSUME_TAC THENL
   [DISJ_CASES_TAC(REAL_ARITH
      `moi_s86_mu (moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a)) <=
       moi_s86_mu (moi_s86_sc ((nn:A->real) b) (K b)) \/
       moi_s86_mu (moi_s86_sc ((nn:A->real) b) (K b)) <=
       moi_s86_mu (moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a))`) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b:A`; `(nn:A->real) a - &1`; `(nn:A->real) b`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `moi_s86_mu`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(DISJ_CASES_THEN2 MP_TAC ACCEPT_TAC) THEN
      STRIP_TAC THEN UNDISCH_TAC `(nn:A->real) a - &1 = nn b` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPECL [`b:A`; `a:A`; `(nn:A->real) b`; `(nn:A->real) a - &1`] o
        check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `moi_s86_mu`)) (concl th) &&
          can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(DISJ_CASES_THEN2 MP_TAC ASSUME_TAC) THENL
       [STRIP_TAC THEN UNDISCH_TAC `(nn:A->real) b = nn a - &1` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`moi_s86_sc ((nn:A->real) b) ((K:A->real^2->bool) b)`;
                     `moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a)`]
        MOI_S5C_NESTED_INSIDE) THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `?j:A. j IN gg /\ ~(j = a)` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
      SUBGOAL_THEN `CARD(gg:A->bool) <= CARD {a:A}` MP_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_SING] THEN ASM SET_TAC[];
        REWRITE_TAC[CARD_SING] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `moi_s86_mu (moi_s86_sc ((nn:A->real) j - &1) ((K:A->real^2->bool) j)) =
      moi_s86_mu (moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a))`
    ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `j:A` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(nn:A->real) b`)) (concl th))) THEN
      FIRST_ASSUM(MP_TAC o SPEC `j:A` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(nn:A->real) a - &1`)) (concl th))) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:A = b`)) THEN
      SUBGOAL_THEN `!i n. i IN gg ==> moi_s86_mu (moi_s86_sc n ((K:A->real^2->bool) i)) =
                                      &2 rpow n * moi_s86_mu (K i)`
      (fun th -> SIMP_TAC[th; ASSUME `(j:A) IN gg`; ASSUME `(a:A) IN gg`]) THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MP_TAC(SPEC `(nn:A->real) a` MOI_S86_RPOW2_SHIFT) THEN
      MP_TAC(SPEC `(nn:A->real) j` MOI_S86_RPOW2_SHIFT) THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:A`; `a:A`; `(nn:A->real) j - &1`; `(nn:A->real) a - &1`] o
      check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_s86_mu`)) (concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th))) THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; REAL_LE_REFL; REAL_LT_REFL] THEN ASM_MESON_TAC[];
    MP_TAC(ISPEC `moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a)`
      INSIDE_UNION_OUTSIDE) THEN
    SUBGOAL_THEN `~(z IN moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a))` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
    UNDISCH_TAC `~(z IN inside(moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a)))` THEN
    SET_TAC[];
    MAP_EVERY X_GEN_TAC [`i:A`; `n:real`] THEN STRIP_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `integer((nn:A->real) i)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `moi_s86_mu (moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a)) <
      moi_s86_mu (moi_s86_sc n (K i)) /\
      moi_s86_mu (moi_s86_sc n ((K:A->real^2->bool) i)) <
      moi_s86_mu (moi_s86_sc ((nn:A->real) b) (K b))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `i:A`; `(nn:A->real) a - &1`; `n:real`] o
          check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `moi_s86_mu`)) (concl th) &&
            can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th)));
        FIRST_X_ASSUM(MP_TAC o SPECL [`i:A`; `b:A`; `n:real`; `(nn:A->real) b`] o
          check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `moi_s86_mu`)) (concl th) &&
            can (find_term (fun t -> is_const t && fst(dest_const t) = "SUBSET")) (concl th)))] THEN
      ASM_SIMP_TAC[INTEGER_CLOSED];
      ALL_TAC] THEN
    SUBGOAL_THEN `(nn:A->real) i <= n \/ n <= nn i - &1` MP_TAC THENL
     [ASM_CASES_TAC `(nn:A->real) i <= n` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`n:real`; `(nn:A->real) i`] REAL_LT_INTEGERS) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(MATCH_MP (SPECL [`i:A`; `n:real`] (ASSUME
     `!i n. i IN gg
            ==> moi_s86_mu (moi_s86_sc n ((K:A->real^2->bool) i)) =
                &2 rpow n * moi_s86_mu (K i) /\ &0 < moi_s86_mu (K i)`))
      (ASSUME `(i:A) IN gg`)) THEN
    STRIP_TAC THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:A` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(nn:A->real) b`)) (concl th))) THEN
      UNDISCH_TAC `moi_s86_mu (moi_s86_sc n ((K:A->real^2->bool) i)) <
                   moi_s86_mu (moi_s86_sc ((nn:A->real) b) (K b))` THEN
      SUBGOAL_THEN `!i n. i IN gg ==> moi_s86_mu (moi_s86_sc n ((K:A->real^2->bool) i)) =
                                      &2 rpow n * moi_s86_mu (K i)`
      (fun th -> SIMP_TAC[th; ASSUME `(i:A) IN gg`; ASSUME `(b:A) IN gg`]) THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&2 rpow ((nn:A->real) i) * moi_s86_mu ((K:A->real^2->bool) i) <=
                    &2 rpow n * moi_s86_mu (K i)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `i:A` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(nn:A->real) a - &1`)) (concl th))) THEN
      UNDISCH_TAC `moi_s86_mu (moi_s86_sc ((nn:A->real) a - &1) ((K:A->real^2->bool) a)) <
                   moi_s86_mu (moi_s86_sc n (K i))` THEN
      SUBGOAL_THEN `!i n. i IN gg ==> moi_s86_mu (moi_s86_sc n ((K:A->real^2->bool) i)) =
                                      &2 rpow n * moi_s86_mu (K i)`
      (fun th -> SIMP_TAC[th; ASSUME `(i:A) IN gg`; ASSUME `(a:A) IN gg`]) THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&2 rpow n * moi_s86_mu ((K:A->real^2->bool) i) <=
                    &2 rpow ((nn:A->real) i - &1) * moi_s86_mu (K i)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Descending maps through E: a PL map h on the plane that is periodic     *)
(* under (8,0) induces desc h on the punctured plane with desc h (E y) =   *)
(* h y; it is PL (local PL sections of E on small boxes) and its images   *)
(* of open sets are images under h of open sets.                            *)
(* ------------------------------------------------------------------------- *)

let moi_s86_desc = new_definition
 `moi_s86_desc (h:real^2->real^N) (z:real^2) = h (@y. moi_s86_e y = z)`;;

let MOI_S86_DESC_E = prove
 (`!h:real^2->real^N.
     (!y m. integer m ==> h(y + m % vector[&8; &0]) = h y)
     ==> !y. moi_s86_desc h (moi_s86_e y) = h y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s86_desc] THEN
  ABBREV_TAC `y' = @y':real^2. moi_s86_e y' = moi_s86_e y` THEN
  SUBGOAL_THEN `moi_s86_e y' = moi_s86_e y` MP_TAC THENL
   [EXPAND_TAC "y'" THEN CONV_TAC SELECT_CONV THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_S86_E_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN `y':real^2 = y + (((y':real^2)$1 - (y:real^2)$1) / &8) % vector[&8; &0]`
  SUBST1_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VECTOR_2] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[]]);;

let MOI_S86_E_BOX_INJ = prove
 (`!y0 y y':real^2.
     y IN interval[y0 - vector[&3; &1],y0 + vector[&3; &1]] /\
     y' IN interval[y0 - vector[&3; &1],y0 + vector[&3; &1]] /\
     moi_s86_e y = moi_s86_e y'
     ==> y = y'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MOI_S86_E_EQ; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
              VECTOR_SUB_COMPONENT; VECTOR_2] THEN
  STRIP_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `((y:real^2)$1 - (y':real^2)$1) / &8` MOI_S8C_INT_SMALL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S86_E_LOCAL_SECTION = prove
 (`!y0:real^2. ?v g. open v /\ moi_s86_e y0 IN v /\ pl_map_on v g /\
                     (!z. z IN v ==> moi_s86_e (g z) = z)`,
  GEN_TAC THEN
  ABBREV_TAC `B = interval[y0 - vector[&3; &1],y0 + vector[&3; &1]]:real^2->bool` THEN
  MP_TAC(ISPECL [`B:real^2->bool`; `moi_s86_e`; `IMAGE moi_s86_e B`] HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[MOI_S86_E_CONTINUOUS] THEN EXPAND_TAC "B" THEN
    REWRITE_TAC[COMPACT_INTERVAL] THEN MESON_TAC[MOI_S86_E_BOX_INJ];
    DISCH_THEN(X_CHOOSE_TAC `g:real^2->real^2`)] THEN
  EXISTS_TAC `IMAGE moi_s86_e (interval(y0 - vector[&3; &1],y0 + vector[&3; &1]))` THEN
  EXISTS_TAC `g:real^2->real^2` THEN
  SUBGOAL_THEN `interval(y0 - vector[&3; &1],y0 + vector[&3; &1]) SUBSET (B:real^2->bool)`
  ASSUME_TAC THENL [EXPAND_TAC "B" THEN REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE moi_s86_e (interval(y0 - vector[&3; &1],y0 + vector[&3; &1])))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[MOI_S86_E_CONTINUOUS; OPEN_INTERVAL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S86_E_BOX_INJ THEN EXISTS_TAC `y0:real^2` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "B" THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_SUB_COMPONENT; VECTOR_2] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE moi_s86_e B` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; IMAGE_SUBSET] THEN
    MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
    MAP_EVERY EXISTS_TAC [`B:real^2->bool`; `moi_s86_e`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[MOI_S86_E_PL; SUBSET_UNIV] THEN
    EXPAND_TAC "B" THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
    REWRITE_TAC[POLYTOPE_INTERVAL];
    UNDISCH_TAC `homeomorphism (B,IMAGE moi_s86_e B) (moi_s86_e,g:real^2->real^2)` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let MOI_S86_DESC_PL = prove
 (`!h:real^2->real^N.
     pl_map_on (:real^2) h /\ (!y m. integer m ==> h(y + m % vector[&8; &0]) = h y)
     ==> pl_map_on ((:real^2) DELETE vec 0) (moi_s86_desc h)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[PL_MAP_ON_LOCAL] THEN
  X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_DELETE; IN_UNIV] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y0:real^2` o MATCH_MP MOI_S86_E_ONTO) THEN
  MP_TAC(SPEC `y0:real^2` MOI_S86_E_LOCAL_SECTION) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^2->bool` (X_CHOOSE_THEN `g:real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `v:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `v:real^2->bool` THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_INTER; OPEN_DELETE; OPEN_UNIV] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `(h:real^2->real^N) o (g:real^2->real^2)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(MATCH_MP th
      (ASSUME `(w:real^2) IN v`))]) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_S86_DESC_E th]);
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let MOI_S86_DESC_IMAGE = prove
 (`!h:real^2->real^N w.
     (!y m. integer m ==> h(y + m % vector[&8; &0]) = h y) /\
     w SUBSET (:real^2) DELETE vec 0
     ==> IMAGE (moi_s86_desc h) w = IMAGE h {y | moi_s86_e y IN w}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S86_DESC_E) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `p:real^N` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(z:real^2 = vec 0)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(X_CHOOSE_TAC `y:real^2` o MATCH_MP MOI_S86_E_ONTO) THEN
    EXISTS_TAC `y:real^2` THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `moi_s86_e y` THEN ASM_MESON_TAC[]]);;

let MOI_S86_DESC_PLH = prove
 (`!h:real^2->real^N s.
     pl_map_on (:real^2) h /\ (!y m. integer m ==> h(y + m % vector[&8; &0]) = h y) /\
     pl_polyhedron s /\ s SUBSET (:real^2) DELETE vec 0 /\
     (!x y. x IN s /\ y IN s /\ moi_s86_desc h x = moi_s86_desc h y ==> x = y)
     ==> ?g. pl_homeomorphism (s,IMAGE (moi_s86_desc h) s) (moi_s86_desc h,g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_map_on s (moi_s86_desc (h:real^2->real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `(:real^2) DELETE vec 0` THEN
    ASM_SIMP_TAC[MOI_S86_DESC_PL; LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^2->bool`; `moi_s86_desc (h:real^2->real^N)`;
                 `IMAGE (moi_s86_desc (h:real^2->real^N)) s`] HOMEOMORPHISM_COMPACT) THEN
  ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT; PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^2`) THEN EXISTS_TAC `g:real^N->real^2` THEN
  ASM_REWRITE_TAC[pl_homeomorphism] THEN
  MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
  MAP_EVERY EXISTS_TAC [`s:real^2->bool`; `moi_s86_desc (h:real^2->real^N)`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cylinder coordinates for the torus model.  For a lattice basis          *)
(* {D,E} of Z^2, lam D E y = y1 D + 8 y2 E and cov D E = Q o lam D E: a PL *)
(* covering of the model with deck lattice Z (8,0) + Z (0,1); phi D E is    *)
(* the inverse of lam D E.  Q is an open map onto the model.                *)
(* ------------------------------------------------------------------------- *)

let moi_s86_lam = new_definition
 `moi_s86_lam (D:real^2) (E:real^2) (y:real^2) = y$1 % D + (&8 * y$2) % E`;;

let moi_s86_cov = new_definition
 `moi_s86_cov (D:real^2) (E:real^2) (y:real^2) = moi_s8c_q (moi_s86_lam D E y)`;;

let moi_s86_phi = new_definition
 `moi_s86_phi (D:real^2) (E:real^2) (x:real^2) =
    vector[moi_s4u_nu x E / moi_s4u_nu D E; moi_s4u_nu D x / (&8 * moi_s4u_nu D E)]:real^2`;;

let MOI_S86_LAM_LINEAR = prove
 (`!D E:real^2. linear (moi_s86_lam D E)`,
  REWRITE_TAC[linear; moi_s86_lam; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  CONJ_TAC THEN CONV_TAC REAL_RING);;

let MOI_S86_LAM_PHI = prove
 (`!D E x:real^2. ~(moi_s4u_nu D E = &0)
       ==> moi_s86_lam D E (moi_s86_phi D E x) = x /\
           moi_s86_phi D E (moi_s86_lam D E x) = x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4u_nu] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s86_lam; moi_s86_phi; moi_s4u_nu; CART_EQ; DIMINDEX_2; FORALL_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REPEAT CONJ_TAC THEN UNDISCH_TAC `~((D:real^2)$1 * (E:real^2)$2 - D$2 * E$1 = &0)` THEN
  CONV_TAC REAL_FIELD);;

let MOI_S86_PHI_LINEAR = prove
 (`!D E:real^2. linear (moi_s86_phi D E)`,
  REWRITE_TAC[linear; moi_s86_phi; moi_s4u_nu] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_2] THEN
  CONJ_TAC THEN REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING);;

let MOI_S86_PHI_8D = prove
 (`!D E x:real^2. ~(moi_s4u_nu D E = &0)
       ==> moi_s86_phi D E (x + &8 % D) = moi_s86_phi D E x + vector[&8; &0]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4u_nu] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s86_phi; moi_s4u_nu; CART_EQ; DIMINDEX_2; FORALL_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
  REPEAT CONJ_TAC THEN UNDISCH_TAC `~((D:real^2)$1 * (E:real^2)$2 - D$2 * E$1 = &0)` THEN
  CONV_TAC REAL_FIELD);;

let MOI_S86_COV_PL = prove
 (`!D E:real^2. pl_map_on (:real^2) (moi_s86_cov D E)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `moi_s86_cov D E = moi_s8c_q o moi_s86_lam D E` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; moi_s86_cov]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[MOI_S8C_Q_PL; SUBSET_UNIV] THEN
  SUBGOAL_THEN `moi_s86_lam D E = (\y. moi_s86_lam D E y + vec 0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; VECTOR_ADD_RID]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
  REWRITE_TAC[ETA_AX; MOI_S86_LAM_LINEAR] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_OPEN THEN REWRITE_TAC[OPEN_UNIV]);;

let MOI_S86_COV_EQ = prove
 (`!D E y y':real^2.
     integer(D$1) /\ integer(D$2) /\ integer(E$1) /\ integer(E$2) /\
     ~(moi_s4u_nu D E = &0) /\
     (!w:real^2. integer(w$1) /\ integer(w$2)
                 ==> ?m n. integer m /\ integer n /\ w = m % D + n % E)
     ==> (moi_s86_cov D E y = moi_s86_cov D E y' <=>
          integer((y$1 - y'$1) / &8) /\ integer(y$2 - y'$2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s86_cov; MOI_S8C_Q_EQ] THEN
  SUBGOAL_THEN `!i. ((moi_s86_lam D E y)$i - (moi_s86_lam D E y')$i) / &8 =
                    (((y:real^2)$1 - (y':real^2)$1) / &8 % D + (y$2 - y'$2) % E:real^2)$i`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[moi_s86_lam; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ABBREV_TAC `al = ((y:real^2)$1 - (y':real^2)$1) / &8` THEN
  ABBREV_TAC `be = (y:real^2)$2 - (y':real^2)$2` THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `al % D + be % E:real^2` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real` (X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(al - m) * moi_s4u_nu D E = &0 /\ (be - n) * moi_s4u_nu D E = &0`
    MP_TAC THENL
     [UNDISCH_TAC `al % D + be % E:real^2 = m % D + n % E` THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; moi_s4u_nu] THEN
      CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[REAL_ENTIRE; REAL_SUB_0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED]]);;

let MOI_S86_Q_ONTO = prove
 (`IMAGE moi_s8c_q (:real^2) = pl_torus_model`,
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_S8C_Q_IN]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; pl_torus_model; FORALL_IN_PCROSS; IN_IMAGE; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN STRIP_TAC THEN
  MP_TAC(SPEC `a:real^2` MOI_S8C_SIG_ONTO) THEN MP_TAC(SPEC `b:real^2` MOI_S8C_SIG_ONTO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `vector[s; t]:real^2` THEN
  ASM_REWRITE_TAC[moi_s8c_q; VECTOR_2]);;

let MOI_S86_Q_FUND = prove
 (`!y:real^2. ?y'. y' IN interval[vec 0,&8 % vec 1] /\ moi_s8c_q y' = moi_s8c_q y /\
                   integer((y$1 - y'$1) / &8) /\ integer((y$2 - y'$2) / &8)`,
  GEN_TAC THEN
  EXISTS_TAC `y - &8 % vector[floor((y:real^2)$1 / &8); floor(y$2 / &8)]:real^2` THEN
  REWRITE_TAC[MOI_S8C_Q_EQ; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_SUB_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT; VECTOR_2] THEN
  REWRITE_TAC[REAL_ARITH `(y - (y - &8 * f)) / &8 = f`;
              REAL_ARITH `(y - &8 * f - y) / &8 = --f`] THEN
  SIMP_TAC[FLOOR; INTEGER_CLOSED] THEN
  MP_TAC(SPEC `(y:real^2)$1 / &8` FLOOR) THEN MP_TAC(SPEC `(y:real^2)$2 / &8` FLOOR) THEN
  REAL_ARITH_TAC);;

let MOI_S86_Q_OPEN = prove
 (`!u:real^2->bool. open u
       ==> open_in (subtopology euclidean pl_torus_model) (IMAGE moi_s8c_q u)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = {y:real^2 | !x. x IN u ==> ~(moi_s8c_q x = moi_s8c_q y)}` THEN
  SUBGOAL_THEN `open {y:real^2 | ?x. x IN u /\ moi_s8c_q x = moi_s8c_q y}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_CONTAINS_BALL; IN_ELIM_THM] THEN X_GEN_TAC `y:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o REWRITE_RULE[OPEN_CONTAINS_BALL]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM] THEN
    X_GEN_TAC `y':real^2` THEN DISCH_TAC THEN
    EXISTS_TAC `x + (y' - y):real^2` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      REWRITE_TAC[IN_BALL] THEN UNDISCH_TAC `dist(y:real^2,y') < e` THEN
      REWRITE_TAC[dist; VECTOR_ARITH `x - (x + (y' - y)):real^2 = y - y'`];
      UNDISCH_TAC `moi_s8c_q x = moi_s8c_q y` THEN
      REWRITE_TAC[MOI_S8C_Q_EQ; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT] THEN
      REWRITE_TAC[REAL_ARITH `((x + (y' - y)) - y') / &8 = (x - y) / &8`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(c:real^2->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `c = (:real^2) DIFF {y:real^2 | ?x. x IN u /\ moi_s8c_q x = moi_s8c_q y}`
    SUBST1_TAC THENL
     [EXPAND_TAC "c" THEN SET_TAC[]; ASM_REWRITE_TAC[GSYM OPEN_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_torus_model DIFF IMAGE moi_s8c_q u =
                IMAGE moi_s8c_q (c INTER interval[vec 0,&8 % vec 1])` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; GSYM MOI_S86_Q_ONTO; IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `p:real^(2,2)finite_sum` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^2` ASSUME_TAC) ASSUME_TAC) THEN
      MP_TAC(SPEC `y:real^2` MOI_S86_Q_FUND) THEN
      DISCH_THEN(X_CHOOSE_THEN `y':real^2` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `y':real^2` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      EXPAND_TAC "c" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(?x:real^2. p = moi_s8c_q x /\ x IN u)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_INTER; MOI_S8C_Q_IN] THEN
      X_GEN_TAC `y:real^2` THEN EXPAND_TAC "c" THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
      STRIP_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `x:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE moi_s8c_q u = pl_torus_model DIFF
                IMAGE moi_s8c_q (c INTER interval[vec 0,&8 % vec 1])` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(MOI_S86_Q_ONTO) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_S8C_Q_IN]; ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
    REWRITE_TAC[MOI_S8C_Q_PL];
    MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[COMPACT_INTERVAL]]);;

(* ------------------------------------------------------------------------- *)
(* Inverting PL maps that are injective on small polytopes: a compact      *)
(* set k on which f is injective, mapped onto a polyhedron, is PL           *)
(* homeomorphic to its image (the inverse is locally the inverse of f on a  *)
(* small polytope).  The descended covering is locally injective.           *)
(* ------------------------------------------------------------------------- *)

let MOI_S86_LOCAL_INJ_PLH = prove
 (`!(f:real^M->real^N) w k.
     open w /\ pl_map_on w f /\
     (!z. z IN w ==> ?b. polytope b /\ b SUBSET w /\ z IN interior b /\
                         (!x y. x IN b /\ y IN b /\ f x = f y ==> x = y)) /\
     compact k /\ k SUBSET w /\ (!x y. x IN k /\ y IN k /\ f x = f y ==> x = y) /\
     pl_polyhedron (IMAGE f k)
     ==> ?g. pl_homeomorphism (IMAGE f k,k) (g,f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) continuous_on w` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^M->bool`; `f:real^M->real^N`; `IMAGE (f:real^M->real^N) k`]
    HOMEOMORPHISM_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^M->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^M`)] THEN
  EXISTS_TAC `g:real^N->real^M` THEN
  SUBGOAL_THEN `homeomorphism (IMAGE (f:real^M->real^N) k,k) (g,f)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (IMAGE (f:real^M->real^N) k) (g:real^N->real^M)` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
      concl th = `homeomorphism (k,IMAGE (f:real^M->real^N) k) (f,g)`)) THEN
    ONCE_REWRITE_TAC[PL_MAP_ON_LOCAL] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^N->real^M) p IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^N->real^M) p` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `polytope:(real^M->bool)->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^M->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`b:real^M->bool`; `f:real^M->real^N`; `IMAGE (f:real^M->real^N) b`]
      HOMEOMORPHISM_COMPACT) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `w:real^M->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_TAC `sg:real^N->real^M`)] THEN
    SUBGOAL_THEN `pl_map_on (IMAGE (f:real^M->real^N) b) (sg:real^N->real^M)` ASSUME_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
      MAP_EVERY EXISTS_TAC [`b:real^M->bool`; `f:real^M->real^N`] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `w:real^M->bool` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`g:real^N->real^M`; `IMAGE (f:real^M->real^N) k`;
                   `interior(b:real^M->bool)`] CONTINUOUS_OPEN_IN_PREIMAGE) THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `sg:real^N->real^M` THEN CONJ_TAC THENL
     [X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `q IN IMAGE (f:real^M->real^N) k /\ (g:real^N->real^M) q IN interior b`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^N->real^M) q IN b` ASSUME_TAC THENL
       [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      UNDISCH_TAC `homeomorphism (b,IMAGE (f:real^M->real^N) b) (f,sg)` THEN
      REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(f:real^M->real^N) ((g:real^N->real^M) q) = q` (fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE (f:real^M->real^N) b` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `q:real^N` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(g:real^N->real^M) q IN interior b` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^N->real^M) q` THEN
        ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
        MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN
        ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_homeomorphism] THEN
  MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (f:real^M->real^N) k`; `g:real^N->real^M`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S86_COV_FACTS = prove
 (`!D E:real^2.
     integer(D$1) /\ integer(D$2) /\ integer(E$1) /\ integer(E$2) /\
     ~(moi_s4u_nu D E = &0) /\
     (!w:real^2. integer(w$1) /\ integer(w$2)
                 ==> ?m n. integer m /\ integer n /\ w = m % D + n % E)
     ==> (!y m. integer m ==> moi_s86_cov D E (y + m % vector[&8; &0]) = moi_s86_cov D E y) /\
         (!y n. integer n ==> moi_s86_cov D E (y + n % vector[&0; &1]) = moi_s86_cov D E y) /\
         IMAGE (moi_s86_cov D E) (:real^2) = pl_torus_model /\
         (!u. open u ==> open_in (subtopology euclidean pl_torus_model)
                                 (IMAGE (moi_s86_cov D E) u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_COV_EQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    REWRITE_TAC[REAL_ARITH `((y + m * &8) - y) / &8 = m`; REAL_MUL_RZERO; REAL_ADD_RID;
                REAL_SUB_REFL] THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    REWRITE_TAC[REAL_ARITH `(y + n * &1) - y = n`; REAL_MUL_RZERO; REAL_ADD_RID;
                REAL_SUB_REFL; REAL_ARITH `&0 / &8 = &0`] THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED];
    REWRITE_TAC[GSYM MOI_S86_Q_ONTO] THEN
    SUBGOAL_THEN `moi_s86_cov D E = moi_s8c_q o moi_s86_lam D E` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; moi_s86_cov]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `x:real^2` THEN
    EXISTS_TAC `moi_s86_phi D E x` THEN ASM_SIMP_TAC[MOI_S86_LAM_PHI];
    X_GEN_TAC `u:real^2->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (moi_s86_cov D E) u = IMAGE moi_s8c_q (IMAGE (moi_s86_lam D E) u)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; moi_s86_cov];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S86_Q_OPEN THEN
    MP_TAC(ISPECL [`moi_s86_lam D E`; `u:real^2->bool`] OPEN_BIJECTIVE_LINEAR_IMAGE_EQ) THEN
    ASM_REWRITE_TAC[MOI_S86_LAM_LINEAR] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:real^2`; `b:real^2`] THEN DISCH_TAC THEN
      MP_TAC(SPECL [`D:real^2`; `E:real^2`; `a:real^2`] MOI_S86_LAM_PHI) THEN
      MP_TAC(SPECL [`D:real^2`; `E:real^2`; `b:real^2`] MOI_S86_LAM_PHI) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      X_GEN_TAC `b:real^2` THEN EXISTS_TAC `moi_s86_phi D E b` THEN
      ASM_SIMP_TAC[MOI_S86_LAM_PHI]]]);;

let MOI_S86_DESC_COV = prove
 (`!D E:real^2.
     integer(D$1) /\ integer(D$2) /\ integer(E$1) /\ integer(E$2) /\
     ~(moi_s4u_nu D E = &0) /\
     (!w:real^2. integer(w$1) /\ integer(w$2)
                 ==> ?m n. integer m /\ integer n /\ w = m % D + n % E)
     ==> !y. moi_s86_desc (moi_s86_cov D E) (moi_s86_e y) = moi_s86_cov D E y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S86_DESC_E THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MOI_S86_COV_FACTS th)]));;

let MOI_S86_DESC_LOCAL_INJ = prove
 (`!D E:real^2.
     integer(D$1) /\ integer(D$2) /\ integer(E$1) /\ integer(E$2) /\
     ~(moi_s4u_nu D E = &0) /\
     (!w:real^2. integer(w$1) /\ integer(w$2)
                 ==> ?m n. integer m /\ integer n /\ w = m % D + n % E)
     ==> !z. z IN (:real^2) DELETE vec 0
             ==> ?b. polytope b /\ b SUBSET (:real^2) DELETE vec 0 /\ z IN interior b /\
                     (!x y. x IN b /\ y IN b /\
                            moi_s86_desc (moi_s86_cov D E) x =
                            moi_s86_desc (moi_s86_cov D E) y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_COV_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_COV_EQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_DELETE; IN_UNIV] THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y0:real^2` o MATCH_MP MOI_S86_E_ONTO) THEN
  ABBREV_TAC `C = interval[y0 - vector[&3; &1 / &4],y0 + vector[&3; &1 / &4]]:real^2->bool` THEN
  SUBGOAL_THEN `!y y':real^2. y IN C /\ y' IN C /\ moi_s86_cov D E y = moi_s86_cov D E y'
                              ==> y = y'` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_SUB_COMPONENT; VECTOR_2] THEN
    STRIP_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    MP_TAC(SPEC `((y:real^2)$1 - (y':real^2)$1) / &8` MOI_S8C_INT_SMALL) THEN
    MP_TAC(SPEC `(y:real^2)$2 - (y':real^2)$2` MOI_S8C_INT_SMALL) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y y':real^2. y IN C /\ y' IN C /\ moi_s86_e y = moi_s86_e y' ==> y = y'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s86_e y = moi_s86_e y'` THEN
    REWRITE_TAC[MOI_S86_E_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE moi_s86_e (interior C))` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[MOI_S86_E_CONTINUOUS; OPEN_INTERIOR] THEN
    MP_TAC(ISPEC `C:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^2) IN IMAGE moi_s86_e (interior C)` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `z:real^2`)) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[INTERIOR_INTERVAL; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_SUB_COMPONENT; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[OPEN_CONTAINS_BALL] o check (fun th ->
    concl th = `open(IMAGE moi_s86_e (interior C))`)) THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `interval[z - (e / &3) % vector[&1; &1],z + (e / &3) % vector[&1; &1]]:real^2->bool` THEN
  SUBGOAL_THEN `interval[z - (e / &3) % vector[&1; &1],z + (e / &3) % vector[&1; &1]] SUBSET
                IMAGE moi_s86_e (interior C)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(z:real^2,e)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; IN_BALL; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2; dist] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    MP_TAC(ISPEC `z - x:real^2` NORM_LE_L1) THEN
    REWRITE_TAC[DIMINDEX_2; SUM_2; VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[POLYTOPE_INTERVAL];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE moi_s86_e (interior C)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV; MOI_S86_E_NONZERO];
    REWRITE_TAC[INTERIOR_INTERVAL; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
                VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^2`; `x':real^2`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN IMAGE moi_s86_e (interior C) /\
                  (x':real^2) IN IMAGE moi_s86_e (interior C)` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`interval[z - (e / &3) % vector[&1; &1],z + (e / &3) % vector[&1; &1]] SUBSET
         IMAGE moi_s86_e (interior C)`;
        `(x:real^2) IN interval[z - (e / &3) % vector[&1; &1],z + (e / &3) % vector[&1; &1]]`;
        `(x':real^2) IN interval[z - (e / &3) % vector[&1; &1],z + (e / &3) % vector[&1; &1]]`] THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `y':real^2` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `moi_s86_desc (moi_s86_cov D E) x = moi_s86_desc (moi_s86_cov D E) x'` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_DESC_COV) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(ASSUME `!y y':real^2. y IN C /\ y' IN C /\
                                      moi_s86_cov D E y = moi_s86_cov D E y' ==> y = y'`) THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `C:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y:real^2) IN interior C` THEN SET_TAC[];
      MP_TAC(ISPEC `C:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y':real^2) IN interior C` THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The members as periodic lines in cylinder coordinates.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S86_E_SCALE_INT = prove
 (`!x:real^2 n. integer n ==> moi_s86_e (x + n % vector[&0; &1]) = (&2 rpow n) % moi_s86_e x`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s86_e; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2;
              REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
  SUBGOAL_THEN `floor((x:real^2)$2 + n) = floor(x$2) + n` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_S8C_FLOOR_ADD THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(x + n) - (f + n) = x - f`] THEN
  SIMP_TAC[RPOW_ADD; REAL_ARITH `&0 < &2`] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC REAL_RING);;

let MOI_S86_DISP_REVERSE = prove
 (`!g:real^1->real^(2,2)finite_sum.
     path g /\ pathfinish g = pathstart g /\ path_image g SUBSET pl_torus_model
     ==> moi_s4u_disp (moi_s8c_bpsi o reversepath g) = --(moi_s4u_disp (moi_s8c_bpsi o g))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_s8c_bpsi o reversepath g = reversepath (moi_s8c_bpsi o g)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; reversepath]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4U_DISP_REVERSEPATH THEN
  MP_TAC(ISPEC `g:real^1->real^(2,2)finite_sum` MOI_S86_BPSI_LOOP) THEN ASM_SIMP_TAC[]);;

let MOI_S86_SETUP = prove
 (`!gg:(real^(2,2)finite_sum->bool)->bool.
     ~(gg = {}) /\ pairwise DISJOINT gg /\
     (!c. c IN gg
          ==> c SUBSET pl_torus_model /\ pl_sphere 1 c /\
              (?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET c /\
                   ~homotopic_loops pl_torus_model k (linepath(pathstart k,pathstart k))))
     ==> ?D E (L:(real^(2,2)finite_sum->bool)->real^1->real^2).
           integer(D$1) /\ integer(D$2) /\ integer(E$1) /\ integer(E$2) /\
           &0 < moi_s4u_nu D E /\
           (!w:real^2. integer(w$1) /\ integer(w$2)
                       ==> ?m n. integer m /\ integer n /\ w = m % D + n % E) /\
           (!c. c IN gg
                ==> path (L c) /\ pathfinish (L c) = pathstart (L c) + vector[&8; &0] /\
                    IMAGE (moi_s86_cov D E) (path_image (L c)) = c /\
                    (!s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                           moi_s86_cov D E (L c s) = moi_s86_cov D E (L c t)
                           ==> s = t \/ (s = vec 0 /\ t = vec 1) \/ (s = vec 1 /\ t = vec 0)))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!c. c IN gg
        ==> ?g:real^1->real^(2,2)finite_sum.
              simple_path g /\ pathfinish g = pathstart g /\ path_image g = c /\
              integer((moi_s4u_disp (moi_s8c_bpsi o g))$1) /\
              integer((moi_s4u_disp (moi_s8c_bpsi o g))$2) /\
              ~(moi_s4u_disp (moi_s8c_bpsi o g) = vec 0)`
  MP_TAC THENL
   [X_GEN_TAC `c:real^(2,2)finite_sum->bool` THEN DISCH_TAC THEN
    MP_TAC(SPEC `c:real^(2,2)finite_sum->bool` MOI_S86_PARAM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^(2,2)finite_sum` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `g:real^1->real^(2,2)finite_sum` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `gp:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum`) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `c0:real^(2,2)finite_sum->bool` o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ABBREV_TAC `D = moi_s4u_disp (moi_s8c_bpsi o gp (c0:real^(2,2)finite_sum->bool))` THEN
  SUBGOAL_THEN `simple_path ((gp:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c0) /\
                pathfinish (gp c0) = pathstart (gp c0) /\ path_image (gp c0) = c0 /\
                integer((D:real^2)$1) /\ integer(D$2) /\ ~(D = vec 0) /\
                c0 SUBSET pl_torus_model`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  (* D is primitive, so a lattice basis {D,E} exists *)
  MP_TAC(SPEC `D:real^2` MOI_S86_BASIS) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`moi_s8c_bpsi o (gp:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c0`;
                   `w:real^2`] MOI_S4U_TT_PRIMITIVE) THEN
    MP_TAC(ISPEC `(gp:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c0`
      MOI_S86_BPSI_LOOP) THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH; SUBSET_REFL];
    DISCH_THEN(X_CHOOSE_THEN `E:real^2` STRIP_ASSUME_TAC)] THEN
  (* each member has a parametrisation with displacement exactly D *)
  SUBGOAL_THEN
   `!c. c IN gg
        ==> ?g:real^1->real^(2,2)finite_sum.
              simple_path g /\ pathfinish g = pathstart g /\ path_image g = c /\
              moi_s4u_disp (moi_s8c_bpsi o g) = D`
  MP_TAC THENL
   [X_GEN_TAC `c:real^(2,2)finite_sum->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `simple_path ((gp:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c) /\
                  pathfinish (gp c) = pathstart (gp c) /\ path_image (gp c) = c /\
                  ~(moi_s4u_disp (moi_s8c_bpsi o gp c) = vec 0) /\ c SUBSET pl_torus_model`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_s4u_disp (moi_s8c_bpsi o
                    (gp:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c) = D \/
                  moi_s4u_disp (moi_s8c_bpsi o gp c) = --D`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `c:real^(2,2)finite_sum->bool = c0` THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "D" THEN MATCH_MP_TAC MOI_S86_COMMON_DISP THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `pairwise DISJOINT (gg:(real^(2,2)finite_sum->bool)->bool)` THEN
      REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[];
      EXISTS_TAC `(gp:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c` THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `reversepath((gp:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c)` THEN
      ASM_SIMP_TAC[SIMPLE_PATH_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                   PATH_IMAGE_REVERSEPATH] THEN
      MP_TAC(ISPEC `(gp:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c`
        MOI_S86_DISP_REVERSE) THEN
      ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH; SUBSET_REFL; VECTOR_NEG_NEG]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `go:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum`) THEN
  (* the lifts through Q *)
  SUBGOAL_THEN
   `!c. c IN gg
        ==> ?G:real^1->real^2.
              path G /\ pathfinish G = pathstart G + &8 % D /\
              !t. t IN interval[vec 0,vec 1]
                  ==> moi_s8c_q (G t) =
                      (go:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c t`
  MP_TAC THENL
   [X_GEN_TAC `c:real^(2,2)finite_sum->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `(go:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c`
      MOI_S8C_Q_LIFT) THEN
    SUBGOAL_THEN `simple_path ((go:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c) /\
                  pathfinish (go c) = pathstart (go c) /\ path_image (go c) = c /\
                  moi_s4u_disp (moi_s8c_bpsi o go c) = D /\ c SUBSET pl_torus_model`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SIMPLE_PATH_IMP_PATH; SUBSET_REFL] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_TAC `Gl:(real^(2,2)finite_sum->bool)->real^1->real^2`) THEN
  SUBGOAL_THEN `~(moi_s4u_nu D E = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`D:real^2`; `E:real^2`;
    `\c:real^(2,2)finite_sum->bool. moi_s86_phi D E o
       (Gl:(real^(2,2)finite_sum->bool)->real^1->real^2) c`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:real^(2,2)finite_sum->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `simple_path ((go:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c) /\
                pathfinish (go c) = pathstart (go c) /\ path_image (go c) = c /\
                path ((Gl:(real^(2,2)finite_sum->bool)->real^1->real^2) c) /\
                pathfinish (Gl c) = pathstart (Gl c) + &8 % D /\
                (!t. t IN interval[vec 0,vec 1] ==> moi_s8c_q (Gl c t) = go c t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1]
                    ==> moi_s86_cov D E ((moi_s86_phi D E o
                          (Gl:(real^(2,2)finite_sum->bool)->real^1->real^2) c) t) =
                        (go:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c t`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[o_THM; moi_s86_cov; MOI_S86_LAM_PHI]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MOI_S86_PHI_LINEAR];
    ASM_SIMP_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; MOI_S86_PHI_8D];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `path_image ((go:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[path_image; GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
      REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_s86_cov`)) (concl th))) THEN
      ASM_REWRITE_TAC[o_THM];
      ASM_MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`] THEN STRIP_TAC THEN
    UNDISCH_TAC `simple_path ((go:(real^(2,2)finite_sum->bool)->real^1->real^(2,2)finite_sum) c)` THEN
    REWRITE_TAC[simple_path] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The lifted members in the punctured plane: moi_s86_ctx collects the      *)
(* setup; the images E o (L c) are Jordan curves around 0, their scaled     *)
(* copies are pairwise disjoint, they are exactly the preimages of the      *)
(* members under the descended covering, and they are PL circles.           *)
(* ------------------------------------------------------------------------- *)

let moi_s86_ctx = new_definition
 `moi_s86_ctx (gg:(real^(2,2)finite_sum->bool)->bool) (D:real^2) (E:real^2)
              (L:(real^(2,2)finite_sum->bool)->real^1->real^2) <=>
    FINITE gg /\ pairwise DISJOINT gg /\
    (!c. c IN gg ==> c SUBSET pl_torus_model /\ pl_sphere 1 c) /\
    integer(D$1) /\ integer(D$2) /\ integer(E$1) /\ integer(E$2) /\ &0 < moi_s4u_nu D E /\
    (!w:real^2. integer(w$1) /\ integer(w$2)
                ==> ?m n. integer m /\ integer n /\ w = m % D + n % E) /\
    (!c. c IN gg
         ==> path (L c) /\ pathfinish (L c) = pathstart (L c) + vector[&8; &0] /\
             IMAGE (moi_s86_cov D E) (path_image (L c)) = c /\
             (!s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                    moi_s86_cov D E (L c s) = moi_s86_cov D E (L c t)
                    ==> s = t \/ (s = vec 0 /\ t = vec 1) \/ (s = vec 1 /\ t = vec 0)))`;;

let MOI_S86_CTX_BASIS = prove
 (`!gg D E L. moi_s86_ctx gg D E L
              ==> integer(D$1) /\ integer(D$2) /\ integer(E$1) /\ integer(E$2) /\
                  ~(moi_s4u_nu D E = &0) /\
                  (!w:real^2. integer(w$1) /\ integer(w$2)
                              ==> ?m n. integer m /\ integer n /\ w = m % D + n % E)`,
  REWRITE_TAC[moi_s86_ctx] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S86_CTX_JORDAN = prove
 (`!gg D E L c. moi_s86_ctx gg D E L /\ c IN gg
                ==> simple_path (moi_s86_e o L c) /\
                    pathfinish (moi_s86_e o L c) = pathstart (moi_s86_e o L c) /\
                    path_image (moi_s86_e o L c) homeomorphic sphere(vec 0:real^2,&1) /\
                    vec 0 IN inside(path_image (moi_s86_e o L c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_BASIS) THEN
  MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_COV_EQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `moi_s86_ctx gg D E L` THEN REWRITE_TAC[moi_s86_ctx] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^(2,2)finite_sum->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `L:(real^(2,2)finite_sum->bool)->real^1->real^2`))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `(L:(real^(2,2)finite_sum->bool)->real^1->real^2) c` MOI_S86_JORDAN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; INTEGER_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_VEC_0] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHIC_SIMPLE_PATH_IMAGE_CIRCLE THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let MOI_S86_CTX_FACTS = prove
 (`!gg D E L. moi_s86_ctx gg D E L
     ==> (!y y'. moi_s86_cov D E y = moi_s86_cov D E y' <=>
                 integer((y$1 - y'$1) / &8) /\ integer(y$2 - y'$2)) /\
         (!y. moi_s86_desc (moi_s86_cov D E) (moi_s86_e y) = moi_s86_cov D E y) /\
         (!y n. integer n ==> moi_s86_cov D E (y + n % vector[&0; &1]) = moi_s86_cov D E y) /\
         (!c. c IN gg
              ==> c SUBSET pl_torus_model /\ pl_sphere 1 c /\
                  path (L c) /\ pathfinish (L c) = pathstart (L c) + vector[&8; &0] /\
                  IMAGE (moi_s86_cov D E) (path_image (L c)) = c /\
                  (!s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                         moi_s86_cov D E (L c s) = moi_s86_cov D E (L c t)
                         ==> s = t \/ (s = vec 0 /\ t = vec 1) \/ (s = vec 1 /\ t = vec 0)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_BASIS) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC MOI_S86_COV_EQ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S86_DESC_COV THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_COV_FACTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ACCEPT_TAC o CONJUNCT1 o CONJUNCT2);
    UNDISCH_TAC `moi_s86_ctx gg D E L` THEN REWRITE_TAC[moi_s86_ctx] THEN
    STRIP_TAC THEN X_GEN_TAC `c:real^(2,2)finite_sum->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^(2,2)finite_sum->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `L:(real^(2,2)finite_sum->bool)->real^1->real^2`))
        (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^(2,2)finite_sum->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `pl_torus_model`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_S86_E_LIFT_SHIFT = prove
 (`!x:real^2 n. integer n
       ==> moi_s86_e (x + n % vector[&0; &1]) = (&2 rpow n) % moi_s86_e x /\
           (x + n % vector[&0; &1])$1 = x$1 /\ (x + n % vector[&0; &1])$2 = x$2 + n`,
  SIMP_TAC[MOI_S86_E_SCALE_INT; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2;
           REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID]);;

let MOI_S86_SC_PATH_IMAGE = prove
 (`!(g:real^1->real^2) n z.
     z IN moi_s86_sc n (path_image (moi_s86_e o g)) <=>
     ?t. t IN interval[vec 0,vec 1] /\ z = (&2 rpow n) % moi_s86_e (g t)`,
  REWRITE_TAC[moi_s86_sc; path_image; IN_IMAGE; o_THM] THEN MESON_TAC[]);;

let MOI_S86_CTX_PRE = prove
 (`!gg D E L c z.
     moi_s86_ctx gg D E L /\ c IN gg /\ ~(z = vec 0)
     ==> (moi_s86_desc (moi_s86_cov D E) z IN c <=>
          ?n. integer n /\ z IN moi_s86_sc n (path_image (moi_s86_e o L c)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_FACTS) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^(2,2)finite_sum->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `L:(real^(2,2)finite_sum->bool)->real^1->real^2`))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y:real^2` o MATCH_MP MOI_S86_E_ONTO) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `moi_s86_e y = z`)) THEN
  ASM_REWRITE_TAC[MOI_S86_SC_PATH_IMAGE] THEN
  FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) o check (fun th ->
    concl th = `IMAGE (moi_s86_cov D E) (path_image ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c)) = c`)) THEN
  REWRITE_TAC[path_image; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^2` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `moi_s86_cov D E y = moi_s86_cov D E x` THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN EXISTS_TAC `(y:real^2)$2 - ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c t)$2` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM MOI_S86_E_SCALE_INT] THEN REWRITE_TAC[MOI_S86_E_EQ] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `n:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `(L:(real^(2,2)finite_sum->bool)->real^1->real^2) c t` THEN
    CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC `moi_s86_e y = &2 rpow n %
                  moi_s86_e ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c t)` THEN
    ASM_SIMP_TAC[GSYM MOI_S86_E_SCALE_INT] THEN REWRITE_TAC[MOI_S86_E_EQ] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_ARITH `(a + n) - a:real = n`]]);;

let MOI_S86_CTX_ENDS = prove
 (`!gg D E L c. moi_s86_ctx gg D E L /\ c IN gg
       ==> !s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                 moi_s86_cov D E (L c s) = moi_s86_cov D E (L c t)
                 ==> ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c s)$2 = (L c t)$2 /\
                     moi_s86_e (L c s) = moi_s86_e (L c t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_FACTS) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^(2,2)finite_sum->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `L:(real^(2,2)finite_sum->bool)->real^1->real^2`))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^1`; `t:real^1`] o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `vec 1:real^1`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(L:(real^(2,2)finite_sum->bool)->real^1->real^2) c (vec 1) =
                L c (vec 0) + &1 % vector[&8; &0]` ASSUME_TAC THENL
   [UNDISCH_TAC `pathfinish ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c) =
                 pathstart (L c) + vector[&8; &0]` THEN
    REWRITE_TAC[pathstart; pathfinish; VECTOR_MUL_LID];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOI_S86_E_PERIODIC; INTEGER_CLOSED] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S86_CTX_DISJ = prove
 (`!gg D E L c c' m n.
     moi_s86_ctx gg D E L /\ c IN gg /\ c' IN gg /\ integer m /\ integer n /\
     ~(c = c' /\ m = n)
     ==> DISJOINT (moi_s86_sc m (path_image (moi_s86_e o L c)))
                  (moi_s86_sc n (path_image (moi_s86_e o L c')))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_FACTS) THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; MOI_S86_SC_PATH_IMAGE] THEN
  X_GEN_TAC `w:real^2` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `moi_s86_e ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c s + m % vector[&0; &1]) =
    moi_s86_e (L c' t + n % vector[&0; &1])`
  MP_TAC THENL
   [ASM_SIMP_TAC[MOI_S86_E_SCALE_INT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MOI_S86_E_EQ] THEN ASM_SIMP_TAC[MOI_S86_E_LIFT_SHIFT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s86_cov D E ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c s) =
                moi_s86_cov D E (L c' t)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c s)$2 - (L c' t)$2 = n - m`
    SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[INTEGER_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d r. d IN gg /\ r IN interval[vec 0,vec 1]
          ==> moi_s86_cov D E ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) d r) IN d`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:real^(2,2)finite_sum->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `vec 1:real^1`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) o check (fun th ->
      is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (lhs(concl th)))) THEN
    REWRITE_TAC[path_image; IN_IMAGE] THEN
    EXISTS_TAC `(L:(real^(2,2)finite_sum->bool)->real^1->real^2) d r` THEN REWRITE_TAC[] THEN
    EXISTS_TAC `r:real^1` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c:real^(2,2)finite_sum->bool = c'` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_s86_ctx gg D E L` THEN REWRITE_TAC[moi_s86_ctx; pairwise] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:real^(2,2)finite_sum->bool`; `c':real^(2,2)finite_sum->bool`] o
      CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC
      `moi_s86_cov D E ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c s)`) THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `c':real^(2,2)finite_sum->bool`]
    MOI_S86_CTX_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:real^1`; `t:real^1`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `~(c':real^(2,2)finite_sum->bool = c' /\ m:real = n)` THEN REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S86_CTX_CURVE = prove
 (`!gg D E L c n.
     moi_s86_ctx gg D E L /\ c IN gg /\ integer n
     ==> (!x y. x IN moi_s86_sc n (path_image (moi_s86_e o L c)) /\
                y IN moi_s86_sc n (path_image (moi_s86_e o L c)) /\
                moi_s86_desc (moi_s86_cov D E) x = moi_s86_desc (moi_s86_cov D E) y
                ==> x = y) /\
         IMAGE (moi_s86_desc (moi_s86_cov D E))
               (moi_s86_sc n (path_image (moi_s86_e o L c))) = c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_FACTS) THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `c:real^(2,2)finite_sum->bool`]
    MOI_S86_CTX_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^(2,2)finite_sum->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `vec 1:real^1`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!t. moi_s86_desc (moi_s86_cov D E)
          ((&2 rpow n) % moi_s86_e ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c t)) =
        moi_s86_cov D E (L c t)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    ASM_SIMP_TAC[GSYM MOI_S86_E_SCALE_INT; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                 VECTOR_2; REAL_MUL_RZERO; REAL_ADD_RID; REAL_MUL_RID; REAL_SUB_REFL;
                 REAL_ARITH `&0 / &8 = &0`; INTEGER_CLOSED;
                 REAL_ARITH `(a + n) - a:real = n`];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_S86_SC_PATH_IMAGE] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^1` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^1`; `t:real^1`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `moi_s86_e`)) (concl th) &&
      can (find_term ((=) `vec 1:real^1`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_S86_SC_PATH_IMAGE] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) o check (fun th ->
        is_eq(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (lhs(concl th)))) THEN
      REWRITE_TAC[path_image; IN_IMAGE] THEN
      EXISTS_TAC `(L:(real^(2,2)finite_sum->bool)->real^1->real^2) c t` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) o check (fun th ->
        is_eq(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (lhs(concl th)))) THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `p:real^(2,2)finite_sum` THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[path_image; IN_IMAGE]) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(&2 rpow n) % moi_s86_e ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c t)` THEN
      ASM_REWRITE_TAC[MOI_S86_SC_PATH_IMAGE; REAL_SUB_REFL; REAL_ARITH `&0 / &8 = &0`;
                      INTEGER_CLOSED] THEN
      EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[]]]);;

let MOI_S86_CTX_SPHERE = prove
 (`!gg D E L c n.
     moi_s86_ctx gg D E L /\ c IN gg /\ integer n
     ==> pl_sphere 1 (moi_s86_sc n (path_image (moi_s86_e o L c)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_BASIS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_FACTS) THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `c:real^(2,2)finite_sum->bool`;
                `n:real`] MOI_S86_CTX_CURVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `c:real^(2,2)finite_sum->bool`]
    MOI_S86_CTX_JORDAN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:real`; `path_image (moi_s86_e o (L:(real^(2,2)finite_sum->bool)->real^1->real^2) c)`]
    MOI_S86_SC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c SUBSET pl_torus_model /\ pl_sphere 1 (c:real^(2,2)finite_sum->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s86_desc (moi_s86_cov D E)`; `(:real^2) DELETE vec 0`;
                 `moi_s86_sc n (path_image (moi_s86_e o (L:(real^(2,2)finite_sum->bool)->real^1->real^2) c))`]
    MOI_S86_LOCAL_INJ_PLH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SIMP_TAC[OPEN_DELETE; OPEN_UNIV];
      MATCH_MP_TAC MOI_S86_DESC_PL THEN REWRITE_TAC[MOI_S86_COV_PL] THEN
      MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_COV_FACTS) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
      MATCH_MP_TAC MOI_S86_DESC_LOCAL_INJ THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV] THEN ASM_MESON_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `1` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g:real^(2,2)finite_sum->real^2`) THEN
  MATCH_MP_TAC(INST_TYPE [`:(2,2)finite_sum`,`:M`] MOI_FM3_PL_SPHERE_TRANSFER) THEN
  MAP_EVERY EXISTS_TAC [`c:real^(2,2)finite_sum->bool`; `g:real^(2,2)finite_sum->real^2`;
                        `moi_s86_desc (moi_s86_cov D E)`] THEN
  ASM_REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The region between two consecutive lifted curves: the descended          *)
(* covering is injective on it, and maps it onto the closure of the         *)
(* complementary component, an annulus with two different members as ends. *)
(* ------------------------------------------------------------------------- *)

let MOI_S86_ABOVE = prove
 (`!gg D E L a b p q.
     moi_s86_ctx gg D E L /\ a IN gg /\ b IN gg /\ ~(a = b) /\ integer p /\ integer q /\
     moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
     inside(moi_s86_sc q (path_image (moi_s86_e o L b))) /\
     (!i n. i IN gg /\ integer n
            ==> ~(moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
                  inside(moi_s86_sc n (path_image (moi_s86_e o L i))) /\
                  moi_s86_sc n (path_image (moi_s86_e o L i)) SUBSET
                  inside(moi_s86_sc q (path_image (moi_s86_e o L b)))))
     ==> moi_s86_sc q (path_image (moi_s86_e o L b)) SUBSET
         inside(moi_s86_sc (p + &1) (path_image (moi_s86_e o L a)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`]
    MOI_S86_CTX_JORDAN) THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `b:real^(2,2)finite_sum->bool`]
    MOI_S86_CTX_JORDAN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_s86_sc q (path_image (moi_s86_e o
                    (L:(real^(2,2)finite_sum->bool)->real^1->real^2) b))`;
                 `moi_s86_sc (p + &1) (path_image (moi_s86_e o
                    (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a))`]
    MOI_S5C_JORDAN_NEST) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S86_SC_FACTS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                     `L:(real^(2,2)finite_sum->bool)->real^1->real^2`;
                     `b:real^(2,2)finite_sum->bool`; `a:real^(2,2)finite_sum->bool`;
                     `q:real`; `p + &1`] MOI_S86_CTX_DISJ) THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_MESON_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `vec 0:real^2` THEN
      ASM_SIMP_TAC[MOI_S86_SC_FACTS]];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  SUBGOAL_THEN
   `moi_s86_sc p (path_image (moi_s86_e o (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a))
    SUBSET inside(moi_s86_sc (p + &1) (path_image (moi_s86_e o L a)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S86_SC_NEST THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                  `L:(real^(2,2)finite_sum->bool)->real^1->real^2`;
                  `a:real^(2,2)finite_sum->bool`; `a:real^(2,2)finite_sum->bool`;
                  `p:real`; `p + &1`] MOI_S86_CTX_DISJ) THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^(2,2)finite_sum->bool`; `p + &1`] o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "inside"))
      (concl th))) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;

let MOI_S86_REGION_SHIFT = prove
 (`!gg D E L a b p q k.
     moi_s86_ctx gg D E L /\ a IN gg /\ b IN gg /\ ~(a = b) /\ integer p /\ integer q /\
     moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
     inside(moi_s86_sc q (path_image (moi_s86_e o L b))) /\
     (!i n. i IN gg /\ integer n
            ==> ~(moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
                  inside(moi_s86_sc n (path_image (moi_s86_e o L i))) /\
                  moi_s86_sc n (path_image (moi_s86_e o L i)) SUBSET
                  inside(moi_s86_sc q (path_image (moi_s86_e o L b))))) /\
     integer k /\ &1 <= k
     ==> !w. w IN (moi_s86_sc q (path_image (moi_s86_e o L b)) UNION
                   inside(moi_s86_sc q (path_image (moi_s86_e o L b)))) DIFF
                  inside(moi_s86_sc p (path_image (moi_s86_e o L a)))
             ==> ~(inv(&2 rpow k) % w IN
                   (moi_s86_sc q (path_image (moi_s86_e o L b)) UNION
                    inside(moi_s86_sc q (path_image (moi_s86_e o L b)))) DIFF
                   inside(moi_s86_sc p (path_image (moi_s86_e o L a))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Ka = path_image (moi_s86_e o (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a)` THEN
  ABBREV_TAC `Kb = path_image (moi_s86_e o (L:(real^(2,2)finite_sum->bool)->real^1->real^2) b)` THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`]
    MOI_S86_CTX_JORDAN) THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `b:real^(2,2)finite_sum->bool`]
    MOI_S86_CTX_JORDAN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`;
                `b:real^(2,2)finite_sum->bool`; `p:real`; `q:real`] MOI_S86_ABOVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `inside(moi_s86_sc (p + &1) Ka) SUBSET inside(moi_s86_sc (p + k) Ka)`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `k = &1` THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
    MP_TAC(ISPECL [`moi_s86_sc (p + &1) Ka`; `moi_s86_sc (p + k) Ka`] MOI_S5C_NESTED_INSIDE) THEN
    ASM_SIMP_TAC[MOI_S86_SC_FACTS] THEN ANTS_TAC THENL
     [MATCH_MP_TAC MOI_S86_SC_NEST THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                    `L:(real^(2,2)finite_sum->bool)->real^1->real^2`;
                    `a:real^(2,2)finite_sum->bool`; `a:real^(2,2)finite_sum->bool`;
                    `p + &1`; `p + k`] MOI_S86_CTX_DISJ) THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s86_sc q Kb UNION inside(moi_s86_sc q Kb) SUBSET
                inside(moi_s86_sc (p + &1) Ka)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s86_sc q Kb`; `moi_s86_sc (p + &1) Ka`] MOI_S5C_NESTED_INSIDE) THEN
    ASM_SIMP_TAC[MOI_S86_SC_FACTS] THEN
    UNDISCH_TAC `moi_s86_sc q Kb SUBSET inside(moi_s86_sc (p + &1) Ka)` THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^2` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC) THEN
  SUBGOAL_THEN `(w:real^2) IN inside(moi_s86_sc (p + k) Ka)` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(w:real^2) IN moi_s86_sc q Kb UNION inside(moi_s86_sc q Kb)`;
      `moi_s86_sc q Kb UNION inside(moi_s86_sc q Kb) SUBSET inside(moi_s86_sc (p + &1) Ka)`;
      `inside(moi_s86_sc (p + &1) Ka) SUBSET inside(moi_s86_sc (p + k) Ka)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `p + k = k + p`] THEN
  REWRITE_TAC[GSYM MOI_S86_SC_ADD; MOI_S86_SC_INSIDE; MOI_S86_SC_IN]);;

let MOI_S86_REGION_INJ = prove
 (`!gg D E L a b p q.
     moi_s86_ctx gg D E L /\ a IN gg /\ b IN gg /\ ~(a = b) /\ integer p /\ integer q /\
     moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
     inside(moi_s86_sc q (path_image (moi_s86_e o L b))) /\
     (!i n. i IN gg /\ integer n
            ==> ~(moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
                  inside(moi_s86_sc n (path_image (moi_s86_e o L i))) /\
                  moi_s86_sc n (path_image (moi_s86_e o L i)) SUBSET
                  inside(moi_s86_sc q (path_image (moi_s86_e o L b)))))
     ==> !z z'. z IN (moi_s86_sc q (path_image (moi_s86_e o L b)) UNION
                      inside(moi_s86_sc q (path_image (moi_s86_e o L b)))) DIFF
                     inside(moi_s86_sc p (path_image (moi_s86_e o L a))) /\
                z' IN (moi_s86_sc q (path_image (moi_s86_e o L b)) UNION
                       inside(moi_s86_sc q (path_image (moi_s86_e o L b)))) DIFF
                      inside(moi_s86_sc p (path_image (moi_s86_e o L a))) /\
                moi_s86_desc (moi_s86_cov D E) z = moi_s86_desc (moi_s86_cov D E) z'
                ==> z = z'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`;
                `b:real^(2,2)finite_sum->bool`; `p:real`; `q:real`] MOI_S86_REGION_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_FACTS) THEN
  ABBREV_TAC `P = (moi_s86_sc q (path_image (moi_s86_e o
                     (L:(real^(2,2)finite_sum->bool)->real^1->real^2) b)) UNION
                   inside(moi_s86_sc q (path_image (moi_s86_e o L b)))) DIFF
                  inside(moi_s86_sc p (path_image (moi_s86_e o L a)))` THEN
  SUBGOAL_THEN `!k (w:real^2). integer k /\ &1 <= k /\ w IN P
                ==> ~(inv(&2 rpow k) % w IN (P:real^2->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((vec 0:real^2) IN (P:real^2->bool))` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[IN_DIFF] THEN
    MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                  `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`]
      MOI_S86_CTX_JORDAN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:real`; `path_image (moi_s86_e o
                    (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a)`] MOI_S86_SC_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`z:real^2`; `z':real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(z:real^2 = vec 0) /\ ~(z':real^2 = vec 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y:real^2` o MATCH_MP MOI_S86_E_ONTO o
    check (fun th -> concl th = `~(z:real^2 = vec 0)`)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y':real^2` o MATCH_MP MOI_S86_E_ONTO o
    check (fun th -> concl th = `~(z':real^2 = vec 0)`)) THEN
  UNDISCH_TAC `moi_s86_desc (moi_s86_cov D E) z = moi_s86_desc (moi_s86_cov D E) z'` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `moi_s86_e y' = z'`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `moi_s86_e y = z`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `k = (y:real^2)$2 - (y':real^2)$2` THEN
  SUBGOAL_THEN `moi_s86_e y = (&2 rpow k) % moi_s86_e y'` SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[GSYM MOI_S86_E_SCALE_INT] THEN REWRITE_TAC[MOI_S86_E_EQ] THEN
    ASM_SIMP_TAC[MOI_S86_E_LIFT_SHIFT] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^2)$2 - (y':real^2)$2 = k` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `k:real` MOI_S86_RPOW2_POS) THEN DISCH_TAC THEN
  SUBGOAL_THEN `k = &0 \/ &1 <= k \/ &1 <= --k` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `k = &0` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `k:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[RPOW_0; VECTOR_MUL_LID];
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:real`; `(&2 rpow k) % moi_s86_e y'`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `inv:real->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&2 rpow k) % (&2 rpow k) % moi_s86_e y' = moi_s86_e y'` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPECL [`--k:real`; `moi_s86_e y'`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `inv:real->real`)) (concl th))) THEN
    REWRITE_TAC[RPOW_NEG; REAL_INV_INV] THEN ASM_REWRITE_TAC[INTEGER_NEG]]);;

(* ------------------------------------------------------------------------- *)
(* The image of the open region is the complementary component, and        *)
(* the image of the closed region is its closure.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S86_BETWEEN = prove
 (`!gg D E L a b p q c n.
     moi_s86_ctx gg D E L /\ a IN gg /\ b IN gg /\ ~(a = b) /\ integer p /\ integer q /\
     moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
     inside(moi_s86_sc q (path_image (moi_s86_e o L b))) /\
     (!i n. i IN gg /\ integer n
            ==> ~(moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
                  inside(moi_s86_sc n (path_image (moi_s86_e o L i))) /\
                  moi_s86_sc n (path_image (moi_s86_e o L i)) SUBSET
                  inside(moi_s86_sc q (path_image (moi_s86_e o L b))))) /\
     c IN gg /\ integer n
     ==> DISJOINT (moi_s86_sc n (path_image (moi_s86_e o L c)))
                  (inside(moi_s86_sc q (path_image (moi_s86_e o L b))) INTER
                   outside(moi_s86_sc p (path_image (moi_s86_e o L a))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t ->
    MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                  `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; t] MOI_S86_CTX_JORDAN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [`a:real^(2,2)finite_sum->bool`; `b:real^(2,2)finite_sum->bool`;
    `c:real^(2,2)finite_sum->bool`] THEN
  MP_TAC(SPECL [`p:real`; `path_image (moi_s86_e o
                  (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a)`] MOI_S86_SC_FACTS) THEN
  MP_TAC(SPECL [`q:real`; `path_image (moi_s86_e o
                  (L:(real^(2,2)finite_sum->bool)->real^1->real^2) b)`] MOI_S86_SC_FACTS) THEN
  MP_TAC(SPECL [`n:real`; `path_image (moi_s86_e o
                  (L:(real^(2,2)finite_sum->bool)->real^1->real^2) c)`] MOI_S86_SC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Ka = moi_s86_sc p (path_image (moi_s86_e o
                     (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a))` THEN
  ABBREV_TAC `Kb = moi_s86_sc q (path_image (moi_s86_e o
                     (L:(real^(2,2)finite_sum->bool)->real^1->real^2) b))` THEN
  ABBREV_TAC `Kc = moi_s86_sc n (path_image (moi_s86_e o
                     (L:(real^(2,2)finite_sum->bool)->real^1->real^2) c))` THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  ASM_CASES_TAC `c:real^(2,2)finite_sum->bool = b /\ n:real = q` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `Kc:real^2->bool = Kb` SUBST_ALL_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Kb"; "Kc"] THEN REFL_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `Kb:real^2->bool` INSIDE_NO_OVERLAP) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `c:real^(2,2)finite_sum->bool = a /\ n:real = p` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `Kc:real^2->bool = Ka` SUBST_ALL_TAC THENL
     [MAP_EVERY EXPAND_TAC ["Ka"; "Kc"] THEN REFL_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `Ka:real^2->bool` OUTSIDE_NO_OVERLAP) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (Kc:real^2->bool) Kb /\ DISJOINT (Ka:real^2->bool) Kc`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Ka"; "Kb"; "Kc"] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_S86_CTX_DISJ THEN
    MAP_EVERY EXISTS_TAC [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Kc:real^2->bool) SUBSET inside Kb` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Kc:real^2->bool`; `Kb:real^2->bool`] MOI_S5C_JORDAN_NEST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `vec 0:real^2` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
    MP_TAC(ISPECL [`Kb:real^2->bool`; `Kc:real^2->bool`] MOI_S5C_NESTED_INSIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `Kb:real^2->bool` INSIDE_INTER_OUTSIDE) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Ka:real^2->bool) SUBSET inside Kc` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Ka:real^2->bool`; `Kc:real^2->bool`] MOI_S5C_JORDAN_NEST) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `vec 0:real^2` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC ASSUME_TAC) THEN
    MP_TAC(ISPEC `Ka:real^2->bool` INSIDE_INTER_OUTSIDE) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^(2,2)finite_sum->bool`; `n:real`] o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> is_const t && fst(dest_const t) = "inside"))
      (concl th))) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S86_REGION_PARTS = prove
 (`!k k':real^2->bool.
     ((k' UNION inside k') DIFF inside k) DIFF (k UNION k') = inside k' INTER outside k /\
     (k SUBSET inside k' /\ k' INTER inside k = {}
      ==> (k' UNION inside k') DIFF inside k =
          (inside k' INTER outside k) UNION k UNION k')`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `k:real^2->bool` INSIDE_UNION_OUTSIDE) THEN
  MP_TAC(ISPEC `k:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
  MP_TAC(ISPEC `k':real^2->bool` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `k:real^2->bool` OUTSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `k:real^2->bool` INSIDE_NO_OVERLAP) THEN
  SET_TAC[]);;

let MOI_S86_COV_E_SCALE = prove
 (`!gg D E L y y':real^2.
     moi_s86_ctx gg D E L /\ moi_s86_cov D E y = moi_s86_cov D E y'
     ==> integer(y$2 - y'$2) /\ moi_s86_e y = (&2 rpow (y$2 - y'$2)) % moi_s86_e y'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_FACTS) THEN
  UNDISCH_TAC `moi_s86_cov D E y = moi_s86_cov D E y'` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[GSYM MOI_S86_E_SCALE_INT] THEN REWRITE_TAC[MOI_S86_E_EQ] THEN
  ASM_SIMP_TAC[MOI_S86_E_LIFT_SHIFT] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_S86_CTX_DESC = prove
 (`!gg D E L.
     moi_s86_ctx gg D E L
     ==> pl_map_on ((:real^2) DELETE vec 0) (moi_s86_desc (moi_s86_cov D E)) /\
         moi_s86_desc (moi_s86_cov D E) continuous_on ((:real^2) DELETE vec 0) /\
         (!z. ~(z = vec 0) ==> moi_s86_desc (moi_s86_cov D E) z IN pl_torus_model)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_BASIS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_FACTS) THEN
  MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_COV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_map_on ((:real^2) DELETE vec 0) (moi_s86_desc (moi_s86_cov D E))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S86_DESC_PL THEN ASM_REWRITE_TAC[MOI_S86_COV_PL]; ALL_TAC] THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  X_GEN_TAC `z:real^2` THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^2` (SUBST1_TAC o SYM) o MATCH_MP MOI_S86_E_ONTO) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) o check (fun th ->
    is_eq(concl th) && rand(concl th) = `pl_torus_model`)) THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]);;

let MOI_S86_DESC_OPEN = prove
 (`!gg D E L w.
     moi_s86_ctx gg D E L /\ open w /\ w SUBSET (:real^2) DELETE vec 0
     ==> open_in (subtopology euclidean pl_torus_model)
                 (IMAGE (moi_s86_desc (moi_s86_cov D E)) w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_BASIS) THEN
  MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_COV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`moi_s86_cov D E`; `w:real^2->bool`] MOI_S86_DESC_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`moi_s86_e`; `(:real^2)`; `w:real^2->bool`] CONTINUOUS_OPEN_PREIMAGE) THEN
  ASM_REWRITE_TAC[MOI_S86_E_CONTINUOUS; OPEN_UNIV; IN_UNIV]);;

let MOI_S86_CLOPEN_COMPONENT = prove
 (`!(u:real^N->bool) m v k x.
     u SUBSET m /\ open_in (subtopology euclidean m) v /\ compact k /\ v SUBSET u /\
     u INTER k = v /\ connected v /\ x IN v
     ==> connected_component u x = v`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `x:real^N`] CONNECTED_CONNECTED_COMPONENT) THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `connected_component u (x:real^N) INTER v`) THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `x:real^N`] CONNECTED_COMPONENT_SUBSET) THEN DISCH_TAC THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `open_in (subtopology euclidean m) (v:real^N->bool)` THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
      SUBGOAL_THEN `connected_component u (x:real^N) INTER v = connected_component u x INTER w`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `connected_component u (x:real^N) INTER v = connected_component u x INTER k`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `x:real^N`] CONNECTED_COMPONENT_REFL) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_S86_REGION_IMAGE = prove
 (`!gg D E L a b p q.
     moi_s86_ctx gg D E L /\ a IN gg /\ b IN gg /\ ~(a = b) /\ integer p /\ integer q /\
     moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
     inside(moi_s86_sc q (path_image (moi_s86_e o L b))) /\
     (!i n. i IN gg /\ integer n
            ==> ~(moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
                  inside(moi_s86_sc n (path_image (moi_s86_e o L i))) /\
                  moi_s86_sc n (path_image (moi_s86_e o L i)) SUBSET
                  inside(moi_s86_sc q (path_image (moi_s86_e o L b)))))
     ==> IMAGE (moi_s86_desc (moi_s86_cov D E))
               (inside(moi_s86_sc q (path_image (moi_s86_e o L b))) INTER
                outside(moi_s86_sc p (path_image (moi_s86_e o L a))))
         SUBSET pl_torus_model DIFF UNIONS gg`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_DESC) THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`]
    MOI_S86_CTX_JORDAN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:real`; `path_image (moi_s86_e o
                  (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a)`] MOI_S86_SC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_DIFF; IN_UNIONS] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(z:real^2 = vec 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPEC `moi_s86_sc p (path_image (moi_s86_e o
                    (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a))` INSIDE_INTER_OUTSIDE) THEN
    UNDISCH_TAC `(vec 0:real^2) IN outside(moi_s86_sc p (path_image (moi_s86_e o
                    (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a)))` THEN
    UNDISCH_TAC `(vec 0:real^2) IN inside(moi_s86_sc p (path_image (moi_s86_e o
                    (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a)))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^(2,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y:real^2` o MATCH_MP MOI_S86_E_ONTO o
    check (fun th -> concl th = `~(z:real^2 = vec 0)`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `moi_s86_e y = z`)) THEN
  UNDISCH_TAC `moi_s86_desc (moi_s86_cov D E) (moi_s86_e y) IN
               (c:real^(2,2)finite_sum->bool)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real^(2,2)finite_sum->bool` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `vec 1:real^1`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `?t. t IN interval[vec 0,vec 1] /\
                    moi_s86_cov D E y =
                    moi_s86_cov D E ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c t)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s86_cov D E y IN (c:real^(2,2)finite_sum->bool)` THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) o check (fun th ->
      is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "IMAGE")) (lhs(concl th)))) THEN
    REWRITE_TAC[path_image; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S86_COV_E_SCALE (CONJ
    (ASSUME `moi_s86_ctx gg D E (L:(real^(2,2)finite_sum->bool)->real^1->real^2)`)
    (ASSUME `moi_s86_cov D E y =
             moi_s86_cov D E ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c t)`))) THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`;
                `b:real^(2,2)finite_sum->bool`; `p:real`; `q:real`; `c:real^(2,2)finite_sum->bool`;
                `(y:real^2)$2 - ((L:(real^(2,2)finite_sum->bool)->real^1->real^2) c t)$2`]
    MOI_S86_BETWEEN) THEN
  ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `moi_s86_e y`) THEN ASM_REWRITE_TAC[MOI_S86_SC_PATH_IMAGE] THEN
  EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[]);;

let MOI_S86_REGION_COMPONENT = prove
 (`!gg D E L a b p q z0.
     moi_s86_ctx gg D E L /\ a IN gg /\ b IN gg /\ ~(a = b) /\ integer p /\ integer q /\
     moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
     inside(moi_s86_sc q (path_image (moi_s86_e o L b))) /\
     (!i n. i IN gg /\ integer n
            ==> ~(moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
                  inside(moi_s86_sc n (path_image (moi_s86_e o L i))) /\
                  moi_s86_sc n (path_image (moi_s86_e o L i)) SUBSET
                  inside(moi_s86_sc q (path_image (moi_s86_e o L b))))) /\
     z0 IN inside(moi_s86_sc q (path_image (moi_s86_e o L b))) /\
     z0 IN outside(moi_s86_sc p (path_image (moi_s86_e o L a)))
     ==> connected_component (pl_torus_model DIFF UNIONS gg)
                             (moi_s86_desc (moi_s86_cov D E) z0) =
         IMAGE (moi_s86_desc (moi_s86_cov D E))
               (inside(moi_s86_sc q (path_image (moi_s86_e o L b))) INTER
                outside(moi_s86_sc p (path_image (moi_s86_e o L a)))) /\
         closure(connected_component (pl_torus_model DIFF UNIONS gg)
                                     (moi_s86_desc (moi_s86_cov D E) z0)) =
         IMAGE (moi_s86_desc (moi_s86_cov D E))
               ((moi_s86_sc q (path_image (moi_s86_e o L b)) UNION
                 inside(moi_s86_sc q (path_image (moi_s86_e o L b)))) DIFF
                inside(moi_s86_sc p (path_image (moi_s86_e o L a))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`;
                `b:real^(2,2)finite_sum->bool`; `p:real`; `q:real`] MOI_S86_REGION_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_DESC) THEN
  MAP_EVERY (fun (c,n) ->
    MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                  `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; c] MOI_S86_CTX_JORDAN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [n; mk_comb(`path_image:(real^1->real^2)->real^2->bool`,
                   mk_comb(mk_comb(`(o):(real^2->real^2)->(real^1->real^2)->real^1->real^2`,
                                   `moi_s86_e`),
                           mk_comb(`L:(real^(2,2)finite_sum->bool)->real^1->real^2`, c)))]
      MOI_S86_SC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                  `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; c; n] MOI_S86_CTX_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                  `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; c; n] MOI_S86_CTX_CURVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [`a:real^(2,2)finite_sum->bool`,`p:real`; `b:real^(2,2)finite_sum->bool`,`q:real`] THEN
  ABBREV_TAC `Ka = moi_s86_sc p (path_image (moi_s86_e o
                     (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a))` THEN
  ABBREV_TAC `Kb = moi_s86_sc q (path_image (moi_s86_e o
                     (L:(real^(2,2)finite_sum->bool)->real^1->real^2) b))` THEN
  MP_TAC(ISPECL [`Ka:real^2->bool`; `Kb:real^2->bool`] MOI_S5C_NESTED_INSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `P = (Kb UNION inside Kb) DIFF inside (Ka:real^2->bool)` THEN
  ABBREV_TAC `W = inside Kb INTER outside (Ka:real^2->bool)` THEN
  SUBGOAL_THEN `P DIFF (Ka UNION Kb) = W:real^2->bool` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `(Kb UNION inside Kb) DIFF inside Ka = P:real^2->bool`);
                GSYM(ASSUME `inside Kb INTER outside Ka = W:real^2->bool`)] THEN
    REWRITE_TAC[MOI_S86_REGION_PARTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `W UNION Ka UNION Kb = P:real^2->bool` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `(Kb UNION inside Kb) DIFF inside Ka = P:real^2->bool`);
                GSYM(ASSUME `inside Kb INTER outside Ka = W:real^2->bool`)] THEN
    CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`Ka:real^2->bool`; `Kb:real^2->bool`] MOI_S86_REGION_PARTS) THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `Ka:real^2->bool` INSIDE_INTER_OUTSIDE) THEN
    UNDISCH_TAC `(Kb:real^2->bool) SUBSET outside Ka` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Ka:real^2->bool`; `Kb:real^2->bool`] MOI_S5C_ANN2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5C_ANN_PARTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5C_ANN_ENDS_CLOSURE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S5C_ANN_OPEN_INTERIOR) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `P SUBSET (:real^2) DELETE vec 0 /\ W SUBSET (P:real^2->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `(Kb UNION inside Kb) DIFF inside Ka = P:real^2->bool`)] THEN
      UNDISCH_TAC `(vec 0:real^2) IN inside Ka` THEN SET_TAC[];
      UNDISCH_TAC `W UNION Ka UNION Kb = P:real^2->bool` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `W:real^2->bool`]
    MOI_S86_DESC_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `P:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `compact(IMAGE (moi_s86_desc (moi_s86_cov D E)) P)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2) DELETE vec 0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (moi_s86_desc (moi_s86_cov D E)) P =
                IMAGE (moi_s86_desc (moi_s86_cov D E)) W UNION a UNION b` ASSUME_TAC THENL
   [UNDISCH_TAC `W UNION Ka UNION Kb = P:real^2->bool` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMAGE_UNION] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(pl_torus_model DIFF UNIONS gg) INTER
                IMAGE (moi_s86_desc (moi_s86_cov D E)) P =
                IMAGE (moi_s86_desc (moi_s86_cov D E)) W` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (moi_s86_desc (moi_s86_cov D E)) P =
       IMAGE (moi_s86_desc (moi_s86_cov D E)) W UNION a UNION b`;
      `IMAGE (moi_s86_desc (moi_s86_cov D E)) W SUBSET pl_torus_model DIFF UNIONS gg`;
      `(a:real^(2,2)finite_sum->bool) IN gg`; `(b:real^(2,2)finite_sum->bool) IN gg`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(IMAGE (moi_s86_desc (moi_s86_cov D E)) W)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2) DELETE vec 0` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `P:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s86_desc (moi_s86_cov D E) z0 IN
                IMAGE (moi_s86_desc (moi_s86_cov D E)) W` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `z0:real^2` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ASSUME `inside Kb INTER outside Ka = W:real^2->bool`)] THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S86_CLOPEN_COMPONENT THEN
    MAP_EVERY EXISTS_TAC [`pl_torus_model`;
                          `IMAGE (moi_s86_desc (moi_s86_cov D E)) P`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `closure W = P:real^2->bool` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      MP_TAC(ISPEC `W:real^2->bool` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `(Ka:real^2->bool) UNION Kb SUBSET closure W` THEN
      UNDISCH_TAC `W UNION Ka UNION Kb = P:real^2->bool` THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) o check (fun th ->
      concl th = `closure W = P:real^2->bool`)) THEN
    MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2) DELETE vec 0` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The region is a PL annulus with two different members as ends, and       *)
(* the model theorem on the torus surface.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S86_REGION_ANNULUS = prove
 (`!gg D E L a b p q.
     moi_s86_ctx gg D E L /\ a IN gg /\ b IN gg /\ ~(a = b) /\ integer p /\ integer q /\
     moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
     inside(moi_s86_sc q (path_image (moi_s86_e o L b))) /\
     (!i n. i IN gg /\ integer n
            ==> ~(moi_s86_sc p (path_image (moi_s86_e o L a)) SUBSET
                  inside(moi_s86_sc n (path_image (moi_s86_e o L i))) /\
                  moi_s86_sc n (path_image (moi_s86_e o L i)) SUBSET
                  inside(moi_s86_sc q (path_image (moi_s86_e o L b)))))
     ==> pl_annulus_with_ends
           (IMAGE (moi_s86_desc (moi_s86_cov D E))
                  ((moi_s86_sc q (path_image (moi_s86_e o L b)) UNION
                    inside(moi_s86_sc q (path_image (moi_s86_e o L b)))) DIFF
                   inside(moi_s86_sc p (path_image (moi_s86_e o L a)))))
           a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`;
                `b:real^(2,2)finite_sum->bool`; `p:real`; `q:real`] MOI_S86_REGION_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_BASIS) THEN
  MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_COV_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY (fun (c,n) ->
    MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                  `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; c] MOI_S86_CTX_JORDAN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [n; mk_comb(`path_image:(real^1->real^2)->real^2->bool`,
                   mk_comb(mk_comb(`(o):(real^2->real^2)->(real^1->real^2)->real^1->real^2`,
                                   `moi_s86_e`),
                           mk_comb(`L:(real^(2,2)finite_sum->bool)->real^1->real^2`, c)))]
      MOI_S86_SC_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                  `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; c; n] MOI_S86_CTX_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                  `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; c; n] MOI_S86_CTX_CURVE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [`a:real^(2,2)finite_sum->bool`,`p:real`; `b:real^(2,2)finite_sum->bool`,`q:real`] THEN
  ABBREV_TAC `Ka = moi_s86_sc p (path_image (moi_s86_e o
                     (L:(real^(2,2)finite_sum->bool)->real^1->real^2) a))` THEN
  ABBREV_TAC `Kb = moi_s86_sc q (path_image (moi_s86_e o
                     (L:(real^(2,2)finite_sum->bool)->real^1->real^2) b))` THEN
  MP_TAC(ISPECL [`Ka:real^2->bool`; `Kb:real^2->bool`] MOI_S5C_ANN2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_s86_cov D E`; `(Kb UNION inside Kb) DIFF inside (Ka:real^2->bool)`]
    MOI_S86_DESC_PLH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_S86_COV_PL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5C_ANN_POLYHEDRON THEN
      MAP_EVERY EXISTS_TAC [`Ka:real^2->bool`; `Kb:real^2->bool`] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(vec 0:real^2) IN inside Ka` THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `g:real^(2,2)finite_sum->real^2`)] THEN
  MP_TAC(ISPECL [`(Kb UNION inside Kb) DIFF inside (Ka:real^2->bool)`; `Ka:real^2->bool`;
                 `Kb:real^2->bool`;
                 `IMAGE (moi_s86_desc (moi_s86_cov D E))
                        ((Kb UNION inside Kb) DIFF inside (Ka:real^2->bool))`;
                 `moi_s86_desc (moi_s86_cov D E)`; `g:real^(2,2)finite_sum->real^2`]
    MOI_S5C_ANN_TRANSFER) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S86_MODEL = prove
 (`!gg:(real^(2,2)finite_sum->bool)->bool.
     FINITE gg /\ 2 <= CARD gg /\ pairwise DISJOINT gg /\
     (!c. c IN gg
          ==> c SUBSET pl_torus_model /\ pl_sphere 1 c /\
              (?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET c /\
                   ~homotopic_loops pl_torus_model k (linepath(pathstart k,pathstart k))))
     ==> !x. x IN pl_torus_model DIFF UNIONS gg
             ==> ?j0 j1. j0 IN gg /\ j1 IN gg /\ ~(j0 = j1) /\
                         pl_annulus_with_ends
                           (closure(connected_component (pl_torus_model DIFF UNIONS gg) x))
                           j0 j1`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^(2,2)finite_sum` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(gg:(real^(2,2)finite_sum->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `2 <= CARD({}:(real^(2,2)finite_sum->bool)->bool)` THEN
    REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `gg:(real^(2,2)finite_sum->bool)->bool` MOI_S86_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^2` (X_CHOOSE_THEN `E:real^2`
    (X_CHOOSE_THEN `L:(real^(2,2)finite_sum->bool)->real^1->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `moi_s86_ctx gg D E (L:(real^(2,2)finite_sum->bool)->real^1->real^2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s86_ctx] THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S86_CTX_FACTS) THEN
  MP_TAC(SPECL [`D:real^2`; `E:real^2`] MOI_S86_COV_FACTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; STRIP_TAC] THEN
  SUBGOAL_THEN `?y0:real^2. moi_s86_cov D E y0 = x` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^(2,2)finite_sum) IN pl_torus_model DIFF UNIONS gg` THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [GSYM th]) o
      check (fun th -> is_eq(concl th) && rand(concl th) = `pl_torus_model`)) THEN
    REWRITE_TAC[IN_DIFF; IN_IMAGE; IN_UNIV] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gg:(real^(2,2)finite_sum->bool)->bool`;
                 `\c:real^(2,2)finite_sum->bool. path_image (moi_s86_e o
                    (L:(real^(2,2)finite_sum->bool)->real^1->real^2) c)`;
                 `moi_s86_e y0`] MOI_S86_CONSEC) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_S86_E_NONZERO] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:real^(2,2)finite_sum->bool` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                    `L:(real^(2,2)finite_sum->bool)->real^1->real^2`;
                    `i:real^(2,2)finite_sum->bool`] MOI_S86_CTX_JORDAN) THEN
      ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S86_CTX_DISJ THEN
      MAP_EVERY EXISTS_TAC [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`i:real^(2,2)finite_sum->bool`; `n:real`] THEN STRIP_TAC THEN
      DISCH_TAC THEN
      MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                    `L:(real^(2,2)finite_sum->bool)->real^1->real^2`;
                    `i:real^(2,2)finite_sum->bool`; `n:real`] MOI_S86_CTX_CURVE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^(2,2)finite_sum) IN i` MP_TAC THENL
       [FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) o check (fun th ->
          is_eq(concl th) && rand(concl th) = `i:real^(2,2)finite_sum->bool`)) THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `moi_s86_e y0` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(x:real^(2,2)finite_sum) IN pl_torus_model DIFF UNIONS gg` THEN
      UNDISCH_TAC `(i:real^(2,2)finite_sum->bool) IN gg` THEN SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^(2,2)finite_sum->bool` (X_CHOOSE_THEN
    `b:real^(2,2)finite_sum->bool` (X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real`
    STRIP_ASSUME_TAC)))) THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`;
                `b:real^(2,2)finite_sum->bool`; `p:real`; `q:real`; `moi_s86_e y0`]
    MOI_S86_REGION_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MAP_EVERY EXISTS_TAC [`a:real^(2,2)finite_sum->bool`; `b:real^(2,2)finite_sum->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`gg:(real^(2,2)finite_sum->bool)->bool`; `D:real^2`; `E:real^2`;
                `L:(real^(2,2)finite_sum->bool)->real^1->real^2`; `a:real^(2,2)finite_sum->bool`;
                `b:real^(2,2)finite_sum->bool`; `p:real`; `q:real`] MOI_S86_REGION_ANNULUS) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Transfer from the torus model to the frontier of the solid torus:        *)
(* Moise Thm 28.6.                                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S86_HOMEO_CLOSURE = prove
 (`!(f:real^M->real^N) g s t c.
     homeomorphism (s,t) (f,g) /\ compact s /\ c SUBSET s
     ==> IMAGE f (closure c) = closure (IMAGE f c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `closure c SUBSET (s:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) continuous_on closure c` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET];
    MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[COMPACT_CLOSURE] THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]]]);;

let MOI_S86_MEMBER_TRANSFER = prove
 (`!(s:real^3->bool) (ph:real^(2,2)finite_sum->real^3) ps j.
     pl_homeomorphism (pl_torus_model,frontier s) (ph,ps) /\
     pl_sphere 1 j /\ j SUBSET frontier s /\
     (!d. d SUBSET frontier s ==> ~pl_cell_with_boundary 2 d j)
     ==> IMAGE ps j SUBSET pl_torus_model /\ pl_sphere 1 (IMAGE ps j) /\
         (?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET IMAGE ps j /\
              ~homotopic_loops pl_torus_model k (linepath(pathstart k,pathstart k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `pl_homeomorphism (pl_torus_model,frontier s)
                   (ph:real^(2,2)finite_sum->real^3,ps)`) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (ps:real^3->real^(2,2)finite_sum) j SUBSET pl_torus_model`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `pl_torus_model`)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (j:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `1` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (j,IMAGE ps j) (ps:real^3->real^(2,2)finite_sum,ph)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`frontier s:real^3->bool`; `pl_torus_model`] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (IMAGE (ps:real^3->real^(2,2)finite_sum) j)` ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:3`,`:M`] MOI_FM3_PL_SPHERE_TRANSFER) THEN
    MAP_EVERY EXISTS_TAC [`j:real^3->bool`; `ps:real^3->real^(2,2)finite_sum`;
                          `ph:real^(2,2)finite_sum->real^3`] THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S86_ESSENTIAL_MODEL THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^(2,2)finite_sum->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (ph:real^(2,2)finite_sum->real^3) d` o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "pl_cell_with_boundary")) (concl th))) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `frontier s:real^3->bool`)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `j = IMAGE (ph:real^(2,2)finite_sum->real^3) (IMAGE ps j)` SUBST1_TAC THENL
   [UNDISCH_TAC `(j:real^3->bool) SUBSET frontier s` THEN
    UNDISCH_TAC `!y. y IN frontier s ==> (ph:real^(2,2)finite_sum->real^3) (ps y) = y` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5C_CELL_PLH THEN
  MAP_EVERY EXISTS_TAC [`d:real^(2,2)finite_sum->bool`; `ps:real^3->real^(2,2)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`pl_torus_model`; `frontier s:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
    MAP_EVERY EXISTS_TAC [`2`; `IMAGE (ps:real^3->real^(2,2)finite_sum) j`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `pl_sphere 1 (j:real^3->bool)` THEN REWRITE_TAC[pl_sphere] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MESON_TAC[]]);;

let MOISE_286 = prove
 (`MOISE_286_STATEMENT`,
  REWRITE_TAC[MOISE_286_STATEMENT] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MP_TAC(SPEC `s:real^3->bool` (CONJUNCT2 PL_SOLID_TORUS_BASIC)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ph:real^(2,2)finite_sum->real^3`
    (X_CHOOSE_THEN `ps:real^3->real^(2,2)finite_sum` ASSUME_TAC)) THEN
  MP_TAC(ASSUME `pl_homeomorphism (pl_torus_model,frontier s)
                   (ph:real^(2,2)finite_sum->real^3,ps)`) THEN
  REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `!j. j IN gg ==> IMAGE (ph:real^(2,2)finite_sum->real^3) (IMAGE ps j) = j`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(j:real^3->bool) SUBSET frontier s` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!y. y IN frontier s ==> (ph:real^(2,2)finite_sum->real^3) (ps y) = y` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `hh = IMAGE (IMAGE (ps:real^3->real^(2,2)finite_sum)) gg` THEN
  MP_TAC(ISPEC `hh:(real^(2,2)finite_sum->bool)->bool` MOI_S86_MODEL) THEN ANTS_TAC THENL
   [EXPAND_TAC "hh" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`IMAGE (ps:real^3->real^(2,2)finite_sum)`; `gg:(real^3->bool)->bool`]
        CARD_IMAGE_INJ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `j:real^3->bool` THEN DISCH_TAC THEN
      X_GEN_TAC `j':real^3->bool` THEN DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `DISJOINT (j:real^3->bool) j' /\ j SUBSET frontier s /\ j' SUBSET frontier s`
      MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `pairwise DISJOINT (gg:(real^3->bool)->bool)` THEN
          REWRITE_TAC[pairwise] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `~(IMAGE (ps:real^3->real^(2,2)finite_sum) j' = IMAGE ps j')` THEN
          REWRITE_TAC[];
          ASM_MESON_TAC[];
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `!y. y IN frontier s ==> (ph:real^(2,2)finite_sum->real^3) (ps y) = y` THEN
      SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `j:real^3->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_S86_MEMBER_TRANSFER THEN
      MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `ph:real^(2,2)finite_sum->real^3`] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j y. j IN gg /\ (y:real^3) IN j ==> y IN frontier s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(j:real^3->bool) SUBSET frontier s` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN j` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN frontier s DIFF UNIONS gg
                ==> (ps:real^3->real^(2,2)finite_sum) z IN pl_torus_model DIFF UNIONS hh`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN EXPAND_TAC "hh" THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE; IN_IMAGE] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (ps:real^3->real^(2,2)finite_sum) (frontier s) = pl_torus_model` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC))) THEN
      SUBGOAL_THEN `(y:real^3) IN frontier s` ASSUME_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 2 &&
          can (find_term ((=) `frontier s:real^3->bool`)) (concl th))) THEN
        EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `z:real^3 = y` SUBST_ALL_TAC THENL
       [MP_TAC(SPEC `z:real^3` (ASSUME
          `!y. y IN frontier s ==> (ph:real^(2,2)finite_sum->real^3) (ps y) = y`)) THEN
        MP_TAC(SPEC `y:real^3` (ASSUME
          `!y. y IN frontier s ==> (ph:real^(2,2)finite_sum->real^3) (ps y) = y`)) THEN
        REWRITE_TAC[ASSUME `(y:real^3) IN frontier s`; ASSUME `(z:real^3) IN frontier s`;
                    ASSUME `(ps:real^3->real^(2,2)finite_sum) z = ps y`] THEN
        MESON_TAC[];
        UNDISCH_TAC `~(?t. t IN gg /\ (y:real^3) IN t)` THEN REWRITE_TAC[] THEN
        EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN pl_torus_model DIFF UNIONS hh
                ==> (ph:real^(2,2)finite_sum->real^3) w IN frontier s DIFF UNIONS gg`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^(2,2)finite_sum` THEN EXPAND_TAC "hh" THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; EXISTS_IN_IMAGE; IN_IMAGE] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (ph:real^(2,2)finite_sum->real^3) pl_torus_model = frontier s` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(?x. x IN gg /\ (?y. w = (ps:real^3->real^(2,2)finite_sum) y /\ y IN x))` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `(ph:real^(2,2)finite_sum->real^3) w` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(ps:real^3->real^(2,2)finite_sum) x`) THEN
  ANTS_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real^(2,2)finite_sum->bool` (X_CHOOSE_THEN
    `c1:real^(2,2)finite_sum->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?j0 j1. j0 IN gg /\ j1 IN gg /\
                        c0 = IMAGE (ps:real^3->real^(2,2)finite_sum) j0 /\ c1 = IMAGE ps j1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(c0:real^(2,2)finite_sum->bool) IN hh` THEN
    UNDISCH_TAC `(c1:real^(2,2)finite_sum->bool) IN hh` THEN
    EXPAND_TAC "hh" THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`j0:real^3->bool`; `j1:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(c0:real^(2,2)finite_sum->bool = c1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the component of x is the image of the component of ps x *)
  SUBGOAL_THEN `IMAGE (ph:real^(2,2)finite_sum->real^3) (pl_torus_model DIFF UNIONS hh) =
                frontier s DIFF UNIONS gg` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      EXISTS_TAC `(ps:real^3->real^(2,2)finite_sum) z` THEN ASM_SIMP_TAC[] THEN
      CONV_TAC SYM_CONV THEN FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `ph:real^(2,2)finite_sum->real^3`)) (concl th) &&
        can (find_term ((=) `frontier s:real^3->bool`)) (lhand(snd(strip_forall(concl th)))))) THEN
      UNDISCH_TAC `(z:real^3) IN frontier s DIFF UNIONS gg` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component (frontier s DIFF UNIONS gg) x =
    IMAGE (ph:real^(2,2)finite_sum->real^3)
          (connected_component (pl_torus_model DIFF UNIONS hh) (ps x))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`ph:real^(2,2)finite_sum->real^3`;
                   `subtopology euclidean (pl_torus_model DIFF UNIONS hh)`;
                   `subtopology euclidean (frontier s DIFF UNIONS gg:real^3->bool)`;
                   `(ps:real^3->real^(2,2)finite_sum) x`]
      HOMEOMORPHIC_MAP_CONNECTED_COMPONENT_OF) THEN
    REWRITE_TAC[CONNECTED_COMPONENT_OF_EUCLIDEAN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(ph:real^(2,2)finite_sum->real^3) (ps x) = x` SUBST1_TAC THENL
     [MP_TAC(SPEC `x:real^3` (ASSUME
        `!y. y IN frontier s ==> (ph:real^(2,2)finite_sum->real^3) (ps y) = y`)) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^3) IN frontier s DIFF UNIONS gg` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
      EXISTS_TAC `ps:real^3->real^(2,2)finite_sum` THEN
      REWRITE_TAC[HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY] THEN
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`pl_torus_model`; `frontier s:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `C0 = connected_component (pl_torus_model DIFF UNIONS hh)
                     ((ps:real^3->real^(2,2)finite_sum) x)` THEN
  SUBGOAL_THEN `C0 SUBSET pl_torus_model` ASSUME_TAC THENL
   [EXPAND_TAC "C0" THEN
    MP_TAC(ISPECL [`pl_torus_model DIFF UNIONS hh`; `(ps:real^3->real^(2,2)finite_sum) x`]
      CONNECTED_COMPONENT_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ph:real^(2,2)finite_sum->real^3`; `ps:real^3->real^(2,2)finite_sum`;
                 `pl_torus_model`; `frontier s:real^3->bool`; `C0:real^(2,2)finite_sum->bool`]
    MOI_S86_HOMEO_CLOSURE) THEN
  ASM_REWRITE_TAC[CONJUNCT2 MOI_FEU_EULER_TORUS_MODEL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `closure C0 SUBSET pl_torus_model` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CONJUNCT2 MOI_FEU_EULER_TORUS_MODEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `j0 = IMAGE (ph:real^(2,2)finite_sum->real^3) c0 /\ j1 = IMAGE ph c1`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_S5C_ANN_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`closure C0:real^(2,2)finite_sum->bool`;
                        `ps:real^3->real^(2,2)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`pl_torus_model`; `frontier s:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
  MATCH_MP_TAC MOI_S5C_ANN_POLYHEDRON THEN
  MAP_EVERY EXISTS_TAC [`c0:real^(2,2)finite_sum->bool`; `c1:real^(2,2)finite_sum->bool`] THEN
  ASM_REWRITE_TAC[]);;

