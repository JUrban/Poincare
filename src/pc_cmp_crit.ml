(* ========================================================================= *)
(* Unit pc_cmp_crit (comparison-geometry layer CMP): CMP_R2_CRITICAL,        *)
(* Gromov's critical point lemma (Petersen Lemma 12.4.2): on a complete      *)
(* connected manifold with sec >= 0 the critical points of d_p lie in a      *)
(* bounded set.  Proof: critical points x_k with d(p,x_(k+1)) > 2 d(p,x_k)   *)
(* would have two members x_i, x_j (i < j) whose directions at p make a      *)
(* small angle (compactness of the unit sphere); the hinge comparison        *)
(* (CMPA_HINGE) at p and at the critical point x_i, where some minimizing    *)
(* direction to p makes a non-obtuse angle with the direction to x_j, gives  *)
(* d(p,x_j) < 2 d(p,x_i).                                                    *)
(* ========================================================================= *)

needs "src/pc_cmp_topo.ml";;
needs "src/pc_cmp_pdefs.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Small facts and the key step.  CMPCR_KEY: if x1, x2 are reached from p by *)
(* minimizing w1, w2 with 0 < a = d(p,x1), 2a <= b = d(p,x2) and a b < 2     *)
(* <w1,w2>_g (angle < 60 degrees), then x1 is regular: the minimizing        *)
(* direction from x1 to x2 is the regular direction.                         *)
(* ========================================================================= *)

let CMPCR_FRAME_DOT = prove
 (`!(g:A->real^N^N) x E a b.
        mfd_orthonormal_frame g x E ==> (E ** a) dot (g x ** (E ** b)) = a dot b`,
  REWRITE_TAC[mfd_orthonormal_frame] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM CMPP_DOT_TRANSP] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC; GSYM MATRIX_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LID]);;

let CMPCR_UNIT = prove
 (`!top atlas (g:A->real^N^N) (x:A) w L.
        smooth_manifold_atlas top atlas /\ riemannian_metric atlas g /\
        x IN topspace top /\ mfd_tnorm g x w = L /\ &0 < L
        ==> mfd_tnorm g x (inv L % w) = &1 /\ L % (inv L % w) = w`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x:A`] GEOD_TNORM_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`; REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let CMPCR_KEY = prove
 (`!top atlas (g:A->real^N^N) (p:A) x1 x2 w1 w2.
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!y a c. y IN topspace top /\ ~collinear {vec 0,a,c}
                 ==> &0 <= mfd_sectional atlas g y a c) /\
        p IN topspace top /\ x1 IN topspace top /\ x2 IN topspace top /\
        mfd_exp (top,atlas) g p w1 = x1 /\ mfd_tnorm g p w1 = mfd_dist (top,atlas) g p x1 /\
        mfd_exp (top,atlas) g p w2 = x2 /\ mfd_tnorm g p w2 = mfd_dist (top,atlas) g p x2 /\
        &0 < mfd_dist (top,atlas) g p x1 /\
        &2 * mfd_dist (top,atlas) g p x1 <= mfd_dist (top,atlas) g p x2 /\
        mfd_dist (top,atlas) g p x1 * mfd_dist (top,atlas) g p x2 <
        &2 * (w1 dot (g p ** w2))
        ==> ?v. !w. w IN mfd_exp_dom (top,atlas) g x1 /\
                    mfd_exp (top,atlas) g x1 w = p /\
                    mfd_tnorm g x1 w = mfd_dist (top,atlas) g x1 p
                    ==> v dot (g x1 ** w) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = mfd_dist (top,atlas) (g:A->real^N^N) p x1` THEN
  ABBREV_TAC `b = mfd_dist (top,atlas) (g:A->real^N^N) p x2` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_joinable (top,atlas:((A->bool)#(A->real^N))->bool) x1 x2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x1:A`; `x2:A`] MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^N` THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `c = mfd_dist (top,atlas) (g:A->real^N^N) x1 x2` THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x1 p = a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mfd_dist (top,atlas) (g:A->real^N^N) x2 p = b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN MATCH_MP_TAC MFD_DIST_SYM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < x`) THEN CONJ_TAC THENL
     [EXPAND_TAC "c" THEN MATCH_MP_TAC MFD_DIST_POS_LE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x1:A`; `x2:A`] MFD_DIST_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `mfd_dist (top,atlas) (g:A->real^N^N) p x2 = b` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `w1:real^N`; `a:real`] CMPCR_UNIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `w2:real^N`; `b:real`] CMPCR_UNIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x1:A`; `w:real^N`; `a:real`] CMPCR_UNIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `x1:A`; `y:real^N`; `c:real`] CMPCR_UNIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 <= a pow 2 + b pow 2 - &2 * (w1 dot ((g:A->real^N^N) p ** w2))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `inv a % (w1:real^N)`; `inv b % (w2:real^N)`;
                   `a:real`; `b:real`] CMPA_HINGE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> c <= x ==> c <= y`) THEN
    REWRITE_TAC[DOT_LMUL; MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
    SUBGOAL_THEN `~(a = &0) /\ ~(b = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `b pow 2 <= a pow 2 + c pow 2 - &2 * (w dot ((g:A->real^N^N) x1 ** y))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `x1:A`; `inv a % (w:real^N)`; `inv c % (y:real^N)`;
                   `a:real`; `c:real`] CMPA_HINGE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> c <= x ==> c <= y`) THEN
    REWRITE_TAC[DOT_LMUL; MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
    SUBGOAL_THEN `~(a = &0) /\ ~(c = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= w dot ((g:A->real^N^N) x1 ** y)` ASSUME_TAC THENL
   [SUBGOAL_THEN `w dot ((g:A->real^N^N) x1 ** y) = y dot (g x1 ** w)` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                     `g:A->real^N^N`; `x1:A`] GEOG_G_SYM_POS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_ACCEPT_TAC o CONJUNCT1);
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * a * a <= a * b` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&2 * a * a = a * (&2 * a)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Two close unit vectors in any sequence (compactness of the sphere), and   *)
(* the N-general critical point lemma.                                       *)
(* ========================================================================= *)

let CMPCR_CLOSE_PAIR = prove
 (`!e:num->real^N. (!n. norm(e n) = &1) ==> ?i j. i < j /\ norm(e i - e j) < &1 / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `&1`] COMPACT_SPHERE) THEN
  REWRITE_TAC[compact] THEN DISCH_THEN(MP_TAC o SPEC `e:num->real^N`) THEN
  ASM_REWRITE_TAC[IN_SPHERE_0] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`l:real^N`; `r:num->num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 / &4` o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MAP_EVERY EXISTS_TAC [`(r:num->num) N`; `(r:num->num) (SUC N)`] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `N:num` th) THEN MP_TAC(SPEC `SUC N` th)) THEN
  REWRITE_TAC[o_THM; LE_REFL; ARITH_RULE `N <= SUC N`; dist] THEN
  NORM_ARITH_TAC);;

let CMPCR_CRITICAL_GEN = prove
 (`!top atlas (g:A->real^N^N) p.
        hausdorff_space top /\ connected_space top /\ smooth_manifold_atlas top atlas /\
        riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
        (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                 ==> &0 <= mfd_sectional atlas g x u v) /\
        p IN topspace top
        ==> ?D. !x. x IN topspace top /\ D < mfd_dist (top,atlas) g p x
                    ==> ?v. !w. w IN mfd_exp_dom (top,atlas) g x /\
                                mfd_exp (top,atlas) g x w = p /\
                                mfd_tnorm g x w = mfd_dist (top,atlas) g x p
                                ==> v dot (g x ** w) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?f:real->A. !D. f D IN topspace top /\
                    D < mfd_dist (top,atlas) (g:A->real^N^N) p (f D) /\
                    ~(?v. !w. w IN mfd_exp_dom (top,atlas) g (f D) /\
                              mfd_exp (top,atlas) g (f D) w = p /\
                              mfd_tnorm g (f D) w = mfd_dist (top,atlas) g (f D) p
                              ==> v dot (g (f D) ** w) < &0)`
  (X_CHOOSE_THEN `f:real->A` (LABEL_TAC "f")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `D:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `D:real` o ONCE_REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `xs = \n. ITER n (\y:A. f(&2 * mfd_dist (top,atlas) (g:A->real^N^N) p y))
                              (f(&0))` THEN
  SUBGOAL_THEN
   `(xs:num->A) 0 = f(&0) /\
    !n. xs(SUC n) = f(&2 * mfd_dist (top,atlas) (g:A->real^N^N) p (xs n))`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "xs" THEN REWRITE_TAC[ITER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (xs:num->A) n IN topspace top /\
        &0 < mfd_dist (top,atlas) (g:A->real^N^N) p (xs n) /\
        ~(?v. !w. w IN mfd_exp_dom (top,atlas) g (xs n) /\
                  mfd_exp (top,atlas) g (xs n) w = p /\
                  mfd_tnorm g (xs n) w = mfd_dist (top,atlas) g (xs n) p
                  ==> v dot (g (xs n) ** w) < &0)`
  (LABEL_TAC "xs") THENL
   [INDUCT_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "f" (MP_TAC o SPEC `&0`) THEN
      SIMP_TAC[];
      ASM_REWRITE_TAC[] THEN
      USE_THEN "f" (MP_TAC o SPEC
        `&2 * mfd_dist (top,atlas) (g:A->real^N^N) p ((xs:num->A) n)`) THEN
      SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. &2 * mfd_dist (top,atlas) (g:A->real^N^N) p ((xs:num->A) n) <
        mfd_dist (top,atlas) g p (xs(SUC n))`
  (LABEL_TAC "dbl") THENL
   [GEN_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "f" (MP_TAC o SPEC
      `&2 * mfd_dist (top,atlas) (g:A->real^N^N) p ((xs:num->A) n)`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n. m < n ==> &2 * mfd_dist (top,atlas) (g:A->real^N^N) p ((xs:num->A) m) <=
                    mfd_dist (top,atlas) g p (xs n)`
  (LABEL_TAC "grow") THENL
   [MP_TAC(ISPEC `\m n. &2 * mfd_dist (top,atlas) (g:A->real^N^N) p ((xs:num->A) m) <=
                         mfd_dist (top,atlas) g p (xs n)` TRANSITIVE_STEPWISE_LT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `k:num`] THEN STRIP_TAC THEN
      USE_THEN "xs" (MP_TAC o SPEC `j:num`) THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN USE_THEN "dbl" (MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?w. mfd_exp (top,atlas) (g:A->real^N^N) p w = (xs:num->A) n /\
            mfd_tnorm g p w = mfd_dist (top,atlas) g p (xs n)`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                   `g:A->real^N^N`; `p:A`; `(xs:num->A) n`]
      MFD_COMPLETE_MINIMIZING_GEODESIC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MFD_JOINABLE_CONNECTED THEN
      ASM_SIMP_TAC[];
      MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `wv:num->real^N` (LABEL_TAC "wv")) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`] GEOJ_ONB) THEN
  ASM_REWRITE_TAC[GSYM mfd_orthonormal_frame] THEN
  DISCH_THEN(X_CHOOSE_TAC `E:real^N^N`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CMPQ_FRAME_INVERTIBLE) THEN
  SUBGOAL_THEN
   `!n. mfd_tnorm (g:A->real^N^N) p
          (inv(mfd_dist (top,atlas) g p ((xs:num->A) n)) % (wv:num->real^N) n) = &1 /\
        mfd_dist (top,atlas) g p (xs n) %
          (inv(mfd_dist (top,atlas) g p (xs n)) % wv n) = wv n`
  (LABEL_TAC "unit") THENL
   [GEN_TAC THEN MATCH_MP_TAC CMPCR_UNIT THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e = \n. inv(mfd_dist (top,atlas) (g:A->real^N^N) p ((xs:num->A) n)) %
                      (matrix_inv(E:real^N^N) ** (wv:num->real^N) n)` THEN
  SUBGOAL_THEN
   `!n. (E:real^N^N) ** (e:num->real^N) n =
        inv(mfd_dist (top,atlas) (g:A->real^N^N) p ((xs:num->A) n)) % (wv:num->real^N) n`
  (LABEL_TAC "Ee") THENL
   [GEN_TAC THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL; MATRIX_VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[MATRIX_INV; MATRIX_VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. norm((e:num->real^N) n) = &1` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`g:A->real^N^N`; `p:A`; `E:real^N^N`; `(e:num->real^N) n`]
      CMPP_TNORM_FRAME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "Ee" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "unit" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPEC `e:num->real^N` CMPCR_CLOSE_PAIR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `di = mfd_dist (top,atlas) (g:A->real^N^N) p ((xs:num->A) i)` THEN
  ABBREV_TAC `dj = mfd_dist (top,atlas) (g:A->real^N^N) p ((xs:num->A) j)` THEN
  SUBGOAL_THEN `&0 < di /\ &0 < dj` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "di" THEN EXPAND_TAC "dj" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * di <= dj` ASSUME_TAC THENL
   [EXPAND_TAC "di" THEN EXPAND_TAC "dj" THEN USE_THEN "grow" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(wv:num->real^N) i dot ((g:A->real^N^N) p ** wv j) =
    di * dj * ((e:num->real^N) i dot e j)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(wv:num->real^N) i = di % ((E:real^N^N) ** (e:num->real^N) i) /\
                  wv j = dj % (E ** e j)`
    (fun th -> REWRITE_TAC[th]) THENL
     [USE_THEN "Ee" (fun th -> REWRITE_TAC[th]) THEN
      EXPAND_TAC "di" THEN EXPAND_TAC "dj" THEN
      USE_THEN "unit" (fun th -> REWRITE_TAC[th]);
      ALL_TAC] THEN
    REWRITE_TAC[DOT_LMUL; MATRIX_VECTOR_MUL_RMUL; DOT_RMUL] THEN
    MP_TAC(ISPECL [`g:A->real^N^N`; `p:A`; `E:real^N^N`; `(e:num->real^N) i`;
                   `(e:num->real^N) j`] CMPCR_FRAME_DOT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 < (e:num->real^N) i dot e j` ASSUME_TAC THENL
   [SUBGOAL_THEN `norm((e:num->real^N) i - e j) pow 2 < (&1 / &2) pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[NORM_POW_2; DOT_LSUB; DOT_RSUB] THEN
    SUBGOAL_THEN `(e:num->real^N) i dot e i = &1 /\ e j dot e j = &1` MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                 `g:A->real^N^N`; `p:A`; `(xs:num->A) i`; `(xs:num->A) j`;
                 `(wv:num->real^N) i`; `(wv:num->real^N) j`] CMPCR_KEY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < di * dj` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(di * dj) * &1 / &2 < (di * dj) * ((e:num->real^N) i dot e j)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "xs" (MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The statement CMP_R2_CRITICAL_STATEMENT, with the body of                 *)
(* P2B_REQ_CMP_CRITICAL_STATEMENT; p2b_dist_regular is from pc_cmp_pdefs.    *)
(* ========================================================================= *)

let CMP_R2_CRITICAL_STATEMENT = new_definition
 `CMP_R2_CRITICAL_STATEMENT (w:B->bool) <=>
    !top atlas g p.
       hausdorff_space top /\ connected_space top /\
       smooth_manifold_atlas top (atlas:((B->bool)#(B->real^3))->bool) /\
       riemannian_metric atlas g /\ mfd_complete (top,atlas) g /\
       (!x u v. x IN topspace top /\ ~collinear {vec 0,u,v}
                ==> &0 <= mfd_sectional atlas g x u v) /\
       p IN topspace top
       ==> ?D. !x. x IN topspace top /\ D < mfd_dist (top,atlas) g p x
                   ==> p2b_dist_regular (top,atlas) g p x`;;

let CMP_R2_CRITICAL = prove
 (`!w:B->bool. CMP_R2_CRITICAL_STATEMENT w`,
  GEN_TAC THEN REWRITE_TAC[CMP_R2_CRITICAL_STATEMENT; p2b_dist_regular] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CMPCR_CRITICAL_GEN THEN
  ASM_REWRITE_TAC[]);;

