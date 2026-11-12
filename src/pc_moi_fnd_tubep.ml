(* ========================================================================= *)
(* pc_moi_fnd_tubep: foundations of the Moise PL core, the regular           *)
(* neighbourhood of a polygon in real^3 is a PL solid torus with the polygon *)
(* as spine (Moise GTM 47, 24.11, p.179). Main theorem                       *)
(* POLYGON_NBHD_SOLID_TORUS (the statement term                              *)
(* MOI_FND_POLYGON_SOLID_TORUS_3 of pc_moi_fnd_stmt). Route: the necklace of *)
(* the dual cells of the polygon vertices, glued along the splitting disks;  *)
(* the gluing cannot flip because the fins are chosen by determinant signs   *)
(* at the edges and carried through each vertex link along a dual path on    *)
(* which the apex determinant of the crossed edge keeps its sign             *)
(* (MOI_FM3_OPPOSITE_SIDES).                                                 *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_fnd_plst.ml";;
needs "src/pc_moi_cells.ml";;
needs "src/pc_moi_fnd_collar.ml";;
needs "src/pc_moi_s35_cells.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_fnd_rnsc.ml";;
needs "src/pc_moi_pl1m.ml";;
needs "src/pc_moi_fnd_rnb2.ml";;   (* MOI_FRB_CMB2_DCONN *)
needs "src/pc_moi_s28_tria.ml";;   (* MOI_S8TA_SPHERE1_LINE_CHARTS *)
needs "src/pc_moi_fnd_tubecm.ml";;  (* THETA3, cells, PROD_ASSEMBLY *)
needs "src/pc_moi_fnd_tubec.ml";;   (* level picture, generic cells *)

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The orientation core.  For an apex v and points of real^3,               *)
(* D(a,b,c) = det(vector[a - v; b - v; c - v]).  Along a dual path of link  *)
(* triangles the crossed edge f_j = [s_j, r_j] (s_j on the S side), the     *)
(* vertex y_j of the current triangle behind f_j and the vertex z_j of the  *)
(* next triangle beyond f_j satisfy D(s_j,r_j,y_j) D(s_j,r_j,z_j) < 0       *)
(* (adjacent link triangles, MOI_FM3_OPPOSITE_SIDES), and the sign of       *)
(* D(s_j,r_j,y_j) is constant (MOI_FTP_JINV).  The labelling rule at an     *)
(* edge (MOI_FTP_LABEL) and the evaluation at the end kite                   *)
(* (MOI_FTP_KITE_END) then force the S side to end on the S radius          *)
(* (MOI_FTP_S_TO_S).                                                         *)
(* ========================================================================= *)

let MOI_FTP_DET_APEX = prove
 (`!p m a b:real^3.
     det(vector[a - p; b - p; m - p]) = --det(vector[a - m; b - m; p - m])`,
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_RING);;

let MOI_FTP_DET_SWAP12 = prove
 (`!v a b c:real^3.
     det(vector[b - v; a - v; c - v]) = --det(vector[a - v; b - v; c - v])`,
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_RING);;

let MOI_FTP_SIGN_TRANS = prove
 (`!a b c. &0 < a * b /\ &0 < b * c ==> &0 < a * c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_MUL_POS_LT] THEN REAL_ARITH_TAC);;

(* One step of the dual path: the next crossed edge is [s,z] (S vertex kept) *)
(* or [z,r] (F vertex kept); in both cases the sign is kept.                 *)

let MOI_FTP_JSTEP = prove
 (`!v s r y z:real^3.
     det(vector[s - v; r - v; y - v]) * det(vector[s - v; r - v; z - v]) < &0
     ==> &0 < det(vector[s - v; r - v; y - v]) * det(vector[s - v; z - v; r - v]) /\
         &0 < det(vector[s - v; r - v; y - v]) * det(vector[z - v; r - v; s - v])`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `det(vector[s - v; z - v; r - v]) = --det(vector[s - v; r - v; z - v]) /\
    det(vector[z - v; r - v; (s:real^3) - v]) = --det(vector[s - v; r - v; z - v])`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_RING;
    REAL_ARITH_TAC]);;

(* The invariant along a whole dual path of n crossed edges.                 *)

let MOI_FTP_JINV = prove
 (`!v (s:num->real^3) r y z n.
     (!j. j < n ==> det(vector[s j - v; r j - v; y j - v]) *
                    det(vector[s j - v; r j - v; z j - v]) < &0) /\
     (!j. SUC j < n ==> (s(SUC j) = s j /\ r(SUC j) = z j /\ y(SUC j) = r j) \/
                        (s(SUC j) = z j /\ r(SUC j) = r j /\ y(SUC j) = s j))
     ==> !j. j < n ==> &0 < det(vector[s 0 - v; r 0 - v; y 0 - v]) *
                            det(vector[s j - v; r j - v; y j - v])`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "adj") (LABEL_TAC "step")) THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[REAL_LT_SQUARE] THEN
    USE_THEN "adj" (fun th -> MP_TAC(MATCH_MP th (ASSUME `0 < n`))) THEN
    DISCH_TAC THEN DISCH_TAC THEN UNDISCH_TAC
     `det(vector[(s:num->real^3) 0 - v; r 0 - v; y 0 - v]) *
      det(vector[s 0 - v; r 0 - v; z 0 - v]) < &0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `j:num < n` ASSUME_TAC THENL
   [UNDISCH_TAC `SUC j < n` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC MOI_FTP_SIGN_TRANS THEN
  EXISTS_TAC `det(vector[(s:num->real^3) j - v; r j - v; y j - v])` THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "adj" (fun th -> MP_TAC(MATCH_MP th (ASSUME `j:num < n`))) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_JSTEP) THEN
  USE_THEN "step" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC j < n`))) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* At the end of the path the vertex beyond the last crossed edge has the   *)
(* opposite sign.                                                            *)

let MOI_FTP_JEND = prove
 (`!v (s:num->real^3) r y z n.
     (!j. j < SUC n ==> det(vector[s j - v; r j - v; y j - v]) *
                        det(vector[s j - v; r j - v; z j - v]) < &0) /\
     (!j. SUC j < SUC n ==> (s(SUC j) = s j /\ r(SUC j) = z j /\ y(SUC j) = r j) \/
                            (s(SUC j) = z j /\ r(SUC j) = r j /\ y(SUC j) = s j)) /\
     &0 < det(vector[s 0 - v; r 0 - v; y 0 - v])
     ==> det(vector[s n - v; r n - v; z n - v]) < &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "adj") (CONJUNCTS_THEN2 (LABEL_TAC "step")
    ASSUME_TAC)) THEN
  MP_TAC(SPECL [`v:real^3`; `s:num->real^3`; `r:num->real^3`; `y:num->real^3`;
                `z:num->real^3`; `SUC n`] MOI_FTP_JINV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN DISCH_TAC THEN
  USE_THEN "adj" (MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LT] THEN DISCH_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`&0 < det(vector[(s:num->real^3) 0 - v; r 0 - v; y 0 - v])`;
    `&0 < det(vector[(s:num->real^3) 0 - v; r 0 - v; y 0 - v]) *
          det(vector[s n - v; r n - v; y n - v])`;
    `det(vector[(s:num->real^3) n - v; r n - v; y n - v]) *
     det(vector[s n - v; r n - v; z n - v]) < &0`] THEN
  REWRITE_TAC[REAL_MUL_POS_LT; REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
  REAL_ARITH_TAC);;

(* The labelling rule: at an edge one of the two orders of the fin ends     *)
(* gives a positive determinant at a given apex.                             *)

let MOI_FTP_LABEL = prove
 (`!w m p q:real^3.
     aff_dim(convex hull {w,m,p,q}) = &3
     ==> &0 < det(vector[p - w; q - w; m - w]) \/
         &0 < det(vector[q - w; p - w; m - w])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:real^3`; `p:real^3`; `q:real^3`; `m:real^3`] MOI_FM3_DET_NZ) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `{w:real^3,p,q,m} = {w,m,p,q}` SUBST1_TAC THENL
     [SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^3`; `p:real^3`; `q:real^3`; `m:real^3`] MOI_FTP_DET_SWAP12) THEN
  REAL_ARITH_TAC);;

(* The end kite conv{m,cS,cF} seen from the two apexes v and w of the       *)
(* polygon edge: if the labels satisfy the rule at the apex w, then at the  *)
(* apex v the order (cS,cF) is the one with a negative determinant.          *)

let MOI_FTP_KITE_SIGN = prove
 (`!(c:(real^3->bool)->bool) v w m cS cF.
     lf_simplicial_complex c /\ ~(v = w) /\
     convex hull {v,m,cS,cF} IN c /\ aff_dim(convex hull {v,m,cS,cF}) = &3 /\
     convex hull {w,m,cS,cF} IN c /\ aff_dim(convex hull {w,m,cS,cF}) = &3 /\
     &0 < det(vector[cS - w; cF - w; m - w])
     ==> det(vector[cS - v; cF - v; m - v]) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `m:real^3`; `cS:real^3`; `cF:real^3`;
                 `v:real^3`; `w:real^3`] MOI_FM3_OPPOSITE_SIDES) THEN
  SUBGOAL_THEN `{m:real^3,cS,cF,v} = {v,m,cS,cF} /\ {m:real^3,cS,cF,w} = {w,m,cS,cF}`
  (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&0 < det(vector[cS - w; cF - w; m - w:real^3])` THEN
  MP_TAC(ISPECL [`v:real^3`; `m:real^3`; `cS:real^3`; `cF:real^3`] MOI_FTP_DET_APEX) THEN
  MP_TAC(ISPECL [`w:real^3`; `m:real^3`; `cS:real^3`; `cF:real^3`] MOI_FTP_DET_APEX) THEN
  REWRITE_TAC[REAL_MUL_POS_LT; REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
  REAL_ARITH_TAC);;

let MOI_FTP_KITE_END = prove
 (`!(c:(real^3->bool)->bool) v w m cS cF s r.
     lf_simplicial_complex c /\ ~(v = w) /\
     convex hull {v,m,cS,cF} IN c /\ aff_dim(convex hull {v,m,cS,cF}) = &3 /\
     convex hull {w,m,cS,cF} IN c /\ aff_dim(convex hull {w,m,cS,cF}) = &3 /\
     &0 < det(vector[cS - w; cF - w; m - w]) /\
     ((s = cS /\ r = cF) \/ (s = cF /\ r = cS)) /\
     det(vector[s - v; r - v; m - v]) < &0
     ==> s = cS /\ r = cF`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e /\ f /\ g /\ h /\ i ==> j <=>
                    a /\ b /\ c /\ d /\ e /\ f /\ g ==> h ==> i ==> j`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FTP_KITE_SIGN) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`v:real^3`; `cS:real^3`; `cF:real^3`; `m:real^3`] MOI_FTP_DET_SWAP12) THEN
  UNDISCH_TAC `det(vector[cS - v; cF - v; m - v:real^3]) < &0` THEN
  MATCH_MP_TAC(TAUT `(a ==> b ==> c ==> F) ==> a ==> b ==> c ==> d`) THEN REAL_ARITH_TAC);;

(* The S side of the dual path ends on the S radius of the end kite: the    *)
(* path starts with D(s 0,r 0,y 0) > 0 (the rule at the incoming edge,      *)
(* whose end vertex is the apex) and the vertex beyond the last crossed     *)
(* edge is the kite centre m.                                                *)

let MOI_FTP_S_TO_S = prove
 (`!(c:(real^3->bool)->bool) v w m cS cF (s:num->real^3) r y z n.
     lf_simplicial_complex c /\ ~(v = w) /\
     convex hull {v,m,cS,cF} IN c /\ aff_dim(convex hull {v,m,cS,cF}) = &3 /\
     convex hull {w,m,cS,cF} IN c /\ aff_dim(convex hull {w,m,cS,cF}) = &3 /\
     &0 < det(vector[cS - w; cF - w; m - w]) /\
     (!j. j < SUC n ==> det(vector[s j - v; r j - v; y j - v]) *
                        det(vector[s j - v; r j - v; z j - v]) < &0) /\
     (!j. SUC j < SUC n ==> (s(SUC j) = s j /\ r(SUC j) = z j /\ y(SUC j) = r j) \/
                            (s(SUC j) = z j /\ r(SUC j) = r j /\ y(SUC j) = s j)) /\
     &0 < det(vector[s 0 - v; r 0 - v; y 0 - v]) /\ z n = m
     ==> (s n = cS /\ r n = cF) \/ (s n = cF /\ r n = cS)
     ==> s n = cS /\ r n = cF`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `det(vector[(s:num->real^3) n - v; r n - v; m - v]) < &0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `(z:num->real^3) n = m`)) THEN
    MATCH_MP_TAC MOI_FTP_JEND THEN EXISTS_TAC `y:num->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC MOI_FTP_KITE_END THEN
  MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `m:real^3`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The link of a vertex with a 2-sphere link is a finite                    *)
(* combinatorial 2-manifold with connected union (vertex links PL circles,  *)
(* MOI_FTA_S2LINK), so its triangles are dual-connected (MOI_FRB_CMB2_DCONN *)
(* of pc_moi_fnd_rnb2) and each of its edges lies in exactly two triangles   *)
(* (MOI_FCL_EDGE_TRIANGLES).  The link triangles are the faces opposite v   *)
(* of the tetrahedra at v.                                                   *)
(* ========================================================================= *)

(* PL 2-spheres are connected (as MOI_S4VU_SPHERE2_CONNECTED of the Sec 34  *)
(* file pc_moi_s34_op1bu, which this file does not load).                  *)

let MOI_FTP_SPHERE2_CONNECTED = prove
 (`!s:real^N->bool. pl_sphere 2 s ==> connected s`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism; homeomorphism] THEN
  NUM_REDUCE_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    try rand(concl th) = `s:real^N->bool` with Failure _ -> false)) THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                AFF_DIM_SIMPLEX; INT_ARITH `~(&3:int = &1)`]);;

let MOI_FTP_LINK_CM2 = prove
 (`!(c:(real^N->bool)->bool) v.
     lf_simplicial_complex c /\ {v} IN c /\
     pl_sphere 2 (UNIONS (simplicial_link c v))
     ==> FINITE (simplicial_link c v) /\
         combinatorial_manifold 2 (simplicial_link c v) /\
         combinatorial_manifold_with_boundary 2 (simplicial_link c v) /\
         connected (UNIONS (simplicial_link c v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (simplicial_link c (v:real^N))` ASSUME_TAC THENL
   [REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOI_FTA_LINK_LF] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FTA_S2LINK THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{s:real^N->bool | ?r. r IN c /\ v IN r /\ s face_of r}` THEN
    ASM_SIMP_TAC[MOI_FTA_CSTAR_COMPLEX] THEN
    REWRITE_TAC[SUBSET; simplicial_link; IN_ELIM_THM] THEN MESON_TAC[];
    UNDISCH_TAC `combinatorial_manifold 2 (simplicial_link c (v:real^N))` THEN
    REWRITE_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary] THEN
    MESON_TAC[];
    MATCH_MP_TAC MOI_FTP_SPHERE2_CONNECTED THEN ASM_REWRITE_TAC[]]);;

(* The link of a polygon vertex in t' = sd t. *)

let MOI_FTP_POLY_LINK = prove
 (`!(t:(real^N->bool)->bool) l v.
     graph_in_complex t l /\ {v} IN l
     ==> lf_simplicial_complex (barycentric_subdivision t) /\
         {v} IN barycentric_subdivision t /\
         pl_sphere 2 (UNIONS (simplicial_link (barycentric_subdivision t) v)) /\
         FINITE (simplicial_link (barycentric_subdivision t) v) /\
         combinatorial_manifold 2 (simplicial_link (barycentric_subdivision t) v) /\
         combinatorial_manifold_with_boundary 2
           (simplicial_link (barycentric_subdivision t) v) /\
         connected (UNIONS (simplicial_link (barycentric_subdivision t) v))`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_FTA_SETUP) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FTP_LINK_CM2 THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Dual paths of triangles in a finite combinatorial                         *)
(* 2-manifold, their existence (dual connectivity), shortest ones being     *)
(* injective, and the labels (s_j, r_j) of the crossed edges along an       *)
(* injective path: the next crossed edge keeps s_j or keeps r_j, which is   *)
(* the step hypothesis of MOI_FTP_JINV.                                     *)
(* ========================================================================= *)

let moi_ftp_dpath = new_definition
 `moi_ftp_dpath (L:(real^N->bool)->bool) (P:num->real^N->bool) n <=>
    (!j. j <= n ==> P j IN L /\ aff_dim(P j) = &2) /\
    (!j. j < n ==> aff_dim(P j INTER P(SUC j)) = &1)`;;

let moi_ftp_third = new_definition
 `moi_ftp_third (t:real^N->bool) (a:real^N) b =
    @z. z extreme_point_of t /\ ~(z = a) /\ ~(z = b)`;;

let moi_ftp_lab = define
 `(moi_ftp_lab (P:num->real^N->bool) (s0:real^N) (r0:real^N) 0 = (s0,r0)) /\
  (!j. moi_ftp_lab P s0 r0 (SUC j) =
       if P(SUC j) INTER P(SUC(SUC j)) =
          segment[FST(moi_ftp_lab P s0 r0 j),
                  moi_ftp_third (P(SUC j)) (FST(moi_ftp_lab P s0 r0 j))
                                           (SND(moi_ftp_lab P s0 r0 j))]
       then (FST(moi_ftp_lab P s0 r0 j),
             moi_ftp_third (P(SUC j)) (FST(moi_ftp_lab P s0 r0 j))
                                      (SND(moi_ftp_lab P s0 r0 j)))
       else (moi_ftp_third (P(SUC j)) (FST(moi_ftp_lab P s0 r0 j))
                                      (SND(moi_ftp_lab P s0 r0 j)),
             SND(moi_ftp_lab P s0 r0 j)))`;;

(* Existence of a dual path between any two triangles. *)

let MOI_FTP_DPATH_EXISTS = prove
 (`!(L:(real^N->bool)->bool) A B.
     FINITE L /\ combinatorial_manifold_with_boundary 2 L /\ connected (UNIONS L) /\
     A IN L /\ aff_dim A = &2 /\ B IN L /\ aff_dim B = &2
     ==> ?n P. moi_ftp_dpath L P n /\ P 0 = A /\ P n = B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`;
                 `{t:real^N->bool | ?n P. moi_ftp_dpath L P n /\ P 0 = A /\ P n = t}`]
                MOI_FRB_CMB2_DCONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_ftp_dpath] THEN
      MESON_TAC[LE_REFL];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`A:real^N->bool`; `0`; `\j:num. (A:real^N->bool)`] THEN
      ASM_REWRITE_TAC[moi_ftp_dpath; LT] THEN ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `u':real^N->bool`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN
        `P:num->real^N->bool` STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC
       [`SUC n`; `\j:num. if j <= n then (P:num->real^N->bool) j else u'`] THEN
      REWRITE_TAC[LE_0; ARITH_RULE `~(SUC n <= n)`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_ftp_dpath L (P:num->real^N->bool) n` THEN
      REWRITE_TAC[moi_ftp_dpath] THEN STRIP_TAC THEN CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[];
        X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        ASM_CASES_TAC `j:num = n` THENL
         [ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `~(SUC n <= n)`] THEN
          UNDISCH_TAC `(P:num->real^N->bool) n = u` THEN DISCH_THEN SUBST1_TAC THEN
          ASM_REWRITE_TAC[];
          SUBGOAL_THEN `j <= n /\ SUC j <= n /\ j < n` STRIP_ASSUME_TAC THENL
           [UNDISCH_TAC `j < SUC n` THEN UNDISCH_TAC `~(j:num = n)` THEN ARITH_TAC;
            ASM_SIMP_TAC[]]]]];
    DISCH_TAC THEN
    SUBGOAL_THEN `(B:real^N->bool) IN {t | t IN L /\ aff_dim t = &2}` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM]]);;

(* A shortest dual path is injective. *)

let MOI_FTP_DPATH_SIMPLE = prove
 (`!(L:(real^N->bool)->bool) n P.
     moi_ftp_dpath L P n
     ==> ?m Q. moi_ftp_dpath L Q m /\ Q 0 = P 0 /\ Q m = P n /\ m <= n /\
               (!i j. i <= m /\ j <= m /\ Q i = Q j ==> i = j)`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `P:num->real^N->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `!i j. i <= n /\ j <= n /\ (P:num->real^N->bool) i = P j ==> i = j` THENL
   [MAP_EVERY EXISTS_TAC [`n:num`; `P:num->real^N->bool`] THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM] o
    check (fun th -> is_neg(concl th))) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `i0:num` (X_CHOOSE_THEN `j0:num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?i j. i < j /\ j <= n /\ (P:num->real^N->bool) i = P j`
  STRIP_ASSUME_TAC THENL
   [DISJ_CASES_TAC(ARITH_RULE `i0 < j0 \/ j0 < i0 \/ i0:num = j0`) THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM(DISJ_CASES_TAC) THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - (j - i):num`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `i:num < j` THEN UNDISCH_TAC `j:num <= n` THEN ARITH_TAC;
                  ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
    `\k:num. if k <= i then (P:num->real^N->bool) k else P(k + (j - i))`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `moi_ftp_dpath L (P:num->real^N->bool) n` THEN
    REWRITE_TAC[moi_ftp_dpath] THEN STRIP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`k <= n - (j - i:num)`; `i:num < j`; `j:num <= n`] THEN
      ARITH_TAC;
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `k:num < i` THENL
       [SUBGOAL_THEN `k <= i /\ SUC k <= i` (fun th -> REWRITE_TAC[th]) THENL
         [UNDISCH_TAC `k:num < i` THEN ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `&1:int`)) (concl th))) THEN
        MAP_EVERY UNDISCH_TAC [`k:num < i`; `i:num < j`; `j:num <= n`] THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `k:num = i` THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
        REWRITE_TAC[LE_REFL; ARITH_RULE `~(SUC k <= k)`] THEN
        UNDISCH_TAC `(P:num->real^N->bool) k = P j` THEN DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `SUC k + j - k = SUC j` SUBST1_TAC THENL
         [UNDISCH_TAC `k:num < j` THEN ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `&1:int`)) (concl th))) THEN
        MAP_EVERY UNDISCH_TAC [`k < n - (j - k:num)`; `k:num < j`; `j:num <= n`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `~(k <= i) /\ ~(SUC k <= i) /\ SUC k + j - i = SUC(k + j - i)`
      (fun th -> REWRITE_TAC[th]) THENL
       [MAP_EVERY UNDISCH_TAC [`~(k:num < i)`; `~(k:num = i)`; `i:num < j`] THEN ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `&1:int`)) (concl th))) THEN
      MAP_EVERY UNDISCH_TAC [`k < n - (j - i:num)`; `i:num < j`; `j:num <= n`] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `Q:num->real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `Q:num->real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LE_0];
    ASM_CASES_TAC `n - (j - i:num) <= i` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `n - (j - i) = i /\ j:num = n` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`n - (j - i:num) <= i`; `i:num < j`; `j:num <= n`] THEN
        ARITH_TAC;
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(P:num->real^N->bool) i = P j` THEN
        ASM_REWRITE_TAC[]];
      AP_TERM_TAC THEN
      MAP_EVERY UNDISCH_TAC [`i:num < j`; `j:num <= n`] THEN ARITH_TAC];
    MAP_EVERY UNDISCH_TAC [`m <= n - (j - i:num)`; `i:num < j`; `j:num <= n`] THEN
    ARITH_TAC]);;

(* The vertices of the triangles of a complex, the edges of a triangle and *)
(* its third vertex.                                                         *)

let MOI_FTP_TRI_VERTS = prove
 (`!(L:(real^N->bool)->bool) t.
     lf_simplicial_complex L /\ t IN L /\ aff_dim t = &2
     ==> ?a b c. ~affine_dependent {a,b,c} /\ t = convex hull {a,b,c} /\
                 ~(a = b) /\ ~(a = c) /\ ~(b = c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 simplex (t:real^N->bool)` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:int` ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(d:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(d:real^N->bool)):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `e:real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `e:real^N`] THEN
  UNDISCH_TAC `~affine_dependent (d:real^N->bool)` THEN
  UNDISCH_TAC `t = convex hull (d:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

let MOI_FTP_EDGE_OF_TRI = prove
 (`!(a:real^N) b c e.
     ~affine_dependent {a,b,c} /\ e face_of convex hull {a,b,c} /\ aff_dim e = &1
     ==> e = segment[a,b] \/ e = segment[a,c] \/ e = segment[b,c]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `e face_of convex hull {a:real^N,b,c}` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~affine_dependent (d:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `aff_dim (e:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[INT_ARITH `x - &1:int = &1 <=> x = &2`; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(d:real^N->bool) SUBSET {a,b,c}` THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET;
                  IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[SEGMENT_EQ] THEN
  UNDISCH_TAC `~(x:real^N = y)` THEN SET_TAC[]);;

let MOI_FTP_THIRD = prove
 (`!t (a:real^N) b c.
     ~affine_dependent {a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
     t = convex hull {a,b,c}
     ==> moi_ftp_third t a b = c /\ moi_ftp_third t b a = c /\
         moi_ftp_third t a c = b /\ moi_ftp_third t c a = b /\
         moi_ftp_third t b c = a /\ moi_ftp_third t c b = a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[moi_ftp_third; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[]);;

(* The intersection of two triangles of a complex sharing an edge is that   *)
(* edge, and both of its ends are vertices of both triangles.               *)

let MOI_FTP_THIRD_OF_SET = prove
 (`!t (a:real^N) b c s r z.
     ~affine_dependent {a,b,c} /\ t = convex hull {a,b,c} /\
     {s,r,z} = {a,b,c} /\ ~(s = r) /\ ~(s = z) /\ ~(r = z)
     ==> ~affine_dependent {s,r,z} /\ t = convex hull {s,r,z} /\
         moi_ftp_third t s r = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent {s:real^N,r,z} /\ t = convex hull {s,r,z}`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N`; `r:real^N`; `z:real^N`] MOI_FTP_THIRD) THEN
  ASM_SIMP_TAC[]);;

let MOI_FTP_EDGE_VERTS = prove
 (`!(L:(real^N->bool)->bool) t s r.
     lf_simplicial_complex L /\ t IN L /\ aff_dim t = &2 /\
     segment[s,r] face_of t /\ ~(s = r)
     ==> ?z. ~affine_dependent {s,r,z} /\ t = convex hull {s,r,z} /\
             ~(s = z) /\ ~(r = z) /\ moi_ftp_third t s r = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FTP_TRI_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`; `segment[s:real^N,r]`]
                MOI_FTP_EDGE_OF_TRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
    UNDISCH_TAC `segment[s:real^N,r] face_of t` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SEGMENT_EQ] THEN STRIP_TAC THENL
   [EXISTS_TAC `c:real^N` THEN
    SUBGOAL_THEN `{s:real^N,r,c} = {a,b,c} /\ ~(s = c) /\ ~(r = c)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{s:real^N,r} = {a,b}` THEN
      UNDISCH_TAC `~(a:real^N = c)` THEN UNDISCH_TAC `~(b:real^N = c)` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `a:real^N`; `b:real^N`; `c:real^N`;
                   `s:real^N`; `r:real^N`; `c:real^N`] MOI_FTP_THIRD_OF_SET);
    EXISTS_TAC `b:real^N` THEN
    SUBGOAL_THEN `{s:real^N,r,b} = {a,b,c} /\ ~(s = b) /\ ~(r = b)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{s:real^N,r} = {a,c}` THEN
      UNDISCH_TAC `~(a:real^N = b)` THEN UNDISCH_TAC `~(b:real^N = c)` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `a:real^N`; `b:real^N`; `c:real^N`;
                   `s:real^N`; `r:real^N`; `b:real^N`] MOI_FTP_THIRD_OF_SET);
    EXISTS_TAC `a:real^N` THEN
    SUBGOAL_THEN `{s:real^N,r,a} = {a,b,c} /\ ~(s = a) /\ ~(r = a)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{s:real^N,r} = {b,c}` THEN
      UNDISCH_TAC `~(a:real^N = b)` THEN UNDISCH_TAC `~(a:real^N = c)` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `a:real^N`; `b:real^N`; `c:real^N`;
                   `s:real^N`; `r:real^N`; `a:real^N`] MOI_FTP_THIRD_OF_SET)] THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]]));;

(* Consecutive triangles of a dual path are distinct. *)

let MOI_FTP_DPATH_NEQ = prove
 (`!(L:(real^N->bool)->bool) P n j.
     moi_ftp_dpath L P n /\ j < n ==> ~(P j = P(SUC j))`,
  REWRITE_TAC[moi_ftp_dpath] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    can (find_term ((=) `&1:int`)) (concl th))) THEN
  ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC j` o check (fun th ->
    can (find_term ((=) `&2:int`)) (concl th))) THEN
  ANTS_TAC THENL [UNDISCH_TAC `j:num < n` THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[] THEN INT_ARITH_TAC);;

(* One labelling step along an injective dual path in a finite              *)
(* combinatorial 2-manifold: the next crossed edge is [s,z] or [z,r] (z the *)
(* vertex of the next triangle off [s,r]), never [s,r] again.               *)

let MOI_FTP_LAB_STEP0 = prove
 (`!(L:(real^N->bool)->bool) P n j s r.
     FINITE L /\ lf_simplicial_complex L /\ combinatorial_manifold 2 L /\
     moi_ftp_dpath L P n /\ (!i k. i <= n /\ k <= n /\ P i = P k ==> i = k) /\
     SUC j < n /\ P j INTER P(SUC j) = segment[s,r] /\ ~(s = r)
     ==> ~(s = moi_ftp_third (P(SUC j)) s r) /\ ~(r = moi_ftp_third (P(SUC j)) s r) /\
         P(SUC j) = convex hull {s, r, moi_ftp_third (P(SUC j)) s r} /\
         ~affine_dependent {s, r, moi_ftp_third (P(SUC j)) s r} /\
         ((P(SUC j) INTER P(SUC(SUC j)) = segment[s, moi_ftp_third (P(SUC j)) s r] /\
           moi_ftp_third (P(SUC j)) s (moi_ftp_third (P(SUC j)) s r) = r) \/
          (P(SUC j) INTER P(SUC(SUC j)) = segment[moi_ftp_third (P(SUC j)) s r, r] /\
           ~(P(SUC j) INTER P(SUC(SUC j)) = segment[s, moi_ftp_third (P(SUC j)) s r]) /\
           moi_ftp_third (P(SUC j)) (moi_ftp_third (P(SUC j)) s r) r = s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `z = moi_ftp_third ((P:num->real^N->bool)(SUC j)) s r` THEN
  SUBGOAL_THEN `j < n /\ SUC j <= n /\ SUC(SUC j) <= n /\ j <= n` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SUC j < n` THEN ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `moi_ftp_dpath L (P:num->real^N->bool) n` THEN
  REWRITE_TAC[moi_ftp_dpath] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(P:num->real^N->bool) j IN L /\ aff_dim(P j) = &2 /\
                P(SUC j) IN L /\ aff_dim(P(SUC j)) = &2 /\
                P(SUC(SUC j)) IN L /\ aff_dim(P(SUC(SUC j))) = &2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  (* the vertices of P (SUC j) *)
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `(P:num->real^N->bool)(SUC j)`;
                 `s:real^N`; `r:real^N`] MOI_FTP_EDGE_VERTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(P:num->real^N->bool) j INTER P(SUC j) = segment[s,r]`)) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    DISCH_THEN(MP_TAC o SPECL [`(P:num->real^N->bool) j`; `(P:num->real^N->bool)(SUC j)`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z':real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `z':real^N = z` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `moi_ftp_third ((P:num->real^N->bool)(SUC j)) s r = z` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  (* the next crossed edge is an edge of P (SUC j) *)
  MP_TAC(ISPECL [`s:real^N`; `r:real^N`; `z:real^N`;
                 `(P:num->real^N->bool)(SUC j) INTER P(SUC(SUC j))`] MOI_FTP_EDGE_OF_TRI) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(P:num->real^N->bool)(SUC j) = convex hull {s,r,z}`)) THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                  GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
      DISCH_THEN(MP_TAC o SPECL [`(P:num->real^N->bool)(SUC j)`;
                                 `(P:num->real^N->bool)(SUC(SUC j))`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `&1:int`)) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* it is not [s,r] *)
  SUBGOAL_THEN `~((P:num->real^N->bool)(SUC j) INTER P(SUC(SUC j)) = segment[s,r])`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `segment[s:real^N,r]`] MOI_FCL_EDGE_TRIANGLES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(P:num->real^N->bool) j INTER P(SUC j) = segment[s,r]`)) THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
      DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `(P:num->real^N->bool) j` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                  GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
      DISCH_THEN(MP_TAC o SPECL [`(P:num->real^N->bool) j`; `(P:num->real^N->bool)(SUC j)`]) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC (K ALL_TAC))))) THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `((P:num->real^N->bool) j = t1 \/ P j = t2) /\
      (P(SUC j) = t1 \/ P(SUC j) = t2) /\
      (P(SUC(SUC j)) = t1 \/ P(SUC(SUC j)) = t2)`
    ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((P:num->real^N->bool) j = P(SUC j)) /\ ~(P(SUC j) = P(SUC(SUC j)))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_FTP_DPATH_NEQ THEN
      MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `n:num`] THEN
      ASM_REWRITE_TAC[moi_ftp_dpath];
      ALL_TAC] THEN
    SUBGOAL_THEN `(P:num->real^N->bool) j = P(SUC(SUC j))` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `j = SUC(SUC j)` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        concl th = `!i k. i <= n /\ k <= n /\ (P:num->real^N->bool) i = P k ==> i = k`)) THEN
      ASM_REWRITE_TAC[];
      ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_MESON_TAC[];
    DISJ1_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ISPECL [`(P:num->real^N->bool)(SUC j)`; `s:real^N`; `r:real^N`; `z:real^N`]
                    MOI_FTP_THIRD) THEN ASM_SIMP_TAC[]];
    DISJ2_TAC THEN REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[ASSUME
        `(P:num->real^N->bool)(SUC j) INTER P(SUC(SUC j)) = segment[r,z]`] THEN
      REWRITE_TAC[SEGMENT_EQ] THEN UNDISCH_TAC `~(s:real^N = r)` THEN
      UNDISCH_TAC `~(r:real^N = z)` THEN UNDISCH_TAC `~(s:real^N = z)` THEN SET_TAC[];
      MP_TAC(ISPECL [`(P:num->real^N->bool)(SUC j)`; `s:real^N`; `r:real^N`; `z:real^N`]
                    MOI_FTP_THIRD) THEN ASM_SIMP_TAC[]]]);;

(* The labels of an injective dual path. *)

let moi_ftp_s = new_definition
 `moi_ftp_s (P:num->real^N->bool) (s0:real^N) (r0:real^N) j =
    FST(moi_ftp_lab P s0 r0 j)`;;

let moi_ftp_r = new_definition
 `moi_ftp_r (P:num->real^N->bool) (s0:real^N) (r0:real^N) j =
    SND(moi_ftp_lab P s0 r0 j)`;;

let moi_ftp_y = new_definition
 `moi_ftp_y (P:num->real^N->bool) (s0:real^N) (r0:real^N) j =
    moi_ftp_third (P j) (moi_ftp_s P s0 r0 j) (moi_ftp_r P s0 r0 j)`;;

let moi_ftp_z = new_definition
 `moi_ftp_z (P:num->real^N->bool) (s0:real^N) (r0:real^N) j =
    moi_ftp_third (P(SUC j)) (moi_ftp_s P s0 r0 j) (moi_ftp_r P s0 r0 j)`;;

let MOI_FTP_LAB_SUC = prove
 (`!(P:num->real^N->bool) s0 r0 j.
     moi_ftp_s P s0 r0 0 = s0 /\ moi_ftp_r P s0 r0 0 = r0 /\
     moi_ftp_s P s0 r0 (SUC j) =
       (if P(SUC j) INTER P(SUC(SUC j)) =
           segment[moi_ftp_s P s0 r0 j, moi_ftp_z P s0 r0 j]
        then moi_ftp_s P s0 r0 j else moi_ftp_z P s0 r0 j) /\
     moi_ftp_r P s0 r0 (SUC j) =
       (if P(SUC j) INTER P(SUC(SUC j)) =
           segment[moi_ftp_s P s0 r0 j, moi_ftp_z P s0 r0 j]
        then moi_ftp_z P s0 r0 j else moi_ftp_r P s0 r0 j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftp_s; moi_ftp_r; moi_ftp_z; moi_ftp_lab] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let MOI_FTP_LABELS = prove
 (`!(L:(real^N->bool)->bool) P n s0 r0.
     FINITE L /\ lf_simplicial_complex L /\ combinatorial_manifold 2 L /\
     moi_ftp_dpath L P n /\ (!i k. i <= n /\ k <= n /\ P i = P k ==> i = k) /\
     P 0 INTER P(SUC 0) = segment[s0,r0] /\ ~(s0 = r0)
     ==> !j. j < n
             ==> P j INTER P(SUC j) = segment[moi_ftp_s P s0 r0 j, moi_ftp_r P s0 r0 j] /\
                 ~(moi_ftp_s P s0 r0 j = moi_ftp_r P s0 r0 j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[MOI_FTP_LAB_SUC]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [UNDISCH_TAC `SUC j < n` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `P:num->real^N->bool`; `n:num`; `j:num`;
                 `moi_ftp_s (P:num->real^N->bool) s0 r0 j`;
                 `moi_ftp_r (P:num->real^N->bool) s0 r0 j`] MOI_FTP_LAB_STEP0) THEN
  ASM_REWRITE_TAC[GSYM moi_ftp_z] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[MOI_FTP_LAB_SUC] THEN ASM_MESON_TAC[]);;

(* Adjacent link triangles have apex determinants of opposite signs. *)

let MOI_FTP_LINK_ADJ = prove
 (`!(c:(real^3->bool)->bool) v s r y z.
     lf_simplicial_complex c /\ {v} IN c /\
     convex hull {s,r,y} IN simplicial_link c v /\ aff_dim(convex hull {s,r,y}) = &2 /\
     convex hull {s,r,z} IN simplicial_link c v /\ aff_dim(convex hull {s,r,z}) = &2 /\
     ~(y = z)
     ==> det(vector[s - v; r - v; y - v]) * det(vector[s - v; r - v; z - v]) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FM3_OPPOSITE_SIDES THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x:real^3. convex hull {v,s,r,x} = convex hull (v INSERT convex hull {s,r,x})`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ONCE_REWRITE_TAC[SET_RULE `(v:real^3) INSERT s = {v} UNION s`] THEN
    MATCH_ACCEPT_TAC HULL_UNION_RIGHT;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `convex hull {s:real^3,r,y}`]
                MOI_FM3_LINK_JOIN) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `convex hull {s:real^3,r,z}`]
                MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

(* The hypotheses of MOI_FTP_JINV for the labels of an injective dual path *)
(* of link triangles of a vertex v of a complex in real^3.                  *)

let MOI_FTP_PATH_J = prove
 (`!(c:(real^3->bool)->bool) v P n s0 r0.
     lf_simplicial_complex c /\ {v} IN c /\
     FINITE (simplicial_link c v) /\ combinatorial_manifold 2 (simplicial_link c v) /\
     moi_ftp_dpath (simplicial_link c v) P n /\
     (!i k. i <= n /\ k <= n /\ P i = P k ==> i = k) /\
     P 0 INTER P(SUC 0) = segment[s0,r0] /\ ~(s0 = r0)
     ==> (!j. j < n
              ==> det(vector[moi_ftp_s P s0 r0 j - v; moi_ftp_r P s0 r0 j - v;
                             moi_ftp_y P s0 r0 j - v]) *
                  det(vector[moi_ftp_s P s0 r0 j - v; moi_ftp_r P s0 r0 j - v;
                             moi_ftp_z P s0 r0 j - v]) < &0) /\
         (!j. SUC j < n
              ==> (moi_ftp_s P s0 r0 (SUC j) = moi_ftp_s P s0 r0 j /\
                   moi_ftp_r P s0 r0 (SUC j) = moi_ftp_z P s0 r0 j /\
                   moi_ftp_y P s0 r0 (SUC j) = moi_ftp_r P s0 r0 j) \/
                  (moi_ftp_s P s0 r0 (SUC j) = moi_ftp_z P s0 r0 j /\
                   moi_ftp_r P s0 r0 (SUC j) = moi_ftp_r P s0 r0 j /\
                   moi_ftp_y P s0 r0 (SUC j) = moi_ftp_s P s0 r0 j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (simplicial_link c (v:real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LINK_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^3)`; `P:num->real^3->bool`; `n:num`;
                 `s0:real^3`; `r0:real^3`] MOI_FTP_LABELS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_ftp_dpath (simplicial_link c v) (P:num->real^3->bool) n` THEN
  REWRITE_TAC[moi_ftp_dpath] THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `moi_ftp_s:(num->real^3->bool)->real^3->real^3->num->real^3`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `j <= n /\ SUC j <= n` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `j:num < n` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(P:num->real^3->bool) j IN simplicial_link c v /\ aff_dim(P j) = &2 /\
      P(SUC j) IN simplicial_link c v /\ aff_dim(P(SUC j)) = &2`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `segment[moi_ftp_s P s0 r0 j,moi_ftp_r P s0 r0 j] face_of (P:num->real^3->bool) j /\
      segment[moi_ftp_s P s0 r0 j,moi_ftp_r P s0 r0 j] face_of P(SUC j)`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) &&
        lhand(concl th) = `(P:num->real^3->bool) j INTER P(SUC j)`)) THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                  GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
      DISCH_THEN(MP_TAC o SPECL [`(P:num->real^3->bool) j`; `(P:num->real^3->bool)(SUC j)`]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`simplicial_link c (v:real^3)`; `(P:num->real^3->bool) j`;
                   `moi_ftp_s (P:num->real^3->bool) s0 r0 j`;
                   `moi_ftp_r (P:num->real^3->bool) s0 r0 j`] MOI_FTP_EDGE_VERTS) THEN
    MP_TAC(ISPECL [`simplicial_link c (v:real^3)`; `(P:num->real^3->bool)(SUC j)`;
                   `moi_ftp_s (P:num->real^3->bool) s0 r0 j`;
                   `moi_ftp_r (P:num->real^3->bool) s0 r0 j`] MOI_FTP_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[GSYM moi_ftp_y; GSYM moi_ftp_z] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `y:real^3 = moi_ftp_y P s0 r0 j /\ z = moi_ftp_z P s0 r0 j`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FTP_LINK_ADJ THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(UNDISCH_TAC `(P:num->real^3->bool) j IN simplicial_link c v` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(UNDISCH_TAC `(P:num->real^3->bool) (SUC j) IN simplicial_link c v` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(UNDISCH_TAC `aff_dim((P:num->real^3->bool) j) = &2` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(UNDISCH_TAC `aff_dim((P:num->real^3->bool) (SUC j)) = &2` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`simplicial_link c (v:real^3)`; `P:num->real^3->bool`; `n:num`; `j:num`]
                  MOI_FTP_DPATH_NEQ) THEN
    ASM_REWRITE_TAC[moi_ftp_dpath];
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      can (find_term ((=) `moi_ftp_s:(num->real^3->bool)->real^3->real^3->num->real^3`))
          (concl th))) THEN
    ANTS_TAC THENL [UNDISCH_TAC `SUC j < n` THEN ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`simplicial_link c (v:real^3)`; `P:num->real^3->bool`; `n:num`; `j:num`;
                   `moi_ftp_s (P:num->real^3->bool) s0 r0 j`;
                   `moi_ftp_r (P:num->real^3->bool) s0 r0 j`] MOI_FTP_LAB_STEP0) THEN
    ASM_REWRITE_TAC[moi_ftp_dpath; GSYM moi_ftp_z] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
       (DISJ_CASES_THEN STRIP_ASSUME_TAC))))) THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[MOI_FTP_LAB_SUC; moi_ftp_y];
      DISJ2_TAC THEN ASM_REWRITE_TAC[MOI_FTP_LAB_SUC; moi_ftp_y]]]);;

(* ========================================================================= *)
(* Planar pieces in a link triangle.  A function f affine                   *)
(* along segments (an apex determinant D(e1,e2,.) or a level function of    *)
(* the dual cells) with f = 0 on an edge of a triangle and f k > 0 at the   *)
(* opposite vertex cuts the triangle in that edge on the side f k <= 0      *)
(* (MOI_FTP_HALFK_EDGE).  Two triangles on opposite sides of a common edge  *)
(* glue to a 2-cell (MOI_FTP_GLUE_TRI); a fan of three triangles (the kite  *)
(* piece, MOI_FTP_FAN3) and the trapezoid between sub-segments of two      *)
(* edges of a triangle (MOI_FTP_QUAD) are 2-cells with their polygonal      *)
(* boundary.  Signs are computed by the plane determinant formula           *)
(* MOI_FTP_DET_PLANE.                                                        *)
(* ========================================================================= *)

let MOI_FTP_DETF_AFF = prove
 (`!v e1 e2:real^3 x y u.
     det(vector[e1 - v; e2 - v; ((&1 - u) % x + u % y) - v]) =
     (&1 - u) * det(vector[e1 - v; e2 - v; x - v]) +
     u * det(vector[e1 - v; e2 - v; y - v])`,
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN CONV_TAC REAL_RING);;

let MOI_FTP_DET_PLANE = prove
 (`!v w u u' x1 y1 x2 y2 x3 y3.
     det(vector[(w + x1 % (u - w) + y1 % (u' - w)) - v;
                (w + x2 % (u - w) + y2 % (u' - w)) - v;
                (w + x3 % (u - w) + y3 % (u' - w)) - v]) =
     ((x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)) *
     det(vector[w - v; u - v; u' - v:real^3])`,
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN CONV_TAC REAL_RING);;

let MOI_FTP_AFF_CONVEX = prove
 (`!(f:real^N->real) t.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y)
     ==> convex {x | f x < t} /\ convex {x | f x <= t} /\
         convex {x | t < f x} /\ convex {x | t <= f x}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[convex; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`; `w:real`] THEN STRIP_TAC THEN
  (SUBGOAL_THEN `u = &1 - w` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_CONVEX_BOUND_LT; REAL_CONVEX_BOUND_LE; REAL_CONVEX_BOUND_GT;
                REAL_CONVEX_BOUND_GE]);;

let MOI_FTP_HALF_EDGE = prove
 (`!(f:real^N->real) t a b c.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     f a = t /\ f c = t /\ t < f b
     ==> convex hull {a,b,c} INTER {x | f x <= t} = segment[a,c]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; MOI_FTC_IN_HULL3; IN_SEGMENT] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real` (X_CHOOSE_THEN `u3:real`
         STRIP_ASSUME_TAC))) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^N->real`; `a:real^N`; `b:real^N`; `c:real^N`;
                   `u1:real`; `u2:real`; `u3:real`] MOI_FTC_AFFINE_COMB3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `u2 = &0` SUBST_ALL_TAC THENL
     [ASM_CASES_TAC `u2 = &0` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < u2 * (f(b:real^N) - t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `u1 * t + u2 * f(b:real^N) + u3 * t = t + u2 * (f b - t)`
      (fun th -> UNDISCH_TAC `u1 * t + u2 * f(b:real^N) + u3 * t <= t` THEN
                 REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `u1 + u2 + u3 = &1` THEN CONV_TAC REAL_RING; REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `u3:real` THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    SUBGOAL_THEN `u1 = &1 - u3` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&1 - u`; `&0`; `u:real`] THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN VECTOR_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let MOI_FTP_HALF_VERT = prove
 (`!(f:real^N->real) t a b c.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     f a = t /\ t < f b /\ t < f c
     ==> convex hull {a,b,c} INTER {x | f x <= t} = {a}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; MOI_FTC_IN_HULL3; IN_SING] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real` (X_CHOOSE_THEN `u3:real`
         STRIP_ASSUME_TAC))) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^N->real`; `a:real^N`; `b:real^N`; `c:real^N`;
                   `u1:real`; `u2:real`; `u3:real`] MOI_FTC_AFFINE_COMB3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `u1 * t + u2 * f(b:real^N) + u3 * f(c:real^N) =
                  t + u2 * (f b - t) + u3 * (f c - t)` ASSUME_TAC THENL
     [UNDISCH_TAC `u1 + u2 + u3 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= u2 * (f(b:real^N) - t) /\ &0 <= u3 * (f(c:real^N) - t)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `u2 * (f(b:real^N) - t) = &0 /\ u3 * (f(c:real^N) - t) = &0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THEN
    TRY(UNDISCH_TAC `f(b:real^N) - t = &0` THEN ASM_REAL_ARITH_TAC) THEN
    TRY(UNDISCH_TAC `f(c:real^N) - t = &0` THEN ASM_REAL_ARITH_TAC) THEN
    SUBGOAL_THEN `u1 = &1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&1`; `&0`; `&0`] THEN
      REWRITE_TAC[REAL_POS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LE_REFL]]]);;

let MOI_FTP_HALF_SEG = prove
 (`!(f:real^N->real) t a b.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     f a = t /\ t < f b
     ==> segment[a,b] INTER {x | f x <= t} = {a}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SEGMENT; IN_SING] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `u = &0` SUBST1_TAC THENL
     [ASM_CASES_TAC `u = &0` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < u * (f(b:real^N) - t)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(&1 - u) * t + u * f(b:real^N) <= t` THEN REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_POS] THEN VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_LE_REFL]]]);;

(* The same with the side given by the sign of f k. *)

let MOI_FTP_HALFK_EDGE = prove
 (`!(f:real^N->real) k a b c.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     f a = &0 /\ f c = &0 /\ &0 < f b * k
     ==> convex hull {a,b,c} INTER {x | f x * k <= &0} = segment[a,c]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`\z:real^N. f z * k:real`; `&0`; `a:real^N`; `b:real^N`;
                           `c:real^N`] MOI_FTP_HALF_EDGE)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_FTP_HALFK_VERT = prove
 (`!(f:real^N->real) k a b c.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     f a = &0 /\ &0 < f b * k /\ &0 < f c * k
     ==> convex hull {a,b,c} INTER {x | f x * k <= &0} = {a}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`\z:real^N. f z * k:real`; `&0`; `a:real^N`; `b:real^N`;
                           `c:real^N`] MOI_FTP_HALF_VERT)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_FTP_HALFK_SEG = prove
 (`!(f:real^N->real) k a b.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     f a = &0 /\ &0 < f b * k
     ==> segment[a,b] INTER {x | f x * k <= &0} = {a}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`\z:real^N. f z * k:real`; `&0`; `a:real^N`; `b:real^N`]
    MOI_FTP_HALF_SEG)) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_FTP_HALFK_CONVEX = prove
 (`!(f:real^N->real) k.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y)
     ==> convex {x | f x * k <= &0} /\ convex {x | &0 < f x * k}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(BETA_RULE(ISPECL [`\z:real^N. f z * k:real`; `&0`] MOI_FTP_AFF_CONVEX)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN REAL_ARITH_TAC; SIMP_TAC[]]);;

(* A function affine along segments vanishing at a and c and not at b:     *)
(* the three points are not collinear.                                      *)

let MOI_FTP_AFF_NONCOLL = prove
 (`!(f:real^N->real) a b c.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     ~(a = c) /\ f a = &0 /\ f c = &0 /\ ~(f b = &0)
     ==> ~collinear {a,b,c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{a:real^N,b,c} = {a,c,b}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL; AFFINE_HULL_2; IN_ELIM_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`u:real`; `w:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `u = &1 - w` SUBST_ALL_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~(f(b:real^N) = &0)` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* f vanishes along a segment between two zeros. *)

let MOI_FTP_AFF_SEG_ZERO = prove
 (`!(f:real^N->real) a c x.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     f a = &0 /\ f c = &0 /\ x IN segment[a,c]
     ==> f x = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Two triangles on opposite sides of their common edge [a,c] (f vanishes  *)
(* on a and c, f b and f d have opposite signs) meet in that edge and form  *)
(* a 2-cell bounded by the four outer edges.                                *)

let MOI_FTP_GLUE_TRI = prove
 (`!(f:real^N->real) a b c d.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     ~(a = c) /\ f a = &0 /\ f c = &0 /\ f b * f d < &0
     ==> convex hull {a,b,c} INTER convex hull {a,c,d} = segment[a,c] /\
         pl_cell_with_boundary 2 (convex hull {a,b,c} UNION convex hull {a,c,d})
           (segment[a,b] UNION segment[b,c] UNION segment[c,d] UNION segment[d,a])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(f(b:real^N) = &0) /\ ~(f(d:real^N) = &0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `f(b:real^N) * f d < &0` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < f(b:real^N) * f b /\ &0 < f(d:real^N) * f d /\ f(d:real^N) * f b < &0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_SQUARE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {a:real^N,b,c} /\ ~collinear {a:real^N,c,d}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTP_AFF_NONCOLL THEN EXISTS_TAC `f:real^N->real` THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `{a:real^N,c,d} = {a,d,c}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_FTP_AFF_NONCOLL THEN EXISTS_TAC `f:real^N->real` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a,c,d} SUBSET {x:real^N | f x * f b <= &0}` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_SIMP_TAC[MOI_FTP_HALFK_CONVEX] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a,b,c} INTER convex hull {a,c,d} = segment[a:real^N,c]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`f:real^N->real`; `f(b:real^N):real`; `a:real^N`; `b:real^N`;
                     `c:real^N`] MOI_FTP_HALFK_EDGE) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `convex hull {a,c,d} SUBSET {x:real^N | f x * f b <= &0}` THEN SET_TAC[];
      REWRITE_TAC[SUBSET_INTER; SEGMENT_CONVEX_HULL] THEN CONJ_TAC THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`convex hull {a,b,c}:real^N->bool`;
                 `segment[a:real^N,b] UNION segment[b,c] UNION segment[c,a]`;
                 `convex hull {a,c,d}:real^N->bool`;
                 `segment[a:real^N,c] UNION segment[c,d] UNION segment[d,a]`;
                 `a:real^N`; `c:real^N`] MOI_FTC_GLUE_SEG) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FTC_TRI_CELL] THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `segment[a:real^N,c] SUBSET {x | f x * f b <= &0} /\
                segment[a:real^N,c] SUBSET {x | f x * f d <= &0}` MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real`; `a:real^N`; `c:real^N`; `x:real^N`]
      MOI_FTP_AFF_SEG_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->real`; `f(b:real^N):real`; `a:real^N`; `b:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`f:real^N->real`; `f(b:real^N):real`; `c:real^N`; `b:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`f:real^N->real`; `f(d:real^N):real`; `c:real^N`; `d:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`f:real^N->real`; `f(d:real^N):real`; `a:real^N`; `d:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]);;

(* A fan of three triangles at p: conv{p,a,c} and conv{p,c,q} on opposite   *)
(* sides of [p,c], and conv{m,p,q} on the other side of [p,q].              *)

let MOI_FTP_FAN3 = prove
 (`!(f:real^N->real) g m p q a c.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     (!x y u. g((&1 - u) % x + u % y) = (&1 - u) * g x + u * g y) /\
     ~(p = c) /\ f p = &0 /\ f c = &0 /\ f a * f q < &0 /\
     ~(p = q) /\ g p = &0 /\ g q = &0 /\ g m * g a < &0 /\ &0 < g a * g c
     ==> pl_cell_with_boundary 2
           (convex hull {m,p,q} UNION convex hull {p,a,c} UNION convex hull {p,c,q})
           (segment[m,p] UNION segment[p,a] UNION segment[a,c] UNION segment[c,q] UNION
            segment[q,m])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `p:real^N`; `a:real^N`; `c:real^N`; `q:real^N`]
    MOI_FTP_GLUE_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(g(m:real^N) = &0) /\ ~(g(a:real^N) = &0) /\ ~(g(c:real^N) = &0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `g(m:real^N) * g a < &0`; UNDISCH_TAC `g(m:real^N) * g a < &0`;
      UNDISCH_TAC `&0 < g(a:real^N) * g c`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < g(a:real^N) * g a /\ &0 < g(m:real^N) * g m /\
                &0 < g(c:real^N) * g a /\ g(a:real^N) * g m < &0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_SQUARE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {m:real^N,p,q}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^N->real`; `p:real^N`; `m:real^N`; `q:real^N`]
      MOI_FTP_AFF_NONCOLL) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {m,p,q} SUBSET {x:real^N | g x * g a <= &0}` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_SIMP_TAC[MOI_FTP_HALFK_CONVEX] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,c] SUBSET {x | &0 < g x * g a}` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_SIMP_TAC[MOI_FTP_HALFK_CONVEX] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p:real^N,q] SUBSET {x | g x * g a <= &0} /\
                segment[p:real^N,q] SUBSET {x | g x * g m <= &0}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`g:real^N->real`; `p:real^N`; `q:real^N`; `x:real^N`]
      MOI_FTP_AFF_SEG_ZERO) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(convex hull {p,a,c} UNION convex hull {p,c,q}) INTER convex hull {m,p,q} =
    segment[p:real^N,q]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`g:real^N->real`; `g(a:real^N):real`; `p:real^N`; `a:real^N`;
                     `c:real^N`] MOI_FTP_HALFK_VERT) THEN
      MP_TAC(ISPECL [`g:real^N->real`; `g(a:real^N):real`; `p:real^N`; `c:real^N`;
                     `q:real^N`] MOI_FTP_HALFK_EDGE) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `convex hull {m,p,q} SUBSET {x:real^N | g x * g a <= &0}` THEN
      MP_TAC(ISPECL [`p:real^N`; `q:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      REWRITE_TAC[SUBSET_INTER; SEGMENT_CONVEX_HULL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET u ==> s SUBSET t UNION u`);
        ALL_TAC] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull {p,a,c} UNION convex hull {p,c,q}:real^N->bool`;
                 `segment[p:real^N,a] UNION segment[a,c] UNION segment[c,q] UNION
                  segment[q,p]`;
                 `convex hull {m,p,q}:real^N->bool`;
                 `segment[m:real^N,p] UNION segment[p,q] UNION segment[q,m]`;
                 `p:real^N`; `q:real^N`] MOI_FTC_GLUE_SEG) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FTC_TRI_CELL] THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
  EXISTS_TAC `(convex hull {p,a,c} UNION convex hull {p,c,q}) UNION
              convex hull {m:real^N,p,q}` THEN
  EXISTS_TAC `((segment[p:real^N,a] UNION segment[a,c] UNION segment[c,q] UNION
               segment[q,p]) UNION (segment[m,p] UNION segment[p,q] UNION segment[q,m]))
              DIFF (segment[p,q] DIFF {p,q})` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^N->real`; `g(a:real^N):real`; `p:real^N`; `a:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`g:real^N->real`; `g(a:real^N):real`; `q:real^N`; `c:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`g:real^N->real`; `g(m:real^N):real`; `p:real^N`; `m:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`g:real^N->real`; `g(m:real^N):real`; `q:real^N`; `m:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `segment[a:real^N,c] SUBSET {x | &0 < g x * g a}` THEN
  SUBGOAL_THEN `{x:real^N | &0 < g x * g a} INTER {x | g x * g a <= &0} = {}` MP_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `segment[p:real^N,q] SUBSET {x | g x * g a <= &0}` THEN
  UNDISCH_TAC `segment[p:real^N,q] SUBSET {x | g x * g m <= &0}` THEN
  REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]);;

let MOI_FTP_HALFK_SUBSETS = prove
 (`!(f:real^N->real) k a b c.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y)
     ==> (f a * k <= &0 /\ f b * k <= &0 /\ f c * k <= &0
          ==> convex hull {a,b,c} SUBSET {x | f x * k <= &0}) /\
         (f a * k <= &0 /\ f b * k <= &0 ==> segment[a,b] SUBSET {x | f x * k <= &0}) /\
         (&0 < f a * k /\ &0 < f b * k /\ &0 < f c * k
          ==> convex hull {a,b,c} SUBSET {x | &0 < f x * k}) /\
         (&0 < f a * k /\ &0 < f b * k ==> segment[a,b] SUBSET {x | &0 < f x * k})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_SIMP_TAC[MOI_FTP_HALFK_CONVEX] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM]);;

let MOI_FTP_HALFK_ZERO = prove
 (`!(f:real^N->real) k a b.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     f a = &0 /\ f b = &0
     ==> segment[a,b] SUBSET {x | f x * k <= &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `a:real^N`; `b:real^N`; `x:real^N`]
    MOI_FTP_AFF_SEG_ZERO) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL]);;

let MOI_FTP_DET_REP = prove
 (`!v x y:real^3.
     det(vector[x - v; y - v; x - v]) = &0 /\ det(vector[x - v; y - v; y - v]) = &0`,
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_RING);;

let MOI_FTP_POS_SQ = prove
 (`!x d. &0 < x /\ ~(d = &0) ==> &0 < x * (d * d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_SQUARE]);;

(* The trapezoid between the sub-segments [a,c] of [w,u] and [a',c'] of      *)
(* [w,u'] (a, a' both nearer to w or both farther), cut by the diagonal     *)
(* [a,c'].                                                                   *)

let MOI_FTP_QUAD = prove
 (`!v w u u':real^3 a c a' c' al ga al' ga'.
     ~(det(vector[w - v; u - v; u' - v]) = &0) /\
     a = w + al % (u - w) /\ c = w + ga % (u - w) /\
     a' = w + al' % (u' - w) /\ c' = w + ga' % (u' - w) /\
     &0 < al /\ al < &1 /\ &0 < ga /\ ga < &1 /\
     &0 < al' /\ al' < &1 /\ &0 < ga' /\ ga' < &1 /\
     &0 < (al - ga) * (al' - ga')
     ==> pl_cell_with_boundary 2 (convex hull {a,c,c'} UNION convex hull {a,c',a'})
           (segment[a,c] UNION segment[c,c'] UNION segment[c',a'] UNION segment[a',a]) /\
         convex hull {a,c,c'} UNION convex hull {a,c',a'} SUBSET convex hull {w,u,u'} /\
         (convex hull {a,c,c'} UNION convex hull {a,c',a'}) INTER segment[w,u] =
         segment[a,c] /\
         (convex hull {a,c,c'} UNION convex hull {a,c',a'}) INTER segment[w,u'] =
         segment[a',c'] /\
         ~(w IN convex hull {a,c,c'} UNION convex hull {a,c',a'}) /\
         ~(u IN convex hull {a,c,c'} UNION convex hull {a,c',a'}) /\
         ~(u' IN convex hull {a,c,c'} UNION convex hull {a,c',a'}) /\
         segment[a,a'] INTER segment[c,c'] = {} /\
         segment[a,a'] INTER segment[a,c] = {a} /\
         segment[a,a'] INTER segment[a',c'] = {a'} /\
         segment[c,c'] INTER segment[a,c] = {c} /\
         segment[c,c'] INTER segment[a',c'] = {c'} /\
         ~(a = c) /\ ~(a' = c')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `D0 = det(vector[w - v; u - v; u' - v:real^3])` THEN
  (* the values of the four determinant functionals *)
  SUBGOAL_THEN
   `det(vector[a - v; c' - v; c - v:real^3]) = (al - ga) * ga' * D0 /\
    det(vector[a - v; c' - v; a' - v:real^3]) = al * (ga' - al') * D0 /\
    det(vector[w - v; u - v; a - v:real^3]) = &0 /\
    det(vector[w - v; u - v; c - v:real^3]) = &0 /\
    det(vector[w - v; u - v; a' - v:real^3]) = al' * D0 /\
    det(vector[w - v; u - v; c' - v:real^3]) = ga' * D0 /\
    det(vector[w - v; u' - v; a - v:real^3]) = --(al * D0) /\
    det(vector[w - v; u' - v; c - v:real^3]) = --(ga * D0) /\
    det(vector[w - v; u' - v; a' - v:real^3]) = &0 /\
    det(vector[w - v; u' - v; c' - v:real^3]) = &0 /\
    det(vector[u - v; u' - v; a - v:real^3]) = (&1 - al) * D0 /\
    det(vector[u - v; u' - v; c - v:real^3]) = (&1 - ga) * D0 /\
    det(vector[u - v; u' - v; a' - v:real^3]) = (&1 - al') * D0 /\
    det(vector[u - v; u' - v; c' - v:real^3]) = (&1 - ga') * D0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "D0" THEN
    REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    REPEAT CONJ_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `det(vector[a - v; c' - v; a - v:real^3]) = &0 /\
    det(vector[a - v; c' - v; c' - v:real^3]) = &0 /\
    det(vector[w - v; u - v; w - v:real^3]) = &0 /\
    det(vector[w - v; u - v; u - v:real^3]) = &0 /\
    det(vector[w - v; u' - v; w - v:real^3]) = &0 /\
    det(vector[w - v; u' - v; u' - v:real^3]) = &0 /\
    det(vector[u - v; u' - v; u - v:real^3]) = &0 /\
    det(vector[u - v; u' - v; u' - v:real^3]) = &0`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[MOI_FTP_DET_REP]; ALL_TAC] THEN
  MAP_EVERY (fun (e1,e2) ->
    MP_TAC(BETA_RULE(ISPECL [`v:real^3`; e1; e2] MOI_FTP_DETF_AFF)))
   [`a:real^3`,`c':real^3`; `w:real^3`,`u:real^3`; `w:real^3`,`u':real^3`;
    `u:real^3`,`u':real^3`] THEN
  REPEAT DISCH_TAC THEN
  (* sign facts *)
  SUBGOAL_THEN `~(al' = ga':real) /\ ~(al = ga:real)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `&0 < (al - ga) * (al' - ga')` THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((al - ga) * ga' * D0) * (al * (ga' - al') * D0) < &0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `((al - ga) * ga' * D0) * (al * (ga' - al') * D0) =
                  --((((al - ga) * (al' - ga')) * (ga' * al)) * (D0 * D0))`
    SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
    REWRITE_TAC[REAL_NEG_LT0] THEN MATCH_MP_TAC MOI_FTP_POS_SQ THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (al * (ga' - al') * D0) * (al * (ga' - al') * D0) /\
    &0 < ((al - ga) * ga' * D0) * ((al - ga) * ga' * D0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_SQUARE; REAL_ENTIRE; DE_MORGAN_THM] THEN
    ASM_REWRITE_TAC[REAL_SUB_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (al' * D0) * D0 /\ &0 < (ga' * D0) * D0 /\
    &0 < --(al * D0) * --D0 /\ &0 < --(ga * D0) * --D0 /\
    &0 < ((&1 - al) * D0) * D0 /\ &0 < ((&1 - ga) * D0) * D0 /\
    &0 < ((&1 - al') * D0) * D0 /\ &0 < ((&1 - ga') * D0) * D0`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_NEG_MUL2; GSYM REAL_MUL_ASSOC] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_FTP_POS_SQ THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. &0 <= x /\ x <= &1
        ==> w + x % (u - w) IN convex hull {w:real^3,u,u'} /\
            w + x % (u' - w) IN convex hull {w:real^3,u,u'} /\
            w + x % (u - w) IN segment[w,u] /\ w + x % (u' - w) IN segment[w,u']`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    REWRITE_TAC[MOI_FTC_IN_HULL3; IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&1 - x`; `x:real`; `&0`];
      MAP_EVERY EXISTS_TAC [`&1 - x`; `&0`; `x:real`];
      EXISTS_TAC `x:real`; EXISTS_TAC `x:real`] THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `a IN convex hull {w:real^3,u,u'} /\ c IN convex hull {w,u,u'} /\
    a' IN convex hull {w,u,u'} /\ c' IN convex hull {w,u,u'} /\
    a IN segment[w,u] /\ c IN segment[w,u] /\ a' IN segment[w,u'] /\ c' IN segment[w,u']`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `al:real` th) THEN MP_TAC(SPEC `ga:real` th) THEN
                            MP_TAC(SPEC `al':real` th) THEN MP_TAC(SPEC `ga':real` th)) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  (* the point definitions are no longer needed *)
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && is_var(lhs(concl th)) && type_of(lhs(concl th)) = `:real^3`))) THEN
  SUBGOAL_THEN `~(a:real^3 = c') /\ ~(a:real^3 = c) /\ ~(a':real^3 = c')`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. det(vector[w - v; u - v; x - v])`) THEN
      BETA_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SYM) THEN
      REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. det(vector[u - v; u' - v; x - v])`) THEN
      BETA_TAC THEN ASM_REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^3. det(vector[u - v; u' - v; x - v])`) THEN
      BETA_TAC THEN ASM_REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[a - v; c' - v; x - v])`;
     `a:real^3`; `c:real^3`; `c':real^3`; `a':real^3`] MOI_FTP_GLUE_TRI)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the traces on the two edges *)
  SUBGOAL_THEN
   `(convex hull {a,c,c'} UNION convex hull {a,c',a'}) INTER segment[w,u] =
    segment[a:real^3,c]`
  ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u - v; x - v])`; `D0:real`;
       `a:real^3`; `c':real^3`; `c:real^3`] MOI_FTP_HALFK_EDGE)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u - v; x - v])`; `D0:real`;
       `a:real^3`; `c':real^3`; `a':real^3`] MOI_FTP_HALFK_VERT)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u - v; x - v])`; `D0:real`; `w:real^3`; `u:real^3`] MOI_FTP_HALFK_ZERO)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `segment[a:real^3,c] SUBSET segment[w,u] /\
                  segment[a:real^3,c] SUBSET convex hull {a,c,c'}` MP_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_SEGMENT; SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{a:real^3,c',c} = {a,c,c'}` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`convex hull {a:real^3,c,c'} INTER {x | det(vector[w - v; u - v; x - v]) * D0 <= &0} =
       segment[a,c]`;
      `convex hull {a:real^3,c',a'} INTER {x | det(vector[w - v; u - v; x - v]) * D0 <= &0} =
       {a}`;
      `segment[w:real^3,u] SUBSET {x | det(vector[w - v; u - v; x - v]) * D0 <= &0}`] THEN
    MP_TAC(ISPECL [`a:real^3`; `c:real^3`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(convex hull {a,c,c'} UNION convex hull {a,c',a'}) INTER segment[w,u'] =
    segment[a':real^3,c']`
  ASSUME_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u' - v; x - v])`; `--D0`;
       `c':real^3`; `a:real^3`; `c:real^3`] MOI_FTP_HALFK_VERT)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u' - v; x - v])`; `--D0`;
       `c':real^3`; `a:real^3`; `a':real^3`] MOI_FTP_HALFK_EDGE)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u' - v; x - v])`; `--D0`; `w:real^3`; `u':real^3`] MOI_FTP_HALFK_ZERO)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `segment[a':real^3,c'] SUBSET segment[w,u'] /\
                  segment[a':real^3,c'] SUBSET convex hull {a,c',a'}` MP_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_SEGMENT; SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{c':real^3,a,c} = {a,c,c'} /\ {c':real^3,a,a'} = {a,c',a'}`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL [SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`convex hull {a:real^3,c,c'} INTER
       {x | det(vector[w - v; u' - v; x - v]) * --D0 <= &0} = {c'}`;
      `convex hull {a:real^3,c',a'} INTER
       {x | det(vector[w - v; u' - v; x - v]) * --D0 <= &0} = segment[c',a']`;
      `segment[w:real^3,u'] SUBSET {x | det(vector[w - v; u' - v; x - v]) * --D0 <= &0}`] THEN
    MP_TAC(ISPECL [`a':real^3`; `c':real^3`] ENDS_IN_SEGMENT) THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [(* subset of the triangle *)
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET];
    (* w is not in the piece *)
    DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN segment[a,c]` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `segment[a:real^3,c]`)) THEN
      ASM_REWRITE_TAC[IN_INTER; ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u' - v; x - v])`; `--D0`;
       `a:real^3`; `c:real^3`; `c:real^3`] MOI_FTP_HALFK_SUBSETS)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL];
    (* u and u' are not in the piece *)
    SUBGOAL_THEN `convex hull {a,c,c'} UNION convex hull {a,c',a'} SUBSET
                  {x:real^3 | &0 < det(vector[u - v; u' - v; x - v]) * D0}` MP_TAC THENL
     [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
       [MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[u - v; u' - v; x - v])`; `D0:real`;
          `a:real^3`; `c:real^3`; `c':real^3`] MOI_FTP_HALFK_SUBSETS));
        MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[u - v; u' - v; x - v])`; `D0:real`;
          `a:real^3`; `c':real^3`; `a':real^3`] MOI_FTP_HALFK_SUBSETS))] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `u:real^3`) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL];
    SUBGOAL_THEN `convex hull {a,c,c'} UNION convex hull {a,c',a'} SUBSET
                  {x:real^3 | &0 < det(vector[u - v; u' - v; x - v]) * D0}` MP_TAC THENL
     [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
       [MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[u - v; u' - v; x - v])`; `D0:real`;
          `a:real^3`; `c:real^3`; `c':real^3`] MOI_FTP_HALFK_SUBSETS));
        MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[u - v; u' - v; x - v])`; `D0:real`;
          `a:real^3`; `c':real^3`; `a':real^3`] MOI_FTP_HALFK_SUBSETS))] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o SPEC `u':real^3`) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_REFL];
    (* the two sides are disjoint *)
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[a - v; c' - v; x - v])`; `al * (ga' - al') * D0`; `a:real^3`; `a':real^3`]
      MOI_FTP_HALFK_SEG)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[a - v; c' - v; x - v])`; `(al - ga) * ga' * D0`; `c':real^3`; `c:real^3`]
      MOI_FTP_HALFK_SEG)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[a - v; c' - v; x - v])`; `al * (ga' - al') * D0`; `c:real^3`; `c':real^3`;
      `c':real^3`] MOI_FTP_HALFK_SUBSETS)) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_LZERO; REAL_LE_REFL] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^3) IN {x | det(vector[a - v; c' - v; x - v]) *
                                     ((al - ga) * ga' * D0) <= &0}` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM; REAL_MUL_LZERO; REAL_LE_REFL]; ALL_TAC] THEN
    UNDISCH_TAC `~(a:real^3 = c')` THEN
    REWRITE_TAC[SEGMENT_SYM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SEGMENT_SYM]) THEN ASM SET_TAC[];
    (* the sides meet the traces in the end points *)
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u - v; x - v])`; `D0:real`; `a:real^3`; `a':real^3`] MOI_FTP_HALFK_SEG)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u - v; x - v])`; `D0:real`; `a:real^3`; `c:real^3`] MOI_FTP_HALFK_ZERO)) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`a:real^3`; `c:real^3`] ENDS_IN_SEGMENT) THEN
    SET_TAC[];
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u' - v; x - v])`; `--D0`; `a':real^3`; `a:real^3`] MOI_FTP_HALFK_SEG)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u' - v; x - v])`; `--D0`; `a':real^3`; `c':real^3`] MOI_FTP_HALFK_ZERO)) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`a':real^3`; `c':real^3`] ENDS_IN_SEGMENT) THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u - v; x - v])`; `D0:real`; `c:real^3`; `c':real^3`] MOI_FTP_HALFK_SEG)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u - v; x - v])`; `D0:real`; `a:real^3`; `c:real^3`] MOI_FTP_HALFK_ZERO)) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`a:real^3`; `c:real^3`] ENDS_IN_SEGMENT) THEN
    SET_TAC[];
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u' - v; x - v])`; `--D0`; `c':real^3`; `c:real^3`] MOI_FTP_HALFK_SEG)) THEN
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[w - v; u' - v; x - v])`; `--D0`; `a':real^3`; `c':real^3`] MOI_FTP_HALFK_ZERO)) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`a':real^3`; `c':real^3`] ENDS_IN_SEGMENT) THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]]);;

(* The boundary of the fan of MOI_FTP_FAN3 splits at a, c and m into the  *)
(* two sides [m,p] + [p,a], [m,q] + [q,c] and the segment [a,c].           *)

let MOI_FTP_FAN3_SIDES = prove
 (`!(f:real^N->real) g m p q a c.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     (!x y u. g((&1 - u) % x + u % y) = (&1 - u) * g x + u * g y) /\
     ~(p = c) /\ f p = &0 /\ f c = &0 /\ f a * f q < &0 /\
     ~(p = q) /\ g p = &0 /\ g q = &0 /\ g m * g a < &0 /\ &0 < g a * g c
     ==> (segment[m,p] UNION segment[p,a]) INTER segment[a,c] = {a} /\
         (segment[m,q] UNION segment[q,c]) INTER segment[a,c] = {c} /\
         (segment[m,p] UNION segment[p,a]) INTER (segment[m,q] UNION segment[q,c]) = {m} /\
         ~(a = c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(f(a:real^N) = &0) /\ ~(f(q:real^N) = &0) /\
                ~(g(m:real^N) = &0) /\ ~(g(a:real^N) = &0) /\ ~(g(c:real^N) = &0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `f(a:real^N) * f q < &0`; UNDISCH_TAC `f(a:real^N) * f q < &0`;
      UNDISCH_TAC `g(m:real^N) * g a < &0`; UNDISCH_TAC `g(m:real^N) * g a < &0`;
      UNDISCH_TAC `&0 < g(a:real^N) * g c`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < g(a:real^N) * g a /\ &0 < g(m:real^N) * g m /\
                &0 < g(c:real^N) * g a /\ g(a:real^N) * g m < &0 /\
                &0 < f(a:real^N) * f a /\ &0 < f(q:real^N) * f q /\
                f(q:real^N) * f a < &0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_SQUARE] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a:real^N = c)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(f(a:real^N) = &0)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {p:real^N,a,c} /\ ~collinear {m:real^N,p,q}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTP_AFF_NONCOLL THEN EXISTS_TAC `f:real^N->real` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`g:real^N->real`; `p:real^N`; `m:real^N`; `q:real^N`]
        MOI_FTP_AFF_NONCOLL) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `(a <=> b) ==> a ==> b`) THEN
      AP_TERM_TAC THEN AP_TERM_TAC THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p:real^N`; `a:real^N`; `c:real^N`] MOI_FSA_TRI_EDGES) THEN
  MP_TAC(ISPECL [`m:real^N`; `p:real^N`; `q:real^N`] MOI_FSA_TRI_EDGES) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  (* half-plane facts for g (line pq) and f (line pc) *)
  MP_TAC(ISPECL [`g:real^N->real`; `g(a:real^N):real`; `m:real^N`; `p:real^N`;
                 `p:real^N`] MOI_FTP_HALFK_SUBSETS) THEN
  MP_TAC(ISPECL [`g:real^N->real`; `g(a:real^N):real`; `q:real^N`; `m:real^N`;
                 `m:real^N`] MOI_FTP_HALFK_SUBSETS) THEN
  MP_TAC(ISPECL [`g:real^N->real`; `g(a:real^N):real`; `a:real^N`; `c:real^N`;
                 `c:real^N`] MOI_FTP_HALFK_SUBSETS) THEN
  MP_TAC(ISPECL [`f:real^N->real`; `f(q:real^N):real`; `a:real^N`; `c:real^N`;
                 `c:real^N`] MOI_FTP_HALFK_SUBSETS) THEN
  MP_TAC(ISPECL [`f:real^N->real`; `f(a:real^N):real`; `q:real^N`; `c:real^N`;
                 `c:real^N`] MOI_FTP_HALFK_SUBSETS) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_MUL_LZERO; REAL_LE_REFL] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^N->real`; `g(a:real^N):real`; `q:real^N`; `c:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`g:real^N->real`; `g(a:real^N):real`; `p:real^N`; `a:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`g:real^N->real`; `g(m:real^N):real`; `p:real^N`; `m:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`g:real^N->real`; `g(m:real^N):real`; `q:real^N`; `m:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`f:real^N->real`; `f(q:real^N):real`; `c:real^N`; `q:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  MP_TAC(ISPECL [`f:real^N->real`; `f(a:real^N):real`; `p:real^N`; `a:real^N`]
    MOI_FTP_HALFK_SEG) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `{x:real^N | &0 < g x * g a} INTER {x | g x * g a <= &0} = {} /\
    (p:real^N) IN {x | g x * g m <= &0} /\ (q:real^N) IN {x | g x * g m <= &0} /\
    (p:real^N) IN {x | f x * f q <= &0}`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY; REAL_MUL_LZERO;
                    REAL_LE_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SEGMENT_SYM]) THEN REWRITE_TAC[SEGMENT_SYM] THEN
  ASM SET_TAC[]);;

(* ========================================================================= *)
(* The kite piece.  In the kite T = conv{m,bS,bF} (m the                    *)
(* midpoint of a polygon edge, bS, bF the barycentres of the fins) with     *)
(* corner H = conv{m,p,q}, p = midpoint(m,bS), q = midpoint(m,bF), and a    *)
(* sub-segment [a,c] of an edge of T beyond the corner, the corridor piece  *)
(* is a fan of three triangles; it is a 2-cell bounded by the S side        *)
(* [m,p] + [p,a], the glue segment [a,c] and the F side [m,q] + [q,c]       *)
(* (MOI_FTP_KITE).  The plane coordinates are relative to m with the basis  *)
(* bS - m, bF - m.                                                           *)
(* ========================================================================= *)

let MOI_FTP_SQN = prove
 (`!w d. w < &0 /\ ~(d = &0) ==> w * (d * d) < &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`--w:real`; `d:real`] MOI_FTP_POS_SQ) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let MOI_FTP_PLANE_IN_TRI = prove
 (`!m bS bF:real^N x y.
     &0 <= x /\ &0 <= y /\ x + y <= &1
     ==> m + x % (bS - m) + y % (bF - m) IN convex hull {m,bS,bF}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FTC_IN_HULL3] THEN
  MAP_EVERY EXISTS_TAC [`&1 - x - y`; `x:real`; `y:real`] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN VECTOR_ARITH_TAC);;

(* The fan from p for a sub-segment [a,c] of the edge [bS,bF] or [bF,m].    *)

let MOI_FTP_KITEP = prove
 (`!v m bS bF a c xa ya xc yc.
     ~(det(vector[m - v; bS - v; bF - v:real^3]) = &0) /\
     a = m + xa % (bS - m) + ya % (bF - m) /\ c = m + xc % (bS - m) + yc % (bF - m) /\
     &0 <= xa /\ &0 <= ya /\ xa + ya <= &1 /\ &0 <= xc /\ &0 <= yc /\ xc + yc <= &1 /\
     xa < &1 /\ ya < &1 /\ xc < &1 /\ yc < &1 /\
     &1 / &2 < xa + ya /\ &1 / &2 < xc + yc /\
     ((xc - &1 / &2) * ya - (xa - &1 / &2) * yc) * (xc + yc - &1 / &2) < &0
     ==> pl_cell_with_boundary 2
           (convex hull {m,midpoint(m,bS),midpoint(m,bF)} UNION
            convex hull {midpoint(m,bS),a,c} UNION
            convex hull {midpoint(m,bS),c,midpoint(m,bF)})
           (segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a] UNION
            segment[a,c] UNION segment[c,midpoint(m,bF)] UNION segment[midpoint(m,bF),m]) /\
         convex hull {m,midpoint(m,bS),midpoint(m,bF)} UNION
         convex hull {midpoint(m,bS),a,c} UNION
         convex hull {midpoint(m,bS),c,midpoint(m,bF)} SUBSET convex hull {m,bS,bF} /\
         ~(bS IN convex hull {m,midpoint(m,bS),midpoint(m,bF)} UNION
                 convex hull {midpoint(m,bS),a,c} UNION
                 convex hull {midpoint(m,bS),c,midpoint(m,bF)}) /\
         ~(bF IN convex hull {m,midpoint(m,bS),midpoint(m,bF)} UNION
                 convex hull {midpoint(m,bS),a,c} UNION
                 convex hull {midpoint(m,bS),c,midpoint(m,bF)}) /\
         (segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a]) INTER
         segment[a,c] = {a} /\
         (segment[m,midpoint(m,bF)] UNION segment[midpoint(m,bF),c]) INTER
         segment[a,c] = {c} /\
         (segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a]) INTER
         (segment[m,midpoint(m,bF)] UNION segment[midpoint(m,bF),c]) = {m} /\
         ~(a = c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `p = midpoint(m:real^3,bS)` THEN ABBREV_TAC `q = midpoint(m:real^3,bF)` THEN
  ABBREV_TAC `D0 = det(vector[m - v; bS - v; bF - v:real^3])` THEN
  SUBGOAL_THEN
   `det(vector[p - v; c - v; a - v:real^3]) =
      ((xc - &1 / &2) * ya - (xa - &1 / &2) * yc) * D0 /\
    det(vector[p - v; c - v; q - v:real^3]) = ((xc + yc - &1 / &2) / &2) * D0 /\
    det(vector[p - v; q - v; m - v:real^3]) = (&1 / &4) * D0 /\
    det(vector[p - v; q - v; a - v:real^3]) = ((&1 - &2 * xa - &2 * ya) / &4) * D0 /\
    det(vector[p - v; q - v; c - v:real^3]) = ((&1 - &2 * xc - &2 * yc) / &4) * D0 /\
    det(vector[bF - v; m - v; m - v:real^3]) = &0 * D0 /\
    det(vector[bF - v; m - v; p - v:real^3]) = (&1 / &2) * D0 /\
    det(vector[bF - v; m - v; q - v:real^3]) = &0 * D0 /\
    det(vector[bF - v; m - v; a - v:real^3]) = xa * D0 /\
    det(vector[bF - v; m - v; c - v:real^3]) = xc * D0 /\
    det(vector[bF - v; m - v; bS - v:real^3]) = &1 * D0 /\
    det(vector[m - v; bS - v; m - v:real^3]) = &0 * D0 /\
    det(vector[m - v; bS - v; p - v:real^3]) = &0 * D0 /\
    det(vector[m - v; bS - v; q - v:real^3]) = (&1 / &2) * D0 /\
    det(vector[m - v; bS - v; a - v:real^3]) = ya * D0 /\
    det(vector[m - v; bS - v; c - v:real^3]) = yc * D0 /\
    det(vector[m - v; bS - v; bF - v:real^3]) = &1 * D0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["p"; "q"; "D0"] THEN
    REWRITE_TAC[midpoint; DET_3; VECTOR_3; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    REPEAT CONJ_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `det(vector[p - v; c - v; p - v:real^3]) = &0 /\
    det(vector[p - v; c - v; c - v:real^3]) = &0 /\
    det(vector[p - v; q - v; p - v:real^3]) = &0 /\
    det(vector[p - v; q - v; q - v:real^3]) = &0`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[MOI_FTP_DET_REP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `m IN convex hull {m:real^3,bS,bF} /\ p IN convex hull {m,bS,bF} /\
    q IN convex hull {m,bS,bF} /\ a IN convex hull {m,bS,bF} /\
    c IN convex hull {m,bS,bF}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "q"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      SUBGOAL_THEN `midpoint(m:real^3,bS) = m + (&1 / &2) % (bS - m) + &0 % (bF - m)`
      SUBST1_TAC THENL
       [REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
        MATCH_MP_TAC MOI_FTP_PLANE_IN_TRI THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `midpoint(m:real^3,bF) = m + &0 % (bS - m) + (&1 / &2) % (bF - m)`
      SUBST1_TAC THENL
       [REWRITE_TAC[midpoint] THEN VECTOR_ARITH_TAC;
        MATCH_MP_TAC MOI_FTP_PLANE_IN_TRI THEN REAL_ARITH_TAC];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FTP_PLANE_IN_TRI THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FTP_PLANE_IN_TRI THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && is_var(lhs(concl th)) && type_of(lhs(concl th)) = `:real^3`))) THEN
  MAP_EVERY (fun (e1,e2) ->
    MP_TAC(BETA_RULE(ISPECL [`v:real^3`; e1; e2] MOI_FTP_DETF_AFF)))
   [`p:real^3`,`c:real^3`; `p:real^3`,`q:real^3`] THEN
  REPEAT DISCH_TAC THEN
  (* signs *)
  SUBGOAL_THEN `&0 < &2 * xa + &2 * ya - &1 /\ &0 < &2 * xc + &2 * yc - &1`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `det(vector[p - v; c - v; a - v:real^3]) * det(vector[p - v; c - v; q - v]) < &0 /\
    det(vector[p - v; q - v; m - v:real^3]) * det(vector[p - v; q - v; a - v]) < &0 /\
    &0 < det(vector[p - v; q - v; a - v:real^3]) * det(vector[p - v; q - v; c - v])`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `(x * d) * (y * d) = (x * y) * (d * d)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTP_SQN THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_FTP_SQN THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_FTP_POS_SQ THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`&2 * xa + &2 * ya - &1`; `&2 * xc + &2 * yc - &1`] REAL_LT_MUL) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p:real^3 = c) /\ ~(p:real^3 = q)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `&0 < det(vector[p - v; q - v; a - v:real^3]) *
                       det(vector[p - v; q - v; c - v])`;
      UNDISCH_TAC `det(vector[p - v; c - v; a - v:real^3]) *
                   det(vector[p - v; c - v; q - v]) < &0`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `p:real^3`)) THEN
    REWRITE_TAC[MOI_FTP_DET_REP; REAL_MUL_RZERO; REAL_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[p - v; c - v; x - v])`; `\x:real^3. det(vector[p - v; q - v; x - v])`; `m:real^3`; `p:real^3`; `q:real^3`; `a:real^3`;
                           `c:real^3`] MOI_FTP_FAN3)) THEN
  MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[p - v; c - v; x - v])`; `\x:real^3. det(vector[p - v; q - v; x - v])`; `m:real^3`; `p:real^3`; `q:real^3`; `a:real^3`;
                           `c:real^3`] MOI_FTP_FAN3_SIDES)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `convex hull {m,p,q} UNION convex hull {p,a,c} UNION convex hull {p,c,q}
    SUBSET convex hull {m:real^3,bS,bF}`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the vertices bS and bF are not in the piece *)
  SUBGOAL_THEN `&0 < D0 * D0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_SQUARE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < (&1 - xa) * (D0 * D0) /\ &0 < (&1 - xc) * (D0 * D0) /\
    &0 < (&1 - ya) * (D0 * D0) /\ &0 < (&1 - yc) * (D0 * D0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_FTP_POS_SQ THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[bF - v; m - v; x - v]) * D0`;
                             `D0 * D0`] MOI_FTP_AFF_CONVEX));
    MP_TAC(BETA_RULE(ISPECL [`\x:real^3. det(vector[m - v; bS - v; x - v]) * D0`;
                             `D0 * D0`] MOI_FTP_AFF_CONVEX))] THEN
  (ANTS_TAC THENL [REWRITE_TAC[MOI_FTP_DETF_AFF] THEN REAL_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MATCH_MP_TAC(SET_RULE
   `!t:real^3->bool. s SUBSET t /\ ~(x IN t) ==> ~(x IN s)`) THENL
   [EXISTS_TAC `{x:real^3 | det(vector[bF - v; m - v; x - v]) * D0 < D0 * D0}`;
    EXISTS_TAC `{x:real^3 | det(vector[m - v; bS - v; x - v]) * D0 < D0 * D0}`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; REAL_MUL_LID; REAL_LT_REFL; UNION_SUBSET] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

(* The kite piece for the three positions of the glue segment [a,c] on the *)
(* edge [s,r] of the kite (s on the S side): (s,r) = (bS,bF), (bF,m) or     *)
(* (m,bS); a and c avoid the corner.  The third case is the second one with *)
(* bS and bF exchanged.                                                       *)

let MOI_FTP_KITE = prove
 (`!v m bS bF s r a c al ga.
     ~(det(vector[m - v; bS - v; bF - v:real^3]) = &0) /\
     ((s = bS /\ r = bF) \/ (s = bF /\ r = m) \/ (s = m /\ r = bS)) /\
     a = s + al % (r - s) /\ c = s + ga % (r - s) /\
     &0 < al /\ al < ga /\ ga < &1 /\
     (r = m ==> ga < &1 / &2) /\ (s = m ==> &1 / &2 < al)
     ==> ?P. pl_cell_with_boundary 2 P
               (segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a] UNION
                segment[a,c] UNION segment[c,midpoint(m,bF)] UNION
                segment[midpoint(m,bF),m]) /\
             convex hull {m,midpoint(m,bS),midpoint(m,bF)} SUBSET P /\
             P SUBSET convex hull {m,bS,bF} /\
             segment[a,c] SUBSET P /\ ~(bS IN P) /\ ~(bF IN P) /\
             (segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a]) INTER
             segment[a,c] = {a} /\
             (segment[m,midpoint(m,bF)] UNION segment[midpoint(m,bF),c]) INTER
             segment[a,c] = {c} /\
             (segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a]) INTER
             (segment[m,midpoint(m,bF)] UNION segment[midpoint(m,bF),c]) = {m} /\
             ~(a = c)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [(* (s,r) = (bS,bF) *)
    MP_TAC(ISPECL [`v:real^3`; `m:real^3`; `bS:real^3`; `bF:real^3`; `a:real^3`;
                   `c:real^3`; `&1 - al`; `al:real`; `&1 - ga`; `ga:real`] MOI_FTP_KITEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      is_eq(concl th) && is_var(lhs(concl th)) && type_of(lhs(concl th)) = `:real^3`))) THEN
    EXISTS_TAC `convex hull {m,midpoint(m,bS),midpoint(m,bF)} UNION
                convex hull {midpoint(m,bS),a,c} UNION
                convex hull {midpoint(m:real^3,bS),c,midpoint(m,bF)}` THEN
    ASM_REWRITE_TAC[SUBSET_UNION] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> s SUBSET u UNION t UNION w`) THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    (* (s,r) = (bF,m) *)
    MP_TAC(ISPECL [`v:real^3`; `m:real^3`; `bS:real^3`; `bF:real^3`; `a:real^3`;
                   `c:real^3`; `&0`; `&1 - al`; `&0`; `&1 - ga`] MOI_FTP_KITEP) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `ga < &1 / &2` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REFL_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`ga - al:real`; `&1 / &2 - ga`] REAL_LT_MUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      is_eq(concl th) && is_var(lhs(concl th)) && type_of(lhs(concl th)) = `:real^3`))) THEN
    EXISTS_TAC `convex hull {m,midpoint(m,bS),midpoint(m,bF)} UNION
                convex hull {midpoint(m,bS),a,c} UNION
                convex hull {midpoint(m:real^3,bS),c,midpoint(m,bF)}` THEN
    ASM_REWRITE_TAC[SUBSET_UNION] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> s SUBSET u UNION t UNION w`) THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    (* (s,r) = (m,bS): the mirror of the second case *)
    MP_TAC(ISPECL [`v:real^3`; `m:real^3`; `bF:real^3`; `bS:real^3`; `c:real^3`;
                   `a:real^3`; `&0`; `ga:real`; `&0`; `al:real`] MOI_FTP_KITEP) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `&1 / &2 < al` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REFL_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`ga - al:real`; `al - &1 / &2`] REAL_LT_MUL) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THENL
       [UNDISCH_TAC `~(det(vector[m - v; bS - v; bF - v:real^3]) = &0)` THEN
        REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
        VECTOR_ARITH_TAC; VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      is_eq(concl th) && is_var(lhs(concl th)) && type_of(lhs(concl th)) = `:real^3`))) THEN
    EXISTS_TAC `convex hull {m,midpoint(m,bF),midpoint(m,bS)} UNION
                convex hull {midpoint(m,bF),c,a} UNION
                convex hull {midpoint(m:real^3,bF),a,midpoint(m,bS)}` THEN
    SUBGOAL_THEN `{m:real^3,midpoint(m,bF),midpoint(m,bS)} =
                  {m,midpoint(m,bS),midpoint(m,bF)} /\ {m:real^3,bF,bS} = {m,bS,bF}`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBSET_UNION] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
      MAP_EVERY EXISTS_TAC
       [`convex hull {m,midpoint(m,bS),midpoint(m,bF)} UNION
         convex hull {midpoint(m,bF),c,a} UNION
         convex hull {midpoint(m:real^3,bF),a,midpoint(m,bS)}`;
        `segment[m,midpoint(m,bF)] UNION segment[midpoint(m,bF),c] UNION
         segment[c,a] UNION segment[a,midpoint(m,bS)] UNION
         segment[midpoint(m:real^3,bS),m]`] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> s SUBSET u UNION t UNION w`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[SEGMENT_SYM]) THEN REWRITE_TAC[SEGMENT_SYM] THEN
      ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[SEGMENT_SYM]) THEN REWRITE_TAC[SEGMENT_SYM] THEN
      ASM_REWRITE_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[SEGMENT_SYM]) THEN REWRITE_TAC[SEGMENT_SYM] THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* A chain of 2-cells P 0, ..., P n glued along segments                    *)
(* [a j, c j] = P j INTER P (SUC j), non-consecutive pieces disjoint, is a  *)
(* 2-cell; its boundary is the union of the S sides Sd j and the F sides    *)
(* Fd j of the pieces (MOI_FTP_CHAIN).  This is the corridor disk.          *)
(* ========================================================================= *)

let MOI_FTP_UNIONS_LE_0 = prove
 (`!(f:num->A->bool). UNIONS {f j | j <= 0} = f 0`,
  REWRITE_TAC[LE; EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FTP_UNIONS_LE_SUC = prove
 (`!(f:num->A->bool) k.
     UNIONS {f j | j <= SUC k} = UNIONS {f j | j <= k} UNION f(SUC k)`,
  REWRITE_TAC[LE; EXTENSION; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FTP_CHAIN = prove
 (`!(P:num->real^N->bool) Sd Fd (a:num->real^N) c n.
     1 <= n /\
     (!j. j <= n
          ==> pl_cell_with_boundary 2 (P j)
                (Sd j UNION Fd j UNION
                 (if j = 0 then {} else segment[a(j - 1),c(j - 1)]) UNION
                 (if j = n then {} else segment[a j,c j]))) /\
     (!j. j < n ==> P j INTER P(SUC j) = segment[a j,c j] /\ ~(a j = c j)) /\
     (!i j. SUC i < j /\ j <= n ==> P i INTER P j = {}) /\
     (!j. j <= n ==> Sd j SUBSET P j /\ Fd j SUBSET P j) /\
     (!j. j < n ==> Sd j INTER segment[a j,c j] = {a j} /\
                    Fd j INTER segment[a j,c j] = {c j} /\
                    Sd(SUC j) INTER segment[a j,c j] = {a j} /\
                    Fd(SUC j) INTER segment[a j,c j] = {c j})
     ==> pl_cell_with_boundary 2 (UNIONS {P j | j <= n})
           (UNIONS {Sd j | j <= n} UNION UNIONS {Fd j | j <= n})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cell")
    (CONJUNCTS_THEN2 (LABEL_TAC "glue") (CONJUNCTS_THEN2 (LABEL_TAC "disj")
    (CONJUNCTS_THEN2 (LABEL_TAC "sub") (LABEL_TAC "ends")))))) THEN
  SUBGOAL_THEN
   `!k. k <= n
        ==> pl_cell_with_boundary 2 (UNIONS {P j | j <= k:num})
              (UNIONS {Sd j | j <= k:num} UNION UNIONS {Fd j | j <= k:num} UNION
               (if k = n then {} else segment[(a:num->real^N) k,c k]))`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL; UNION_EMPTY]] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[MOI_FTP_UNIONS_LE_0] THEN
    USE_THEN "cell" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0; UNION_EMPTY] THEN
    REWRITE_TAC[UNION_ASSOC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(k:num) < n /\ k <= n /\ ~(k = n)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `SUC k <= n` THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  USE_THEN "glue" (fun th -> MP_TAC(MATCH_MP th (ASSUME `k:num < n`))) THEN
  STRIP_TAC THEN
  USE_THEN "ends" (fun th -> MP_TAC(MATCH_MP th (ASSUME `k:num < n`))) THEN
  STRIP_TAC THEN
  USE_THEN "cell" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC k <= n`))) THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN DISCH_TAC THEN
  (* the earlier pieces meet P(SUC k) only in the glue segment *)
  SUBGOAL_THEN `UNIONS {P j | j <= k:num} INTER P(SUC k) = segment[(a:num->real^N) k,c k]`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[UNIONS_GSPEC; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      ASM_CASES_TAC `i:num = k` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC `P k INTER P(SUC k) = segment[(a:num->real^N) k,c k]` THEN
        REWRITE_TAC[EXTENSION; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
        ASM_REWRITE_TAC[];
        USE_THEN "disj" (MP_TAC o SPECL [`i:num`; `SUC k`]) THEN
        ANTS_TAC THENL
         [UNDISCH_TAC `i <= k:num` THEN UNDISCH_TAC `~(i:num = k)` THEN
          UNDISCH_TAC `SUC k <= n` THEN ARITH_TAC;
          REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[]]];
      DISCH_TAC THEN
      UNDISCH_TAC `P k INTER P(SUC k) = segment[(a:num->real^N) k,c k]` THEN
      REWRITE_TAC[EXTENSION; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS {P j | j <= k:num}:real^N->bool`;
                 `UNIONS {Sd j | j <= k:num} UNION UNIONS {Fd j | j <= k:num} UNION
                  segment[(a:num->real^N) k,c k]`;
                 `(P:num->real^N->bool)(SUC k)`;
                 `Sd(SUC k) UNION Fd(SUC k) UNION segment[(a:num->real^N) k,c k] UNION
                  (if SUC k = n then {} else segment[a(SUC k),c(SUC k)])`;
                 `(a:num->real^N) k`; `(c:num->real^N) k`] MOI_FTC_GLUE_SEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[MOI_FTP_UNIONS_LE_SUC] THEN
  MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
  EXISTS_TAC `UNIONS {P j | j <= k:num} UNION (P:num->real^N->bool)(SUC k)` THEN
  EXISTS_TAC
   `((UNIONS {Sd j | j <= k:num} UNION UNIONS {Fd j | j <= k:num} UNION
      segment[(a:num->real^N) k,c k]) UNION
     (Sd(SUC k) UNION Fd(SUC k) UNION segment[a k,c k] UNION
      (if SUC k = n then {} else segment[a(SUC k),c(SUC k)]))) DIFF
    (segment[a k,c k] DIFF {a k,c k})` THEN
  ASM_REWRITE_TAC[] THEN
  (* the boundary bookkeeping *)
  SUBGOAL_THEN
   `!j. j <= k ==> (Sd j UNION Fd j) INTER segment[(a:num->real^N) k,c k] SUBSET {a k,c k}`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j:num = k` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `(Sd:num->real^N->bool) k INTER segment[a k,c k] = {a k}` THEN
      UNDISCH_TAC `(Fd:num->real^N->bool) k INTER segment[a k,c k] = {c k}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "disj" (MP_TAC o SPECL [`j:num`; `SUC k`]) THEN
    USE_THEN "sub" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `j <= k:num` THEN UNDISCH_TAC `k:num < n` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN ANTS_TAC THENL
     [UNDISCH_TAC `j <= k:num` THEN UNDISCH_TAC `~(j:num = k)` THEN
      UNDISCH_TAC `SUC k <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `(Sd:num->real^N->bool) j SUBSET P j /\ Fd j SUBSET P j` THEN
    UNDISCH_TAC `P k INTER P(SUC k) = segment[(a:num->real^N) k,c k]` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(if SUC k = n then {} else segment[(a:num->real^N)(SUC k),c(SUC k)]) INTER
    segment[a k,c k] = {}`
  ASSUME_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[INTER_EMPTY] THEN
    SUBGOAL_THEN `SUC k < n` ASSUME_TAC THENL
     [UNDISCH_TAC `SUC k <= n` THEN UNDISCH_TAC `~(SUC k = n)` THEN ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "glue" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC k < n`))) THEN
    USE_THEN "disj" (MP_TAC o SPECL [`k:num`; `SUC(SUC k)`]) THEN
    ANTS_TAC THENL [UNDISCH_TAC `SUC k < n` THEN ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `P k INTER P(SUC k) = segment[(a:num->real^N) k,c k]` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {Sd j | j <= k:num} INTER segment[(a:num->real^N) k,c k] SUBSET {a k,c k} /\
    UNIONS {Fd j | j <= k:num} INTER segment[(a:num->real^N) k,c k] SUBSET {a k,c k} /\
    a k IN UNIONS {Sd j | j <= k:num} /\ c k IN UNIONS {Fd j | j <= k:num}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `{(a:num->real^N) k,c k}`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_UNION] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `{(a:num->real^N) k,c k}`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_INTER; IN_UNION] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `k:num` THEN REWRITE_TAC[LE_REFL] THEN
      UNDISCH_TAC `(Sd:num->real^N->bool) k INTER segment[a k,c k] = {a k}` THEN
      SET_TAC[];
      EXISTS_TAC `k:num` THEN REWRITE_TAC[LE_REFL] THEN
      UNDISCH_TAC `(Fd:num->real^N->bool) k INTER segment[a k,c k] = {c k}` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`UNIONS {Sd j | j <= k:num} INTER segment[(a:num->real^N) k,c k] SUBSET {a k,c k}`;
    `UNIONS {Fd j | j <= k:num} INTER segment[(a:num->real^N) k,c k] SUBSET {a k,c k}`;
    `(a:num->real^N) k IN UNIONS {Sd j | j <= k:num}`;
    `(c:num->real^N) k IN UNIONS {Fd j | j <= k:num}`;
    `(if SUC k = n then {} else segment[(a:num->real^N)(SUC k),c(SUC k)]) INTER
     segment[a k,c k] = {}`;
    `(Sd:num->real^N->bool)(SUC k) INTER segment[a k,c k] = {a k}`;
    `(Fd:num->real^N->bool)(SUC k) INTER segment[a k,c k] = {c k}`] THEN
  SET_TAC[]);;

(* The S sides and the F sides of a chain meet only at the two ends. *)

let MOI_FTP_CHAIN_ARCS = prove
 (`!(P:num->real^N->bool) Sd Fd (a:num->real^N) c n m1 m2.
     1 <= n /\
     (!j. j < n ==> P j INTER P(SUC j) = segment[a j,c j] /\ ~(a j = c j)) /\
     (!i j. SUC i < j /\ j <= n ==> P i INTER P j = {}) /\
     (!j. j <= n ==> Sd j SUBSET P j /\ Fd j SUBSET P j) /\
     (!j. j < n ==> Sd j INTER segment[a j,c j] = {a j} /\
                    Fd j INTER segment[a j,c j] = {c j} /\
                    Sd(SUC j) INTER segment[a j,c j] = {a j} /\
                    Fd(SUC j) INTER segment[a j,c j] = {c j}) /\
     Sd 0 INTER Fd 0 = {m1} /\ Sd n INTER Fd n = {m2} /\
     (!j. 0 < j /\ j < n ==> Sd j INTER Fd j = {})
     ==> UNIONS {Sd j | j <= n} INTER UNIONS {Fd j | j <= n} = {m1,m2}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "glue")
    (CONJUNCTS_THEN2 (LABEL_TAC "disj") (CONJUNCTS_THEN2 (LABEL_TAC "sub")
    (CONJUNCTS_THEN2 (LABEL_TAC "ends") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mid")))))))) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_INTER; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
    DISJ_CASES_TAC(ARITH_RULE `i:num = j \/ SUC i < j \/ SUC j < i \/ j = SUC i \/ i = SUC j`)
    THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_CASES_TAC `j = 0` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC `(Sd:num->real^N->bool) 0 INTER Fd 0 = {m1}` THEN ASM SET_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `j:num = n` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        UNDISCH_TAC `(Sd:num->real^N->bool) n INTER Fd n = {m2}` THEN ASM SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "mid" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~(j = 0)`; `~(j:num = n)`; `j <= n:num`] THEN ARITH_TAC;
        ASM SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THENL
     [USE_THEN "disj" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      USE_THEN "sub" (MP_TAC o SPEC `i:num`) THEN USE_THEN "sub" (MP_TAC o SPEC `j:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THENL
     [USE_THEN "disj" (MP_TAC o SPECL [`j:num`; `i:num`]) THEN
      USE_THEN "sub" (MP_TAC o SPEC `i:num`) THEN USE_THEN "sub" (MP_TAC o SPEC `j:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
       [UNDISCH_TAC `SUC i <= n` THEN ARITH_TAC; ALL_TAC] THEN
      USE_THEN "glue" (MP_TAC o SPEC `i:num`) THEN USE_THEN "ends" (MP_TAC o SPEC `i:num`) THEN
      USE_THEN "sub" (MP_TAC o SPEC `i:num`) THEN USE_THEN "sub" (MP_TAC o SPEC `SUC i`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `i <= n:num` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `i:num < n` THEN ARITH_TAC; ALL_TAC] THEN
      ASM SET_TAC[];
      SUBGOAL_THEN `j:num < n` ASSUME_TAC THENL
       [UNDISCH_TAC `SUC j <= n` THEN ARITH_TAC; ALL_TAC] THEN
      USE_THEN "glue" (MP_TAC o SPEC `j:num`) THEN USE_THEN "ends" (MP_TAC o SPEC `j:num`) THEN
      USE_THEN "sub" (MP_TAC o SPEC `j:num`) THEN USE_THEN "sub" (MP_TAC o SPEC `SUC j`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `j <= n:num` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `j:num < n` THEN ARITH_TAC; ALL_TAC] THEN
      ASM SET_TAC[]];
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [CONJ_TAC THEN EXISTS_TAC `0` THEN REWRITE_TAC[LE_0] THEN
      UNDISCH_TAC `(Sd:num->real^N->bool) 0 INTER Fd 0 = {m1}` THEN SET_TAC[];
      CONJ_TAC THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[LE_REFL] THEN
      UNDISCH_TAC `(Sd:num->real^N->bool) n INTER Fd n = {m2}` THEN SET_TAC[]]]);;

(* ========================================================================= *)
(* Dual path data for the corridor.  Shortest dual paths have               *)
(* no repeated triangle and no shortcut (MOI_FTP_DPATH_SHORT); the          *)
(* triangles along a labelled path (MOI_FTP_PATH_TRIS); the vertex sets of  *)
(* a simplex; cyclic orders from determinant signs (MOI_FTP_PERM_ROT); the  *)
(* glue sub-segment [moi_ftp_sa, moi_ftp_sc] of a crossed edge, placed by   *)
(* the weights of its ends (1 at the polygon midpoints W) so that it        *)
(* avoids the dual disks.                                                    *)
(* ========================================================================= *)

let MOI_FTP_DPATH_SHORT = prove
 (`!(L:(real^N->bool)->bool) A B.
     FINITE L /\ combinatorial_manifold_with_boundary 2 L /\ connected (UNIONS L) /\
     A IN L /\ aff_dim A = &2 /\ B IN L /\ aff_dim B = &2
     ==> ?n P. moi_ftp_dpath L P n /\ P 0 = A /\ P n = B /\
               (!i j. i <= n /\ j <= n /\ P i = P j ==> i = j) /\
               (!i j. SUC i < j /\ j <= n ==> ~(aff_dim(P i INTER P j) = &1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FTP_DPATH_EXISTS) THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `P0:num->real^N->bool` STRIP_ASSUME_TAC) (LABEL_TAC "min"))) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `n:num`; `P0:num->real^N->bool`]
    MOI_FTP_DPATH_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `P:num->real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `m:num = n` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM LE_ANTISYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    USE_THEN "min" (MP_TAC o SPEC `m:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN EXISTS_TAC `P:num->real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `P:num->real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN DISCH_TAC THEN
  USE_THEN "min" (MP_TAC o SPEC `n - (j - SUC i)`) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`SUC i < j`; `j:num <= n`] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  EXISTS_TAC `\k. if k <= i then (P:num->real^N->bool) k else P(k + (j - SUC i))` THEN
  BETA_TAC THEN REWRITE_TAC[LE_0] THEN
  SUBGOAL_THEN `~(n - (j - SUC i) <= i) /\ n - (j - SUC i) + (j - SUC i) = n`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC [`SUC i < j`; `j:num <= n`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_ftp_dpath L (P:num->real^N->bool) n` THEN
  REWRITE_TAC[moi_ftp_dpath] THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`k <= n - (j - SUC i)`; `SUC i < j`; `j:num <= n`] THEN
    ARITH_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `k:num < i` THENL
     [SUBGOAL_THEN `k <= i /\ SUC k <= i` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `k:num < i` THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `&1:int`)) (concl th))) THEN
      MAP_EVERY UNDISCH_TAC [`k:num < i`; `SUC i < j`; `j:num <= n`] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `k:num = i` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[LE_REFL; ARITH_RULE `~(SUC k <= k)`] THEN
      SUBGOAL_THEN `SUC i + j - SUC i = j` SUBST1_TAC THENL
       [UNDISCH_TAC `SUC i < j` THEN ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(k <= i) /\ ~(SUC k <= i) /\
                  SUC k + j - SUC i = SUC(k + j - SUC i)`
    (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC [`~(k:num < i)`; `~(k:num = i)`; `SUC i < j`] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `&1:int`)) (concl th))) THEN
    MAP_EVERY UNDISCH_TAC [`k < n - (j - SUC i)`; `SUC i < j`; `j:num <= n`] THEN
    ARITH_TAC]);;

(* Affinely independent sets with the same convex hull are equal. *)

let MOI_FTP_AFF_VERTS_EQ = prove
 (`!s t:real^N->bool.
     ~affine_dependent s /\ ~affine_dependent t /\ convex hull s = convex hull t
     ==> s = t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
    EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `x:real^N`]
    EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* The triangles along a labelled injective dual path. *)

let MOI_FTP_PATH_TRIS = prove
 (`!(L:(real^N->bool)->bool) P n s0 r0.
     FINITE L /\ lf_simplicial_complex L /\ combinatorial_manifold 2 L /\
     moi_ftp_dpath L P n /\ (!i k. i <= n /\ k <= n /\ P i = P k ==> i = k) /\
     P 0 INTER P(SUC 0) = segment[s0,r0] /\ ~(s0 = r0)
     ==> !j. j < n
             ==> P j INTER P(SUC j) = segment[moi_ftp_s P s0 r0 j, moi_ftp_r P s0 r0 j] /\
                 P j = convex hull {moi_ftp_s P s0 r0 j, moi_ftp_r P s0 r0 j,
                                    moi_ftp_y P s0 r0 j} /\
                 ~affine_dependent {moi_ftp_s P s0 r0 j, moi_ftp_r P s0 r0 j,
                                    moi_ftp_y P s0 r0 j} /\
                 P(SUC j) = convex hull {moi_ftp_s P s0 r0 j, moi_ftp_r P s0 r0 j,
                                         moi_ftp_z P s0 r0 j} /\
                 ~affine_dependent {moi_ftp_s P s0 r0 j, moi_ftp_r P s0 r0 j,
                                    moi_ftp_z P s0 r0 j} /\
                 ~(moi_ftp_s P s0 r0 j = moi_ftp_r P s0 r0 j) /\
                 ~(moi_ftp_s P s0 r0 j = moi_ftp_y P s0 r0 j) /\
                 ~(moi_ftp_r P s0 r0 j = moi_ftp_y P s0 r0 j) /\
                 ~(moi_ftp_s P s0 r0 j = moi_ftp_z P s0 r0 j) /\
                 ~(moi_ftp_r P s0 r0 j = moi_ftp_z P s0 r0 j) /\
                 ~(moi_ftp_y P s0 r0 j = moi_ftp_z P s0 r0 j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `P:num->real^N->bool`; `n:num`;
                 `s0:real^N`; `r0:real^N`] MOI_FTP_LABELS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_ftp_dpath L (P:num->real^N->bool) n` THEN
  REWRITE_TAC[moi_ftp_dpath] THEN STRIP_TAC THEN
  SUBGOAL_THEN `j <= n /\ SUC j <= n` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `j:num < n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(P:num->real^N->bool) j IN L /\ aff_dim(P j) = &2 /\
    P(SUC j) IN L /\ aff_dim(P(SUC j)) = &2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[moi_ftp_s P s0 r0 j,moi_ftp_r P s0 r0 j] face_of (P:num->real^N->bool) j /\
    segment[moi_ftp_s P s0 r0 j,moi_ftp_r P s0 r0 j] face_of P(SUC j)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhand(concl th) = `(P:num->real^N->bool) j INTER P(SUC j)`)) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    DISCH_THEN(MP_TAC o SPECL [`(P:num->real^N->bool) j`; `(P:num->real^N->bool)(SUC j)`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `(P:num->real^N->bool) j`;
                 `moi_ftp_s (P:num->real^N->bool) s0 r0 j`;
                 `moi_ftp_r (P:num->real^N->bool) s0 r0 j`] MOI_FTP_EDGE_VERTS) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `(P:num->real^N->bool)(SUC j)`;
                 `moi_ftp_s (P:num->real^N->bool) s0 r0 j`;
                 `moi_ftp_r (P:num->real^N->bool) s0 r0 j`] MOI_FTP_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[GSYM moi_ftp_y; GSYM moi_ftp_z] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `y:real^N = moi_ftp_y P s0 r0 j /\ z = moi_ftp_z P s0 r0 j`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `P:num->real^N->bool`; `n:num`; `j:num`]
                MOI_FTP_DPATH_NEQ) THEN
  ASM_REWRITE_TAC[moi_ftp_dpath]);;

(* Cyclic orders.  A permutation (x,y,z) of three points a, b, c (apex      *)
(* determinant D) with D(x,y,z) D(a,b,c) > 0 is a cyclic rotation.          *)

let MOI_FTP_DET_CYC = prove
 (`!v a b c:real^3.
     det(vector[b - v; c - v; a - v]) = det(vector[a - v; b - v; c - v]) /\
     det(vector[c - v; a - v; b - v]) = det(vector[a - v; b - v; c - v]) /\
     det(vector[b - v; a - v; c - v]) = --det(vector[a - v; b - v; c - v]) /\
     det(vector[a - v; c - v; b - v]) = --det(vector[a - v; b - v; c - v]) /\
     det(vector[c - v; b - v; a - v]) = --det(vector[a - v; b - v; c - v])`,
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_RING);;

let MOI_FTP_PERM_ROT = prove
 (`!v a b c x y z:real^3.
     {x,y,z} = {a,b,c} /\ ~(x = y) /\ ~(x = z) /\ ~(y = z) /\
     &0 < det(vector[x - v; y - v; z - v]) * det(vector[a - v; b - v; c - v])
     ==> (x = a /\ y = b /\ z = c) \/ (x = b /\ y = c /\ z = a) \/
         (x = c /\ y = a /\ z = b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `x IN {a:real^3,b,c} /\ y IN {a,b,c} /\ z IN {a,b,c}` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `{x:real^3,y,z}`)) THEN
    REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  UNDISCH_TAC `&0 < det(vector[x - v; y - v; z - v:real^3]) *
                    det(vector[a - v; b - v; c - v])` THEN
  MAP_EVERY UNDISCH_TAC [`~(x:real^3 = y)`; `~(x:real^3 = z)`; `~(y:real^3 = z)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(fun th ->
    REPEAT_TCL CONJUNCTS_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) th) THEN
  REWRITE_TAC[] THEN
  TRY(FIRST_X_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[] THEN NO_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    fst(strip_comb(concl th)) = `(<):real->real->bool`)) THEN
  MP_TAC(ISPECL [`v:real^3`; `a:real^3`; `b:real^3`; `c:real^3`] MOI_FTP_DET_CYC) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
  MP_TAC(SPEC `det(vector[a - v; b - v; c - v:real^3])` REAL_LE_SQUARE) THEN
  REAL_ARITH_TAC);;

(* The glue sub-segment of an edge [s,r]: weights 1 on W shift it away from *)
(* the end in W (at most one end is in W).                                   *)

let moi_ftp_w = new_definition
 `moi_ftp_w (W:real^N->bool) x = if x IN W then &1 else &0`;;

let moi_ftp_lam = new_definition
 `moi_ftp_lam (W:real^N->bool) s r = &1 / &2 + (moi_ftp_w W s - moi_ftp_w W r) / &4`;;

let moi_ftp_sa = new_definition
 `moi_ftp_sa (W:real^N->bool) s r = s + (moi_ftp_lam W s r - &1 / &8) % (r - s)`;;

let moi_ftp_sc = new_definition
 `moi_ftp_sc (W:real^N->bool) s r = s + (moi_ftp_lam W s r + &1 / &8) % (r - s)`;;

let MOI_FTP_SUBSEG = prove
 (`!(W:real^N->bool) s r.
     ~(s IN W /\ r IN W)
     ==> &0 < moi_ftp_lam W s r - &1 / &8 /\
         moi_ftp_lam W s r - &1 / &8 < moi_ftp_lam W s r + &1 / &8 /\
         moi_ftp_lam W s r + &1 / &8 < &1 /\
         (r IN W ==> moi_ftp_lam W s r + &1 / &8 < &1 / &2) /\
         (s IN W ==> &1 / &2 < moi_ftp_lam W s r - &1 / &8) /\
         &1 - (moi_ftp_lam W s r - &1 / &8) = moi_ftp_lam W r s + &1 / &8 /\
         &1 - (moi_ftp_lam W s r + &1 / &8) = moi_ftp_lam W r s - &1 / &8 /\
         moi_ftp_sa W s r = r + (&1 - (moi_ftp_lam W s r - &1 / &8)) % (s - r) /\
         moi_ftp_sc W s r = r + (&1 - (moi_ftp_lam W s r + &1 / &8)) % (s - r) /\
         moi_ftp_sa W s r = moi_ftp_sc W r s /\ moi_ftp_sc W s r = moi_ftp_sa W r s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_ftp_sa; moi_ftp_sc; moi_ftp_lam; moi_ftp_w] THEN
  ASM_CASES_TAC `(s:real^N) IN W` THEN ASM_CASES_TAC `(r:real^N) IN W` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) THEN
  VECTOR_ARITH_TAC);;

(* An affine function equal to the weights at s and r stays below 1/2 on    *)
(* the glue points.                                                          *)

let MOI_FTP_SUBSEG_LEVEL = prove
 (`!(W:real^N->bool) f s r.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     ~(s IN W /\ r IN W) /\ f s = moi_ftp_w W s /\ f r = moi_ftp_w W r
     ==> f(moi_ftp_sa W s r) < &1 / &2 /\ f(moi_ftp_sc W s r) < &1 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!t. (s:real^N) + t % (r - s) = (&1 - t) % s + t % r`
  (fun th -> REWRITE_TAC[moi_ftp_sa; moi_ftp_sc; th]) THENL
   [GEN_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_ftp_lam; moi_ftp_w] THEN
  UNDISCH_TAC `~((s:real^N) IN W /\ r IN W)` THEN
  ASM_CASES_TAC `(s:real^N) IN W` THEN ASM_CASES_TAC `(r:real^N) IN W` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ========================================================================= *)
(* The corridor path.  In the link of the apex v, a shortest                *)
(* dual path from the start kite conv{m1,bS,bF} to the end kite             *)
(* conv{m2,bS',bF'} (not adjacent), labelled so that the first crossed edge *)
(* (s0,r0) with the vertex behind it is a cyclic rotation of (bS,bF,m1).    *)
(* The J-invariant (MOI_FTP_PATH_J, MOI_FTP_JEND) and the sign at the end   *)
(* kite force the last crossed edge with the vertex beyond it to be a       *)
(* cyclic rotation of (bS',bF',m2): the S side ends on the S radius.        *)
(* ========================================================================= *)

let MOI_FTP_TRI_AFF_DIM = prove
 (`!a b c:real^N.
     ~affine_dependent {a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c)
     ==> aff_dim(convex hull {a,b,c}) = &2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV);;

let MOI_FTP_CORR_PATH = prove
 (`!(c:(real^3->bool)->bool) v m1 bS bF m2 bS' bF'.
     lf_simplicial_complex c /\ {v} IN c /\
     FINITE (simplicial_link c v) /\ combinatorial_manifold 2 (simplicial_link c v) /\
     combinatorial_manifold_with_boundary 2 (simplicial_link c v) /\
     connected (UNIONS (simplicial_link c v)) /\
     convex hull {m1,bS,bF} IN simplicial_link c v /\ ~affine_dependent {m1,bS,bF} /\
     convex hull {m2,bS',bF'} IN simplicial_link c v /\ ~affine_dependent {m2,bS',bF'} /\
     ~(m1 = bS) /\ ~(m1 = bF) /\ ~(bS = bF) /\ ~(m2 = bS') /\ ~(m2 = bF') /\ ~(bS' = bF') /\
     ~(convex hull {m1,bS,bF} = convex hull {m2,bS',bF'}) /\
     ~(aff_dim(convex hull {m1,bS,bF} INTER convex hull {m2,bS',bF'}) = &1) /\
     &0 < det(vector[bS - v; bF - v; m1 - v]) /\ det(vector[bS' - v; bF' - v; m2 - v]) < &0
     ==> ?n P s0 r0.
           2 <= n /\ moi_ftp_dpath (simplicial_link c v) P n /\
           P 0 = convex hull {m1,bS,bF} /\ P n = convex hull {m2,bS',bF'} /\
           (!i j. i <= n /\ j <= n /\ P i = P j ==> i = j) /\
           (!i j. SUC i < j /\ j <= n ==> ~(aff_dim(P i INTER P j) = &1)) /\
           P 0 INTER P(SUC 0) = segment[s0,r0] /\ ~(s0 = r0) /\
           ((s0 = bS /\ r0 = bF /\ moi_ftp_y P s0 r0 0 = m1) \/
            (s0 = bF /\ r0 = m1 /\ moi_ftp_y P s0 r0 0 = bS) \/
            (s0 = m1 /\ r0 = bS /\ moi_ftp_y P s0 r0 0 = bF)) /\
           ((moi_ftp_s P s0 r0 (n - 1) = bS' /\ moi_ftp_r P s0 r0 (n - 1) = bF' /\
             moi_ftp_z P s0 r0 (n - 1) = m2) \/
            (moi_ftp_s P s0 r0 (n - 1) = bF' /\ moi_ftp_r P s0 r0 (n - 1) = m2 /\
             moi_ftp_z P s0 r0 (n - 1) = bS') \/
            (moi_ftp_s P s0 r0 (n - 1) = m2 /\ moi_ftp_r P s0 r0 (n - 1) = bS' /\
             moi_ftp_z P s0 r0 (n - 1) = bF'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = simplicial_link c (v:real^3)` THEN
  SUBGOAL_THEN `lf_simplicial_complex (L:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN ASM_SIMP_TAC[MOI_FTA_LINK_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(convex hull {m1:real^3,bS,bF}) = &2 /\
                aff_dim(convex hull {m2:real^3,bS',bF'}) = &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FTP_TRI_AFF_DIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `convex hull {m1:real^3,bS,bF}`;
                 `convex hull {m2:real^3,bS',bF'}`] MOI_FTP_DPATH_SHORT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `P:num->real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `2 <= n` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n = 0) /\ ~(n = 1)`] THEN CONJ_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THENL
     [UNDISCH_TAC `~(convex hull {m1:real^3,bS,bF} = convex hull {m2,bS',bF'})` THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `moi_ftp_dpath L (P:num->real^3->bool) 1` THEN
      REWRITE_TAC[moi_ftp_dpath] THEN DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT2) THEN
      REWRITE_TAC[ARITH_RULE `0 < 1`; ARITH_RULE `SUC 0 = 1`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the first crossed edge is an edge of the start kite *)
  SUBGOAL_THEN
   `(P:num->real^3->bool) 0 IN L /\ P(SUC 0) IN L /\ aff_dim(P 0 INTER P(SUC 0)) = &1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_ftp_dpath L (P:num->real^3->bool) n` THEN
    REWRITE_TAC[moi_ftp_dpath] THEN STRIP_TAC THEN
    SUBGOAL_THEN `0 <= n /\ SUC 0 <= n /\ 0 < n` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:num->real^3->bool) 0 INTER P(SUC 0) face_of P 0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
                GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    DISCH_THEN(MP_TAC o SPECL [`(P:num->real^3->bool) 0`; `(P:num->real^3->bool)(SUC 0)`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m1:real^3`; `bS:real^3`; `bF:real^3`;
                 `(P:num->real^3->bool) 0 INTER P(SUC 0)`] MOI_FTP_EDGE_OF_TRI) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(P:num->real^3->bool) 0 INTER P(SUC 0) face_of P 0` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`convex hull {m1:real^3,bS,bF}`; `m1:real^3`; `bS:real^3`; `bF:real^3`]
    MOI_FTP_THIRD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?s0 r0. P 0 INTER P(SUC 0) = segment[s0:real^3,r0] /\ ~(s0 = r0) /\
            ((s0 = bS /\ r0 = bF /\ moi_ftp_y P s0 r0 0 = m1) \/
             (s0 = bF /\ r0 = m1 /\ moi_ftp_y P s0 r0 0 = bS) \/
             (s0 = m1 /\ r0 = bS /\ moi_ftp_y P s0 r0 0 = bF))`
  MP_TAC THENL
   [REWRITE_TAC[moi_ftp_y; MOI_FTP_LAB_SUC] THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (fun th ->
      is_disj(concl th) && can (find_term ((=) `segment[m1:real^3,bS]`)) (concl th))) THENL
     [MAP_EVERY EXISTS_TAC [`m1:real^3`; `bS:real^3`];
      MAP_EVERY EXISTS_TAC [`bF:real^3`; `m1:real^3`] THEN ONCE_REWRITE_TAC[SEGMENT_SYM];
      MAP_EVERY EXISTS_TAC [`bS:real^3`; `bF:real^3`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^3` (X_CHOOSE_THEN `r0:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `P:num->real^3->bool`; `s0:real^3`; `r0:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the end: J-invariant and the sign at the end kite *)
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `P:num->real^3->bool`; `n:num`;
                 `s0:real^3`; `r0:real^3`] MOI_FTP_PATH_J) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `P:num->real^3->bool`; `n:num`;
                 `s0:real^3`; `r0:real^3`] MOI_FTP_PATH_TRIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n - 1`) THEN
  SUBGOAL_THEN `n - 1 < n /\ SUC(n - 1) = n` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^3`; `moi_ftp_s (P:num->real^3->bool) s0 r0`;
                 `moi_ftp_r (P:num->real^3->bool) s0 r0`;
                 `moi_ftp_y (P:num->real^3->bool) s0 r0`;
                 `moi_ftp_z (P:num->real^3->bool) s0 r0`; `n - 1`] MOI_FTP_JEND) THEN
  SUBGOAL_THEN `SUC(n - 1) = n` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_FTP_LAB_SUC] THEN
    MP_TAC(ISPECL [`v:real^3`; `bS:real^3`; `bF:real^3`; `m1:real^3`] MOI_FTP_DET_CYC) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th ->
      is_disj(concl th) && can (find_term ((=) `s0:real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`v:real^3`; `bS:real^3`; `bF:real^3`; `m1:real^3`] MOI_FTP_DET_CYC) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`{moi_ftp_s P s0 r0 (n - 1), moi_ftp_r P s0 r0 (n - 1),
                   moi_ftp_z (P:num->real^3->bool) s0 r0 (n - 1)}`;
                 `{m2:real^3,bS',bF'}`] MOI_FTP_AFF_VERTS_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun t -> UNDISCH_TAC t)
     [`(P:num->real^3->bool) n = convex hull {m2,bS',bF'}`;
      `(P:num->real^3->bool) n =
       convex hull {moi_ftp_s P s0 r0 (n - 1), moi_ftp_r P s0 r0 (n - 1),
                    moi_ftp_z P s0 r0 (n - 1)}`] THEN
    MESON_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC MOI_FTP_PERM_ROT THEN EXISTS_TAC `v:real^3` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_POS_LT] THEN DISJ2_TAC THEN ASM_REWRITE_TAC[]);;

(* The trapezoid piece of the corridor in the triangle conv{s,r,z} entered  *)
(* through [s,r] and left through [s',r'] = [s,z] (S vertex kept) or [z,r]  *)
(* (F vertex kept), between the glue sub-segments of the two edges.         *)

let MOI_FTP_TRAP = prove
 (`!v (W:real^3->bool) s r z s' r' a c a' c'.
     ~(det(vector[s - v; r - v; z - v]) = &0) /\
     ((s' = s /\ r' = z) \/ (s' = z /\ r' = r)) /\
     ~(s IN W /\ r IN W) /\ ~(s' IN W /\ r' IN W) /\
     a = moi_ftp_sa W s r /\ c = moi_ftp_sc W s r /\
     a' = moi_ftp_sa W s' r' /\ c' = moi_ftp_sc W s' r'
     ==> pl_cell_with_boundary 2 (convex hull {a,c,c'} UNION convex hull {a,c',a'})
           (segment[a,c] UNION segment[c,c'] UNION segment[c',a'] UNION segment[a',a]) /\
         convex hull {a,c,c'} UNION convex hull {a,c',a'} SUBSET convex hull {s,r,z} /\
         (convex hull {a,c,c'} UNION convex hull {a,c',a'}) INTER segment[s,r] =
         segment[a,c] /\
         (convex hull {a,c,c'} UNION convex hull {a,c',a'}) INTER segment[s',r'] =
         segment[a',c'] /\
         ~(s IN convex hull {a,c,c'} UNION convex hull {a,c',a'}) /\
         ~(r IN convex hull {a,c,c'} UNION convex hull {a,c',a'}) /\
         ~(z IN convex hull {a,c,c'} UNION convex hull {a,c',a'}) /\
         segment[a,a'] INTER segment[c,c'] = {} /\
         segment[a,a'] INTER segment[a,c] = {a} /\
         segment[a,a'] INTER segment[a',c'] = {a'} /\
         segment[c,c'] INTER segment[a,c] = {c} /\
         segment[c,c'] INTER segment[a',c'] = {c'} /\
         ~(a = c) /\ ~(a' = c') /\
         (!f. (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
              f s = moi_ftp_w W s /\ f r = moi_ftp_w W r /\ f z = moi_ftp_w W z
              ==> convex hull {a,c,c'} UNION convex hull {a,c',a'} SUBSET
                  {x | f x < &1 / &2})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  MAP_EVERY (fun t -> FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = t))) [`a:real^3`; `c:real^3`; `a':real^3`; `c':real^3`] THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `s:real^3`; `r:real^3`] MOI_FTP_SUBSEG) THEN
  MP_TAC(ISPECL [`W:real^3->bool`; `s':real^3`; `r':real^3`] MOI_FTP_SUBSEG) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  (* the level part, common to both cases *)
  SUBGOAL_THEN
   `!f. (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
        f s = moi_ftp_w W s /\ f r = moi_ftp_w W r /\ f z = moi_ftp_w W z
        ==> convex hull {moi_ftp_sa W s r,moi_ftp_sc W s r,moi_ftp_sc W s' r'} UNION
            convex hull {moi_ftp_sa W s r,moi_ftp_sc W s' r',moi_ftp_sa W s' r'} SUBSET
            {x:real^3 | f x < &1 / &2}`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`W:real^3->bool`; `f:real^3->real`; `s:real^3`; `r:real^3`]
      MOI_FTP_SUBSEG_LEVEL) THEN
    MP_TAC(ISPECL [`W:real^3->bool`; `f:real^3->real`; `s':real^3`; `r':real^3`]
      MOI_FTP_SUBSEG_LEVEL) THEN
    SUBGOAL_THEN `f(s':real^3) = moi_ftp_w W s' /\ f(r':real^3) = moi_ftp_w W r'`
    (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC) o check (fun th ->
        is_disj(concl th))) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_SIMP_TAC[MOI_FTP_AFF_CONVEX] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC) o check (fun th ->
    is_disj(concl th))) THENL
   [(* S vertex kept: w = s, u = r, u' = z *)
    MP_TAC(ISPECL [`v:real^3`; `s:real^3`; `r:real^3`; `z:real^3`;
                   `moi_ftp_sa W (s:real^3) r`; `moi_ftp_sc W (s:real^3) r`;
                   `moi_ftp_sa W (s:real^3) z`; `moi_ftp_sc W (s:real^3) z`;
                   `moi_ftp_lam W (s:real^3) r - &1 / &8`;
                   `moi_ftp_lam W (s:real^3) r + &1 / &8`;
                   `moi_ftp_lam W (s:real^3) z - &1 / &8`;
                   `moi_ftp_lam W (s:real^3) z + &1 / &8`] MOI_FTP_QUAD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[moi_ftp_sa; moi_ftp_sc] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    (* F vertex kept: w = r, u = s, u' = z *)
    MP_TAC(ISPECL [`v:real^3`; `r:real^3`; `s:real^3`; `z:real^3`;
                   `moi_ftp_sa W (s:real^3) r`; `moi_ftp_sc W (s:real^3) r`;
                   `moi_ftp_sa W (z:real^3) r`; `moi_ftp_sc W (z:real^3) r`;
                   `&1 - (moi_ftp_lam W (s:real^3) r - &1 / &8)`;
                   `&1 - (moi_ftp_lam W (s:real^3) r + &1 / &8)`;
                   `&1 - (moi_ftp_lam W (z:real^3) r - &1 / &8)`;
                   `&1 - (moi_ftp_lam W (z:real^3) r + &1 / &8)`] MOI_FTP_QUAD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[moi_ftp_sa; moi_ftp_sc] THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN TRY VECTOR_ARITH_TAC THEN
      UNDISCH_TAC `~(det(vector[s - v; r - v; z - v:real^3]) = &0)` THEN
      REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `{r:real^3,s,z} = {s,r,z}` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
     [SET_TAC[]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SEGMENT_SYM]) THEN REWRITE_TAC[SEGMENT_SYM] THEN
    ASM_REWRITE_TAC[]]);;

(* The level of the kite pieces: a level function equal to 1 at m and 0 at *)
(* bS, bF is >= 1/2 exactly on the corner and = 1/2 exactly on its chord.   *)

let MOI_FTP_KITE_LEVEL = prove
 (`!(f:real^N->real) m bS bF a c P.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     f m = &1 /\ f bS = &0 /\ f bF = &0 /\ f a < &1 / &2 /\ f c < &1 / &2 /\
     convex hull {m,midpoint(m,bS),midpoint(m,bF)} SUBSET P /\
     P SUBSET convex hull {m,bS,bF}
     ==> P INTER {x | &1 / &2 <= f x} = convex hull {m,midpoint(m,bS),midpoint(m,bF)} /\
         P INTER {x | f x = &1 / &2} = segment[midpoint(m,bS),midpoint(m,bF)] /\
         (segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a]) INTER
         {x | &1 / &2 <= f x} = segment[m,midpoint(m,bS)] /\
         (segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a]) INTER
         {x | f x = &1 / &2} = {midpoint(m,bS)} /\
         (segment[m,midpoint(m,bF)] UNION segment[midpoint(m,bF),c]) INTER
         {x | &1 / &2 <= f x} = segment[m,midpoint(m,bF)] /\
         (segment[m,midpoint(m,bF)] UNION segment[midpoint(m,bF),c]) INTER
         {x | f x = &1 / &2} = {midpoint(m,bF)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `m:real^N`; `bS:real^N`; `bF:real^N`] MOI_FTC_LEVEL_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `f(midpoint(m:real^N,bS)) = &1 / &2 /\ f(midpoint(m:real^N,bF)) = &1 / &2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[midpoint; VECTOR_ARITH `inv(&2) % (x + y:real^N) =
                                         (&1 - inv(&2)) % x + inv(&2) % y`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[midpoint(m,bS),midpoint(m,bF)] SUBSET
    convex hull {m:real^N,midpoint(m,bS),midpoint(m,bF)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  (* the segments from the corner points *)
  SUBGOAL_THEN
   `!p b. f(p:real^N) = &1 / &2 /\ f b < &1 / &2
          ==> segment[p,b] INTER {x | &1 / &2 <= f x} = {p}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`\z:real^N. --(f z)`; `--(&1 / &2)`; `p:real^N`; `b:real^N`]
      MOI_FTP_HALF_SEG)) THEN
    REWRITE_TAC[REAL_LE_NEG2; REAL_LT_NEG2; REAL_EQ_NEG2] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^N. f p = &1 / &2 ==> segment[m,p] SUBSET {x | &1 / &2 <= f x} /\
                                 segment[m,p] INTER {x | f x = &1 / &2} = {p}`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_SIMP_TAC[MOI_FTP_AFF_CONVEX] THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`f:real^N->real`; `&1 / &2`; `p:real^N`; `m:real^N`] MOI_FTP_HALF_SEG) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[SEGMENT_SYM] THEN
      SUBGOAL_THEN `{x:real^N | f x = &1 / &2} SUBSET {x | f x <= &1 / &2}` MP_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`m:real^N`; `p:real^N`] ENDS_IN_SEGMENT) THEN
      SUBGOAL_THEN `(p:real^N) IN {x | f x = &1 / &2}` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      ASM_REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`{x | x IN convex hull {m,bS,bF} /\ &1 / &2 <= f x} =
       convex hull {m:real^N,midpoint(m,bS),midpoint(m,bF)}`;
      `convex hull {m:real^N,midpoint(m,bS),midpoint(m,bF)} SUBSET P`;
      `P SUBSET convex hull {m:real^N,bS,bF}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`{x | x IN convex hull {m,bS,bF} /\ f x = &1 / &2} =
       segment[midpoint(m:real^N,bS),midpoint(m,bF)]`;
      `convex hull {m:real^N,midpoint(m,bS),midpoint(m,bF)} SUBSET P`;
      `segment[midpoint(m,bS),midpoint(m,bF)] SUBSET
       convex hull {m:real^N,midpoint(m,bS),midpoint(m,bF)}`;
      `P SUBSET convex hull {m:real^N,bS,bF}`] THEN SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `midpoint(m:real^N,bS)`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`midpoint(m:real^N,bS)`; `a:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`m:real^N`; `midpoint(m:real^N,bS)`]
      ENDS_IN_SEGMENT) THEN SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `midpoint(m:real^N,bS)`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`midpoint(m:real^N,bS)`; `a:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x:real^N | f x = &1 / &2} SUBSET {x | &1 / &2 <= f x}` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`m:real^N`; `midpoint(m:real^N,bS)`] ENDS_IN_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `midpoint(m:real^N,bF)`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`midpoint(m:real^N,bF)`; `c:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`m:real^N`; `midpoint(m:real^N,bF)`]
      ENDS_IN_SEGMENT) THEN SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `midpoint(m:real^N,bF)`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`midpoint(m:real^N,bF)`; `c:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x:real^N | f x = &1 / &2} SUBSET {x | &1 / &2 <= f x}` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`m:real^N`; `midpoint(m:real^N,bF)`] ENDS_IN_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* Two different triangles of a complex that are not adjacent meet in a     *)
(* common vertex at most.                                                    *)

let MOI_FTP_LINK_MEET = prove
 (`!(L:(real^N->bool)->bool) t t' x.
     lf_simplicial_complex L /\ t IN L /\ t' IN L /\ aff_dim t = &2 /\ aff_dim t' = &2 /\
     ~(t = t') /\ ~(aff_dim(t INTER t') = &1) /\ x IN t /\ x IN t'
     ==> x extreme_point_of t /\ x extreme_point_of t'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
              GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  DISCH_THEN(MP_TAC o SPECL [`t:real^N->bool`; `t':real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex(t:real^N->bool) /\ convex(t':real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t INTER t':real^N->bool) = &0` MP_TAC THENL
   [SUBGOAL_THEN `~(t INTER t':real^N->bool = t) \/ ~(t INTER t' = t')` MP_TAC THENL
     [UNDISCH_TAC `~(t:real^N->bool = t')` THEN SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [MP_TAC(ISPECL [`t INTER t':real^N->bool`; `t:real^N->bool`] FACE_OF_AFF_DIM_LT);
      MP_TAC(ISPECL [`t INTER t':real^N->bool`; `t':real^N->bool`] FACE_OF_AFF_DIM_LT)] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `t INTER t':real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    MP_TAC(ISPEC `t INTER t':real^N->bool` AFF_DIM_GE) THEN
    (SUBGOAL_THEN `~(t INTER t':real^N->bool = {})` (fun th -> REWRITE_TAC[th]) THENL
      [ASM SET_TAC[]; ALL_TAC]) THEN
    UNDISCH_TAC `~(aff_dim(t INTER t':real^N->bool) = &1)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_TAC `u:real^N`) THEN
  SUBGOAL_THEN `u:real^N = x` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM FACE_OF_SING] THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* The corridor disk Q in the link of the apex v.  It joins                 *)
(* the corner of the start kite at m1 to the corner of the end kite at m2:  *)
(* the two kite pieces and the trapezoids along the corridor path form a    *)
(* chain of 2-cells (MOI_FTP_CHAIN).  Its boundary splits into the S arc As *)
(* and the F arc AF from m1 to m2; on the level sets Y (level >= 1/2) and Z *)
(* (level = 1/2) of the dual cells Q meets only the two corners, As only     *)
(* the two S radii, AF only the two F radii (MOI_FTP_CORRIDOR).              *)
(* ========================================================================= *)

let moi_ftp_trap = new_definition
 `moi_ftp_trap (a:real^N) c a' c' = convex hull {a,c,c'} UNION convex hull {a,c',a'}`;;

let moi_ftp_pc = new_definition
 `moi_ftp_pc (P0:real^N->bool) Pn (a:num->real^N) c n j =
    if j = 0 then P0 else if j = n then Pn
    else moi_ftp_trap (a(j - 1)) (c(j - 1)) (a j) (c j)`;;

let moi_ftp_sd = new_definition
 `moi_ftp_sd (m1:real^N) p1 m2 p2 (a:num->real^N) n j =
    if j = 0 then segment[m1,p1] UNION segment[p1,a 0]
    else if j = n then segment[m2,p2] UNION segment[p2,a(n - 1)]
    else segment[a(j - 1),a j]`;;

let MOI_FTP_IDX_CASES = prove
 (`!j n. j <= n ==> j = 0 \/ j = n \/ ?i. j = SUC i /\ SUC i < n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `j:num = n` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `j - 1` THEN
  MAP_EVERY UNDISCH_TAC [`j <= n:num`; `~(j = 0)`; `~(j:num = n)`] THEN ARITH_TAC);;

let MOI_FTP_UNIONS_ENDS = prove
 (`!(A:num->real^N->bool) X n B0 Bn.
     1 <= n /\ X INTER A 0 = B0 /\ X INTER A n = Bn /\
     (!j. 0 < j /\ j < n ==> X INTER A j = {})
     ==> X INTER UNIONS {A j | j <= n} = B0 UNION Bn`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
    ASM_CASES_TAC `j = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `j:num = n` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`j <= n:num`; `~(j = 0)`; `~(j:num = n)`] THEN ARITH_TAC;
      ASM SET_TAC[]];
    STRIP_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `0` THEN REWRITE_TAC[LE_0] THEN ASM SET_TAC[]];
      CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `n:num` THEN REWRITE_TAC[LE_REFL] THEN
                      ASM SET_TAC[]]]]);;

let MOI_FTP_SEG_POLY = prove
 (`!a b:real^N. pl_polyhedron(segment[a,b])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
  REWRITE_TAC[POLYTOPE_SEGMENT]);;

let MOI_FTP_KITE_YZ = prove
 (`!(f:real^N->real) Y Z m bS bF a c P.
     (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
     f m = &1 /\ f bS = &0 /\ f bF = &0 /\ f a < &1 / &2 /\ f c < &1 / &2 /\
     convex hull {m,midpoint(m,bS),midpoint(m,bF)} SUBSET P /\
     P SUBSET convex hull {m,bS,bF} /\
     segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a] SUBSET P /\
     segment[m,midpoint(m,bF)] UNION segment[midpoint(m,bF),c] SUBSET P /\
     Y INTER convex hull {m,bS,bF} = {x | x IN convex hull {m,bS,bF} /\ &1 / &2 <= f x} /\
     Z INTER convex hull {m,bS,bF} = {x | x IN convex hull {m,bS,bF} /\ f x = &1 / &2}
     ==> Y INTER P = convex hull {m,midpoint(m,bS),midpoint(m,bF)} /\
         Z INTER P = segment[midpoint(m,bS),midpoint(m,bF)] /\
         Y INTER (segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a]) =
         segment[m,midpoint(m,bS)] /\
         Z INTER (segment[m,midpoint(m,bS)] UNION segment[midpoint(m,bS),a]) =
         {midpoint(m,bS)} /\
         Y INTER (segment[m,midpoint(m,bF)] UNION segment[midpoint(m,bF),c]) =
         segment[m,midpoint(m,bF)] /\
         Z INTER (segment[m,midpoint(m,bF)] UNION segment[midpoint(m,bF),c]) =
         {midpoint(m,bF)} /\
         ~(a IN Y) /\ ~(c IN Y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real`; `m:real^N`; `bS:real^N`; `bF:real^N`; `a:real^N`;
                 `c:real^N`; `P:real^N->bool`] MOI_FTP_KITE_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(a IN {x:real^N | &1 / &2 <= f x}) /\ ~(c IN {x:real^N | &1 / &2 <= f x})`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`midpoint(m:real^N,bS)`; `a:real^N`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`midpoint(m:real^N,bF)`; `c:real^N`] ENDS_IN_SEGMENT) THEN
  REPEAT STRIP_TAC THEN ASM SET_TAC[]);;

(* A piece inside a dual triangle t below the level 1/2 misses Y and Z. *)

let MOI_FTP_LEVEL_MISS = prove
 (`!(f:real^N->real) Y Z t p.
     Y INTER t = {x | x IN t /\ &1 / &2 <= f x} /\
     Z INTER t = {x | x IN t /\ f x = &1 / &2} /\
     p SUBSET t /\ p SUBSET {x | f x < &1 / &2}
     ==> Y INTER p = {} /\ Z INTER p = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  MESON_TAC[REAL_LT_REFL; REAL_NOT_LE]);;

let MOI_FTP_TRAPAT_TAC i =
  USE_THEN "tready" (fun th ->
    MP_TAC(MATCH_MP MOI_FTP_TRAP
      (MATCH_MP (SPEC i th)
         (ASSUME (mk_binop `(<):num->num->bool` (mk_comb(`SUC`,i)) `n:num`)))));;

let MOI_FTP_CORRIDOR = prove
 (`!(c:(real^3->bool)->bool) v m1 bS bF m2 bS' bF' Y Z.
     lf_simplicial_complex c /\ {v} IN c /\
     FINITE (simplicial_link c v) /\ combinatorial_manifold 2 (simplicial_link c v) /\
     combinatorial_manifold_with_boundary 2 (simplicial_link c v) /\
     connected (UNIONS (simplicial_link c v)) /\
     convex hull {m1,bS,bF} IN simplicial_link c v /\ ~affine_dependent {m1,bS,bF} /\
     convex hull {m2,bS',bF'} IN simplicial_link c v /\ ~affine_dependent {m2,bS',bF'} /\
     ~(m1 = bS) /\ ~(m1 = bF) /\ ~(bS = bF) /\ ~(m2 = bS') /\ ~(m2 = bF') /\ ~(bS' = bF') /\
     ~(m1 = m2) /\
     ~(aff_dim(convex hull {m1,bS,bF} INTER convex hull {m2,bS',bF'}) = &1) /\
     &0 < det(vector[bS - v; bF - v; m1 - v]) /\ det(vector[bS' - v; bF' - v; m2 - v]) < &0 /\
     (!t. t IN simplicial_link c v ==> ~(m1 IN t /\ m2 IN t)) /\
     (!t. t IN simplicial_link c v /\ aff_dim t = &2
          ==> ?f. (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
                  (!x. x extreme_point_of t ==> f x = moi_ftp_w {m1,m2} x) /\
                  Y INTER t = {x | x IN t /\ &1 / &2 <= f x} /\
                  Z INTER t = {x | x IN t /\ f x = &1 / &2})
     ==> ?Q As AF.
           pl_cell_with_boundary 2 Q (As UNION AF) /\
           Q SUBSET UNIONS (simplicial_link c v) /\
           As INTER AF = {m1,m2} /\ pl_polyhedron As /\ pl_polyhedron AF /\
           Y INTER Q = convex hull {m1,midpoint(m1,bS),midpoint(m1,bF)} UNION
                       convex hull {m2,midpoint(m2,bS'),midpoint(m2,bF')} /\
           Y INTER As = segment[m1,midpoint(m1,bS)] UNION segment[m2,midpoint(m2,bS')] /\
           Y INTER AF = segment[m1,midpoint(m1,bF)] UNION segment[m2,midpoint(m2,bF')] /\
           Z INTER Q = segment[midpoint(m1,bS),midpoint(m1,bF)] UNION
                       segment[midpoint(m2,bS'),midpoint(m2,bF')] /\
           Z INTER As = {midpoint(m1,bS), midpoint(m2,bS')} /\
           Z INTER AF = {midpoint(m1,bF), midpoint(m2,bF')} /\
           ~(As SUBSET Y) /\ ~(AF SUBSET Y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (simplicial_link c (v:real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LINK_LF]; ALL_TAC] THEN
  (* the corridor path *)
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `m1:real^3`; `bS:real^3`; `bF:real^3`;
                 `m2:real^3`; `bS':real^3`; `bF':real^3`] MOI_FTP_CORR_PATH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `convex hull {m1:real^3,bS,bF}` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `m1:real^3`)) (concl th) &&
      not(can (find_term ((=) `Y:real^3->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(m1:real^3) IN convex hull {m1,bS,bF} /\ (m2:real^3) IN convex hull {m2,bS',bF'}`
    MP_TAC THENL [CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `P:num->real^3->bool`
    (X_CHOOSE_THEN `s0:real^3` (X_CHOOSE_THEN `r0:real^3`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `P:num->real^3->bool`; `n:num`;
                 `s0:real^3`; `r0:real^3`] MOI_FTP_PATH_J) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "adj") (LABEL_TAC "step")) THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^3)`; `P:num->real^3->bool`; `n:num`;
                 `s0:real^3`; `r0:real^3`] MOI_FTP_PATH_TRIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "tris") THEN
  ABBREV_TAC `L = simplicial_link c (v:real^3)` THEN
  ABBREV_TAC `W = {m1:real^3,m2}` THEN
  (* the labels and the glue points *)
  ABBREV_TAC `s = moi_ftp_s (P:num->real^3->bool) s0 r0` THEN
  ABBREV_TAC `r = moi_ftp_r (P:num->real^3->bool) s0 r0` THEN
  ABBREV_TAC `y = moi_ftp_y (P:num->real^3->bool) s0 r0` THEN
  ABBREV_TAC `z = moi_ftp_z (P:num->real^3->bool) s0 r0` THEN
  SUBGOAL_THEN `(s:num->real^3) 0 = s0 /\ (r:num->real^3) 0 = r0` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "r"] THEN REWRITE_TAC[MOI_FTP_LAB_SUC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?ga gc:num->real^3. !j. ga j = moi_ftp_sa W (s j) (r j) /\ gc j = moi_ftp_sc W (s j) (r j)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`\j:num. moi_ftp_sa W ((s:num->real^3) j) (r j)`;
                          `\j:num. moi_ftp_sc W ((s:num->real^3) j) (r j)`] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(m1:real^3) IN W /\ (m2:real^3) IN W /\ ~(bS IN W) /\ ~(bF IN W) /\
    ~(bS' IN W) /\ ~(bF' IN W)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `convex hull {m1:real^3,bS,bF}` th) THEN
      MP_TAC(SPEC `convex hull {m2:real^3,bS',bF'}` th)) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `m1:real^3`)) (concl th) &&
      not(can (find_term ((=) `Y:real^3->bool`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!x y z:real^3. x IN convex hull {x,y,z} /\ y IN convex hull {x,y,z} /\
                     z IN convex hull {x,y,z}`
    (fun th -> MESON_TAC[th]) THEN
    REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. j <= n ==> (P:num->real^3->bool) j IN L /\ aff_dim(P j) = &2`
  (LABEL_TAC "inL") THENL
   [UNDISCH_TAC `moi_ftp_dpath L (P:num->real^3->bool) n` THEN
    REWRITE_TAC[moi_ftp_dpath] THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* no crossed edge joins the two polygon midpoints *)
  SUBGOAL_THEN `!j. j < n ==> ~((s:num->real^3) j IN W /\ (r:num->real^3) j IN W)`
  (LABEL_TAC "noW") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "tris" (fun th -> MP_TAC(MATCH_MP th (ASSUME `j:num < n`))) THEN STRIP_TAC THEN
    USE_THEN "inL" (MP_TAC o SPEC `SUC j`) THEN
    ANTS_TAC THENL [UNDISCH_TAC `j:num < n` THEN ARITH_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(P:num->real^3->bool)(SUC j) IN L`) o
      SPEC `(P:num->real^3->bool)(SUC j)` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `m1:real^3`)) (concl th) &&
      not(can (find_term ((=) `Y:real^3->bool`)) (concl th)))) THEN
    SUBGOAL_THEN `(s:num->real^3) j IN P(SUC j) /\ (r:num->real^3) j IN P(SUC j)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~((s:num->real^3) j = r j)` THEN
    EXPAND_TAC "W" THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the hypotheses of the trapezoid lemma at each inner step *)
  SUBGOAL_THEN
   `!i. SUC i < n
        ==> ~(det(vector[(s:num->real^3) i - v; r i - v; z i - v]) = &0) /\
            ((s(SUC i) = s i /\ r(SUC i) = z i) \/ (s(SUC i) = z i /\ r(SUC i) = r i)) /\
            ~(s i IN W /\ r i IN W) /\ ~(s(SUC i) IN W /\ r(SUC i) IN W) /\
            ga i = moi_ftp_sa W (s i) (r i) /\ gc i = moi_ftp_sc W (s i) (r i) /\
            ga(SUC i) = moi_ftp_sa W (s(SUC i)) (r(SUC i)) /\
            gc(SUC i) = moi_ftp_sc W (s(SUC i)) (r(SUC i))`
  (LABEL_TAC "tready") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "adj" (MP_TAC o SPEC `i:num`) THEN
      ANTS_TAC THENL [UNDISCH_TAC `SUC i < n` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL];
      USE_THEN "step" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC i < n`))) THEN MESON_TAC[];
      USE_THEN "noW" MATCH_MP_TAC THEN UNDISCH_TAC `SUC i < n` THEN ARITH_TAC;
      USE_THEN "noW" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the start kite piece *)
  SUBGOAL_THEN `~((s0:real^3) IN W /\ r0 IN W)` ASSUME_TAC THENL
   [USE_THEN "noW" (fun th -> MP_TAC(SPEC `0` th)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `2 <= n` THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3`; `m1:real^3`; `bS:real^3`; `bF:real^3`;
                 `s0:real^3`; `r0:real^3`;
                 `(ga:num->real^3) (0)`; `(gc:num->real^3) (0)`;
                 `moi_ftp_lam W (s0:real^3) r0 - &1 / &8`;
                 `moi_ftp_lam W (s0:real^3) r0 + &1 / &8`] MOI_FTP_KITE) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`W:real^3->bool`; `s0:real^3`; `r0:real^3`] MOI_FTP_SUBSEG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
    SUBGOAL_THEN `~(det(vector[m1 - v; bS - v; bF - v:real^3]) = &0)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`v:real^3`; `bS:real^3`; `bF:real^3`; `m1:real^3`]
        MOI_FTP_DET_CYC) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(s0 = bS /\ r0 = bF) \/ (s0 = bF /\ r0 = m1) \/
                  (s0 = m1 /\ r0 = bS:real^3)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term ((=) `bS:real^3`)) (concl th) &&
        can (find_term ((=) `s0:real^3`)) (concl th))) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(r0 = m1 ==> moi_ftp_lam W (s0:real^3) r0 + &1 / &8 < &1 / &2) /\
                  (s0 = m1 ==> &1 / &2 < moi_ftp_lam W (s0:real^3) r0 - &1 / &8)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(m1:real^3) IN W`;
        `(r0:real^3) IN W ==> moi_ftp_lam W (s0:real^3) r0 + &1 / &8 < &1 / &2`;
        `(s0:real^3) IN W ==> &1 / &2 < moi_ftp_lam W (s0:real^3) r0 - &1 / &8`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_ftp_sa; moi_ftp_sc];
    DISCH_THEN(X_CHOOSE_THEN `P0:real^3->bool` (LABEL_TAC "k0"))] THEN
  (* the end kite piece *)
  SUBGOAL_THEN `~((((s:num->real^3)(n - 1)):real^3) IN W /\ ((r:num->real^3)(n - 1)) IN W)` ASSUME_TAC THENL
   [USE_THEN "noW" (fun th -> MP_TAC(SPEC `n - 1` th)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `2 <= n` THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3`; `m2:real^3`; `bS':real^3`; `bF':real^3`;
                 `((s:num->real^3)(n - 1)):real^3`; `((r:num->real^3)(n - 1)):real^3`;
                 `(ga:num->real^3) (n - 1)`; `(gc:num->real^3) (n - 1)`;
                 `moi_ftp_lam W (((s:num->real^3)(n - 1)):real^3) ((r:num->real^3)(n - 1)) - &1 / &8`;
                 `moi_ftp_lam W (((s:num->real^3)(n - 1)):real^3) ((r:num->real^3)(n - 1)) + &1 / &8`] MOI_FTP_KITE) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`W:real^3->bool`; `((s:num->real^3)(n - 1)):real^3`; `((r:num->real^3)(n - 1)):real^3`] MOI_FTP_SUBSEG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))))) THEN
    SUBGOAL_THEN `~(det(vector[m2 - v; bS' - v; bF' - v:real^3]) = &0)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`v:real^3`; `bS':real^3`; `bF':real^3`; `m2:real^3`]
        MOI_FTP_DET_CYC) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(((s:num->real^3)(n - 1)) = bS' /\ ((r:num->real^3)(n - 1)) = bF') \/ (((s:num->real^3)(n - 1)) = bF' /\ ((r:num->real^3)(n - 1)) = m2) \/
                  (((s:num->real^3)(n - 1)) = m2 /\ ((r:num->real^3)(n - 1)) = bS':real^3)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term ((=) `bS':real^3`)) (concl th) &&
        can (find_term ((=) `(s:num->real^3)(n - 1)`)) (concl th))) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(((r:num->real^3)(n - 1)) = m2 ==> moi_ftp_lam W (((s:num->real^3)(n - 1)):real^3) ((r:num->real^3)(n - 1)) + &1 / &8 < &1 / &2) /\
                  (((s:num->real^3)(n - 1)) = m2 ==> &1 / &2 < moi_ftp_lam W (((s:num->real^3)(n - 1)):real^3) ((r:num->real^3)(n - 1)) - &1 / &8)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(m2:real^3) IN W`;
        `((r:num->real^3)(n - 1)) IN W
         ==> moi_ftp_lam W ((s:num->real^3)(n - 1)) ((r:num->real^3)(n - 1)) + &1 / &8 < &1 / &2`;
        `((s:num->real^3)(n - 1)) IN W
         ==> &1 / &2 < moi_ftp_lam W ((s:num->real^3)(n - 1)) ((r:num->real^3)(n - 1)) - &1 / &8`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_ftp_sa; moi_ftp_sc];
    DISCH_THEN(X_CHOOSE_THEN `Pn:real^3->bool` (LABEL_TAC "kn"))] THEN
  (* fold the glue point definitions (unfolding them would break the facts) *)
  SUBGOAL_THEN
   `!j. moi_ftp_sa W ((s:num->real^3) j) (r j) = ga j /\ moi_ftp_sc W (s j) (r j) = gc j`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) &&
    (let tm = snd(dest_forall(concl th)) in
     is_conj tm && is_eq(lhand tm) && lhs(lhand tm) = `(ga:num->real^3) j`))) THEN
  (* the pieces, their sides and the facts of the chain *)
  ABBREV_TAC `PC = moi_ftp_pc (P0:real^3->bool) Pn (ga:num->real^3) gc n` THEN
  ABBREV_TAC `SD = moi_ftp_sd (m1:real^3) (midpoint(m1,bS)) m2 (midpoint(m2,bS'))
                              (ga:num->real^3) n` THEN
  ABBREV_TAC `FD = moi_ftp_sd (m1:real^3) (midpoint(m1,bF)) m2 (midpoint(m2,bF'))
                              (gc:num->real^3) n` THEN
  SUBGOAL_THEN `~(0 = n) /\ 0 < n /\ n - 1 < n /\ SUC(n - 1) = n` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(PC:num->real^3->bool) 0 = P0 /\ PC n = Pn /\
    (!i. SUC i < n ==> PC(SUC i) = moi_ftp_trap (ga i) (gc i) (ga(SUC i)) (gc(SUC i))) /\
    (SD:num->real^3->bool) 0 = segment[m1,midpoint(m1,bS)] UNION segment[midpoint(m1,bS),ga 0] /\
    SD n = segment[m2,midpoint(m2,bS')] UNION segment[midpoint(m2,bS'),ga(n - 1)] /\
    (!i. SUC i < n ==> SD(SUC i) = segment[ga i,ga(SUC i)]) /\
    (FD:num->real^3->bool) 0 = segment[m1,midpoint(m1,bF)] UNION segment[midpoint(m1,bF),gc 0] /\
    FD n = segment[m2,midpoint(m2,bF')] UNION segment[midpoint(m2,bF'),gc(n - 1)] /\
    (!i. SUC i < n ==> FD(SUC i) = segment[gc i,gc(SUC i)])`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["PC"; "SD"; "FD"] THEN
    REWRITE_TAC[moi_ftp_pc; moi_ftp_sd; NOT_SUC; SUC_SUB1] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    (SUBGOAL_THEN `~(SUC i = n)` ASSUME_TAC THENL
      [UNDISCH_TAC `SUC i < n` THEN ARITH_TAC; ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  (* the trapezoid pieces *)
  SUBGOAL_THEN
   `!i. SUC i < n
        ==> pl_cell_with_boundary 2 ((PC:num->real^3->bool)(SUC i))
              (segment[(ga:num->real^3) i,gc i] UNION segment[gc i,gc(SUC i)] UNION
               segment[gc(SUC i),ga(SUC i)] UNION segment[ga(SUC i),ga i]) /\
            PC(SUC i) SUBSET P(SUC i) /\
            PC(SUC i) INTER segment[(s:num->real^3) i,r i] = segment[ga i,gc i] /\
            PC(SUC i) INTER segment[s(SUC i),r(SUC i)] = segment[ga(SUC i),gc(SUC i)] /\
            (!x. x extreme_point_of P(SUC i) ==> ~(x IN PC(SUC i))) /\
            segment[ga i,ga(SUC i)] INTER segment[gc i,gc(SUC i)] = {} /\
            segment[ga i,ga(SUC i)] INTER segment[ga i,gc i] = {ga i} /\
            segment[ga i,ga(SUC i)] INTER segment[ga(SUC i),gc(SUC i)] = {ga(SUC i)} /\
            segment[gc i,gc(SUC i)] INTER segment[ga i,gc i] = {gc i} /\
            segment[gc i,gc(SUC i)] INTER segment[ga(SUC i),gc(SUC i)] = {gc(SUC i)} /\
            ~(ga i = gc i) /\ ~(ga(SUC i) = gc(SUC i)) /\
            segment[ga i,ga(SUC i)] SUBSET PC(SUC i) /\
            segment[gc i,gc(SUC i)] SUBSET PC(SUC i) /\
            (!f. (!x y u. f((&1 - u) % x + u % y) = (&1 - u) * f x + u * f y) /\
                 (!x. x extreme_point_of P(SUC i) ==> f x = moi_ftp_w W x)
                 ==> PC(SUC i) SUBSET {x | f x < &1 / &2})`
  (LABEL_TAC "T") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MOI_FTP_TRAPAT_TAC `i:num` THEN REWRITE_TAC[GSYM moi_ftp_trap] THEN STRIP_TAC THEN
    SUBGOAL_THEN `i:num < n` ASSUME_TAC THENL
     [UNDISCH_TAC `SUC i < n` THEN ARITH_TAC; ALL_TAC] THEN
    USE_THEN "tris" (fun th -> MP_TAC(MATCH_MP th (ASSUME `i:num < n`))) THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!x:real^3. x extreme_point_of P(SUC i) <=> x = s i \/ x = r i \/ x = z i`
    ASSUME_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `(P:num->real^3->bool)(SUC i)`)) THEN
      ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `(PC:num->real^3->bool)(SUC i) =
                  moi_ftp_trap (ga i) (gc i) (ga(SUC i)) (gc(SUC i))` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `PC:num->real^3->bool`)) (concl th))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(P:num->real^3->bool)(SUC i)`)) THEN
    SUBGOAL_THEN
     `!x:real^3. x extreme_point_of
                 convex hull {(s:num->real^3) i, (r:num->real^3) i, (z:num->real^3) i} <=>
                 x = s i \/ x = r i \/ x = z i`
    ASSUME_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT th])
        o check (fun th -> concl th = `~affine_dependent {(s:num->real^3) i, r i, z i}`)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_ftp_trap; SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET u ==> s SUBSET t UNION u`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      REWRITE_TAC[moi_ftp_trap; SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> s SUBSET t UNION u`) THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      GEN_TAC THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_ftp_w:(real^3->bool)->real^3->real`)) (concl th) &&
        can (find_term ((=) `(z:num->real^3) i`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(<=>):bool->bool->bool`)) (concl th) &&
        can (find_term ((=) `(z:num->real^3) i`)) (concl th)))];
    ALL_TAC] THEN
  (* the start kite piece in chain form *)
  USE_THEN "k0" (STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `segment[m1:real^3,midpoint(m1,bS)] UNION
                segment[midpoint(m1,bS),(ga:num->real^3) 0] UNION
                segment[ga 0,(gc:num->real^3) 0] UNION segment[gc 0,midpoint(m1,bF)] UNION
                segment[midpoint(m1,bF),m1] SUBSET P0` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      can (term_match [] `pl_cell_with_boundary 2 (P0:real^3->bool) b`) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(PC:num->real^3->bool) 0 SUBSET P 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x extreme_point_of P 0 /\ x IN (PC:num->real^3->bool) 0 ==> x = m1`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `{m1:real^3,bS,bF}`
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `~((bS:real^3) IN P0)` THEN UNDISCH_TAC `~((bF:real^3) IN P0)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[(ga:num->real^3) 0,(gc:num->real^3) 0] SUBSET (PC:num->real^3->bool) 0 /\
    (SD:num->real^3->bool) 0 SUBSET PC 0 /\ (FD:num->real^3->bool) 0 SUBSET PC 0`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `segment[m1:real^3,midpoint(m1,bS)] UNION
                 segment[midpoint(m1,bS),(ga:num->real^3) 0] UNION
                 segment[ga 0,(gc:num->real^3) 0] UNION segment[gc 0,midpoint(m1,bF)] UNION
                 segment[midpoint(m1,bF),m1] SUBSET P0` THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 ((PC:num->real^3->bool) 0)
      ((SD:num->real^3->bool) 0 UNION (FD:num->real^3->bool) 0 UNION
       segment[(ga:num->real^3) 0,(gc:num->real^3) 0])`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`P0:real^3->bool`;
      `segment[m1:real^3,midpoint(m1,bS)] UNION
       segment[midpoint(m1,bS),(ga:num->real^3) 0] UNION
       segment[ga 0,(gc:num->real^3) 0] UNION segment[gc 0,midpoint(m1,bF)] UNION
       segment[midpoint(m1,bF),m1]`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(SD:num->real^3->bool) 0 INTER segment[(ga:num->real^3) 0,(gc:num->real^3) 0] = {ga 0} /\
    (FD:num->real^3->bool) 0 INTER segment[ga 0,gc 0] = {gc 0} /\
    SD 0 INTER FD 0 = {m1}`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the end kite piece in chain form *)
  USE_THEN "kn" (STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `segment[m2:real^3,midpoint(m2,bS')] UNION
                segment[midpoint(m2,bS'),(ga:num->real^3) (n - 1)] UNION
                segment[ga (n - 1),(gc:num->real^3) (n - 1)] UNION segment[gc (n - 1),midpoint(m2,bF')] UNION
                segment[midpoint(m2,bF'),m2] SUBSET Pn` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      can (term_match [] `pl_cell_with_boundary 2 (Pn:real^3->bool) b`) (concl th))) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(PC:num->real^3->bool) n SUBSET P n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x extreme_point_of P n /\ x IN (PC:num->real^3->bool) n ==> x = m2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `{m2:real^3,bS',bF'}`
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `~((bS':real^3) IN Pn)` THEN UNDISCH_TAC `~((bF':real^3) IN Pn)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[(ga:num->real^3) (n - 1),(gc:num->real^3) (n - 1)] SUBSET (PC:num->real^3->bool) n /\
    (SD:num->real^3->bool) n SUBSET PC n /\ (FD:num->real^3->bool) n SUBSET PC n`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `segment[m2:real^3,midpoint(m2,bS')] UNION
                 segment[midpoint(m2,bS'),(ga:num->real^3) (n - 1)] UNION
                 segment[ga (n - 1),(gc:num->real^3) (n - 1)] UNION segment[gc (n - 1),midpoint(m2,bF')] UNION
                 segment[midpoint(m2,bF'),m2] SUBSET Pn` THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 ((PC:num->real^3->bool) n)
      ((SD:num->real^3->bool) n UNION (FD:num->real^3->bool) n UNION
       segment[(ga:num->real^3) (n - 1),(gc:num->real^3) (n - 1)])`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`Pn:real^3->bool`;
      `segment[m2:real^3,midpoint(m2,bS')] UNION
       segment[midpoint(m2,bS'),(ga:num->real^3) (n - 1)] UNION
       segment[ga (n - 1),(gc:num->real^3) (n - 1)] UNION segment[gc (n - 1),midpoint(m2,bF')] UNION
       segment[midpoint(m2,bF'),m2]`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(SD:num->real^3->bool) n INTER segment[(ga:num->real^3) (n - 1),(gc:num->real^3) (n - 1)] = {ga (n - 1)} /\
    (FD:num->real^3->bool) n INTER segment[ga (n - 1),gc (n - 1)] = {gc (n - 1)} /\
    SD n INTER FD n = {m2}`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* drop the closed formulas for the end pieces: from now on PC, SD, FD stay abstract *)
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    mem (lhs(concl th)) [`(PC:num->real^3->bool) 0`; `(PC:num->real^3->bool) n`;
                         `(SD:num->real^3->bool) 0`; `(SD:num->real^3->bool) n`;
                         `(FD:num->real^3->bool) 0`; `(FD:num->real^3->bool) n`]))) THEN
  MAP_EVERY (fun (lab,t) -> FIRST_X_ASSUM(LABEL_TAC lab o check (fun th ->
      is_forall(concl th) &&
      (let tm = snd(dest_forall(concl th)) in
       is_imp tm && is_eq(rand tm) && fst(strip_comb(lhs(rand tm))) = t))))
   [("PCS",`PC:num->real^3->bool`); ("SDS",`SD:num->real^3->bool`);
    ("FDS",`FD:num->real^3->bool`)] THEN
  (* the hypotheses of the chain lemma *)
  SUBGOAL_THEN `!j. j <= n ==> (PC:num->real^3->bool) j SUBSET P j` (LABEL_TAC "PCP") THENL
   [X_GEN_TAC `j:num` THEN DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) o
      MATCH_MP MOI_FTP_IDX_CASES) THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC i < n`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j <= n ==> !x. x extreme_point_of P j /\ x IN (PC:num->real^3->bool) j
                       ==> (j = 0 /\ x = m1) \/ (j = n /\ x = m2)`
  (LABEL_TAC "VX") THENL
   [X_GEN_TAC `j:num` THEN DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) o
      MATCH_MP MOI_FTP_IDX_CASES) THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [DISJ1_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `m1:real^3`)) (concl th) &&
        can (find_term ((=) `(PC:num->real^3->bool) 0`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      DISJ2_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `m2:real^3`)) (concl th) &&
        can (find_term ((=) `(PC:num->real^3->bool) n`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC i < n`))) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. SUC i < j /\ j <= n ==> (PC:num->real^3->bool) i INTER PC j = {}`
  (LABEL_TAC "ND") THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i <= n /\ ~(i:num = j) /\ ~(i = n) /\ ~(j = 0)` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`SUC i < j`; `j <= n:num`] THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(P:num->real^3->bool) i IN L /\ aff_dim(P i) = &2 /\ P j IN L /\ aff_dim(P j) = &2 /\
      (x:real^3) IN P i /\ x IN P j /\ ~(P i = P j) /\ ~(aff_dim(P i INTER P j) = &1)`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "inL" (fun th -> MP_TAC(MATCH_MP th (ASSUME `i <= n:num`))) THEN
      USE_THEN "inL" (fun th -> MP_TAC(MATCH_MP th (ASSUME `j <= n:num`))) THEN
      USE_THEN "PCP" (fun th -> MP_TAC(MATCH_MP th (ASSUME `i <= n:num`))) THEN
      USE_THEN "PCP" (fun th -> MP_TAC(MATCH_MP th (ASSUME `j <= n:num`))) THEN
      FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th ->
        can (term_match [] `!i j. i <= n /\ j <= n /\ (P:num->real^3->bool) i = P j ==> i = j`)
          (concl th))) THEN
      FIRST_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th ->
        can (term_match []
          `!i j. SUC i < j /\ j <= n ==> ~(aff_dim((P:num->real^3->bool) i INTER P j) = &1)`)
          (concl th))) THEN
      UNDISCH_TAC `(x:real^3) IN (PC:num->real^3->bool) i` THEN
      UNDISCH_TAC `(x:real^3) IN (PC:num->real^3->bool) j` THEN
      UNDISCH_TAC `SUC i < j` THEN UNDISCH_TAC `j <= n:num` THEN UNDISCH_TAC `i <= n:num` THEN
      UNDISCH_TAC `~(i:num = j)` THEN
      REWRITE_TAC[SUBSET] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`L:(real^3->bool)->bool`; `(P:num->real^3->bool) i`;
                   `(P:num->real^3->bool) j`; `x:real^3`] MOI_FTP_LINK_MEET) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    USE_THEN "VX" (fun th -> MP_TAC(SPEC `x:real^3` (MATCH_MP th (ASSUME `i <= n:num`)))) THEN
    USE_THEN "VX" (fun th -> MP_TAC(SPEC `x:real^3` (MATCH_MP th (ASSUME `j <= n:num`)))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(m1:real^3 = m2)` THEN MESON_TAC[];
    ALL_TAC] THEN
  (* consecutive pieces meet in the glue segment; the glue segments are proper *)
  SUBGOAL_THEN `!j. j < n ==> ~((ga:num->real^3) j = gc j)` (LABEL_TAC "NE") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j = 0` THENL [FIRST_X_ASSUM SUBST1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?i. j = SUC i` (X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THENL
     [EXISTS_TAC `j - 1` THEN UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC i < n`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j < n ==> (PC:num->real^3->bool) j INTER PC(SUC j) = segment[(ga:num->real^3) j,gc j]`
  (LABEL_TAC "TRC") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "tris" (fun th -> MP_TAC(MATCH_MP th (ASSUME `j:num < n`))) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_TAC THEN
    SUBGOAL_THEN `j <= n /\ SUC j <= n` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `j:num < n` THEN ARITH_TAC; ALL_TAC] THEN
    USE_THEN "PCP" (fun th -> MP_TAC(MATCH_MP th (ASSUME `j <= n:num`))) THEN
    USE_THEN "PCP" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC j <= n`))) THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `(segment[(ga:num->real^3) j,gc j] SUBSET (PC:num->real^3->bool) j /\
       PC(SUC j) INTER segment[(s:num->real^3) j,r j] = segment[ga j,gc j]) \/
      (segment[ga j,gc j] SUBSET PC(SUC j) /\
       PC j INTER segment[s j,r j] = segment[ga j,gc j])`
    MP_TAC THENL
     [ASM_CASES_TAC `j = 0` THENL
       [DISJ1_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
        SUBGOAL_THEN `SUC 0 < n` ASSUME_TAC THENL
         [UNDISCH_TAC `2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC 0 < n`))) THEN SIMP_TAC[]];
        ALL_TAC] THEN
      DISJ2_TAC THEN
      SUBGOAL_THEN `?i. j = SUC i` (X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THENL
       [EXISTS_TAC `j - 1` THEN UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `SUC i < n` ASSUME_TAC THENL
       [UNDISCH_TAC `SUC i < n` THEN ARITH_TAC; ALL_TAC] THEN
      USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC i < n`))) THEN STRIP_TAC THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      ASM_CASES_TAC `SUC(SUC i) = n` THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
        SUBGOAL_THEN `SUC(SUC i) - 1 = SUC i` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
         [ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `SUC(SUC i) < n` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`SUC(SUC i) <= n`; `~(SUC(SUC i) = n)`] THEN ARITH_TAC;
          ALL_TAC] THEN
        USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC(SUC i) < n`))) THEN
        DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `(P:num->real^3->bool) j INTER P(SUC j) = segment[(s:num->real^3) j,r j]` THEN
    UNDISCH_TAC `(PC:num->real^3->bool) j SUBSET P j` THEN
    UNDISCH_TAC `(PC:num->real^3->bool)(SUC j) SUBSET P(SUC j)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the sides lie in the pieces; the cells *)
  SUBGOAL_THEN
   `!j. j <= n ==> (SD:num->real^3->bool) j SUBSET (PC:num->real^3->bool) j /\
                   (FD:num->real^3->bool) j SUBSET PC j`
  (LABEL_TAC "SUBS") THENL
   [X_GEN_TAC `j:num` THEN DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) o
      MATCH_MP MOI_FTP_IDX_CASES) THENL
     [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "SDS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC i < n`)]) THEN
      USE_THEN "FDS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC i < n`)]) THEN USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC i < n`))) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j <= n
        ==> pl_cell_with_boundary 2 ((PC:num->real^3->bool) j)
              ((SD:num->real^3->bool) j UNION (FD:num->real^3->bool) j UNION
               (if j = 0 then {} else segment[(ga:num->real^3)(j - 1),(gc:num->real^3)(j - 1)]) UNION
               (if j = n then {} else segment[ga j,gc j]))`
  (LABEL_TAC "CELLS") THENL
   [X_GEN_TAC `j:num` THEN DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) o
      MATCH_MP MOI_FTP_IDX_CASES) THENL
     [ASM_REWRITE_TAC[UNION_EMPTY];
      ASM_REWRITE_TAC[UNION_EMPTY] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (term_match [] `pl_cell_with_boundary 2 ((PC:num->real^3->bool) n) b`) (concl th))) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[];
      SUBGOAL_THEN `~(SUC i = 0) /\ ~(SUC i = n) /\ SUC i - 1 = i` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `SUC i < n` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "SDS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC i < n`)]) THEN
      USE_THEN "FDS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC i < n`)]) THEN USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC i < n`))) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the ends of the sides on the glue segments *)
  SUBGOAL_THEN
   `!j. j < n
        ==> (SD:num->real^3->bool) j INTER segment[(ga:num->real^3) j,(gc:num->real^3) j] = {ga j} /\
            (FD:num->real^3->bool) j INTER segment[ga j,gc j] = {gc j} /\
            SD(SUC j) INTER segment[ga j,gc j] = {ga j} /\
            FD(SUC j) INTER segment[ga j,gc j] = {gc j}`
  (LABEL_TAC "ENDS") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(SD:num->real^3->bool) j INTER segment[(ga:num->real^3) j,(gc:num->real^3) j] = {ga j} /\
      (FD:num->real^3->bool) j INTER segment[ga j,gc j] = {gc j}`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `j = 0` THENL
       [FIRST_X_ASSUM SUBST1_TAC THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `?i. j = SUC i` (X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THENL
       [EXISTS_TAC `j - 1` THEN UNDISCH_TAC `~(j = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      USE_THEN "SDS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC i < n`)]) THEN
      USE_THEN "FDS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC i < n`)]) THEN USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC i < n`))) THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `SUC j = n` THENL
     [SUBGOAL_THEN `j = n - 1` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `SUC j = n` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `SUC j < n` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`j:num < n`; `~(SUC j = n)`] THEN ARITH_TAC; ALL_TAC] THEN
    USE_THEN "SDS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC j < n`)]) THEN
    USE_THEN "FDS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC j < n`)]) THEN
    USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC j < n`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. 0 < j /\ j < n ==> (SD:num->real^3->bool) j INTER (FD:num->real^3->bool) j = {}`
  (LABEL_TAC "MID") THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?i. j = SUC i` (X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THENL
     [EXISTS_TAC `j - 1` THEN UNDISCH_TAC `0 < j` THEN ARITH_TAC; ALL_TAC] THEN
    USE_THEN "SDS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC i < n`)]) THEN
      USE_THEN "FDS" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC i < n`)]) THEN USE_THEN "T" (fun th -> MP_TAC(MATCH_MP th (ASSUME `SUC i < n`))) THEN SIMP_TAC[];
    ALL_TAC] THEN
  (* the corridor disk and its two arcs *)
  SUBGOAL_THEN
   `!j. j < n ==> (PC:num->real^3->bool) j INTER PC(SUC j) = segment[(ga:num->real^3) j,gc j] /\
                  ~(ga j = gc j)`
  (LABEL_TAC "GLUE") THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "TRC" (fun th -> ACCEPT_TAC(MATCH_MP th (ASSUME `j:num < n`)));
      USE_THEN "NE" (fun th -> ACCEPT_TAC(MATCH_MP th (ASSUME `j:num < n`)))];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL [UNDISCH_TAC `2 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`PC:num->real^3->bool`; `SD:num->real^3->bool`; `FD:num->real^3->bool`;
                 `ga:num->real^3`; `gc:num->real^3`; `n:num`] MOI_FTP_CHAIN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`PC:num->real^3->bool`; `SD:num->real^3->bool`; `FD:num->real^3->bool`;
                 `ga:num->real^3`; `gc:num->real^3`; `n:num`; `m1:real^3`; `m2:real^3`]
    MOI_FTP_CHAIN_ARCS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS {(PC:num->real^3->bool) j | j <= n}`;
    `UNIONS {(SD:num->real^3->bool) j | j <= n}`;
    `UNIONS {(FD:num->real^3->bool) j | j <= n}`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the level facts at the start kite *)
  SUBGOAL_THEN
   `Y INTER (PC:num->real^3->bool) 0 =
      convex hull {m1,midpoint(m1,bS),midpoint(m1,bF)} /\
    Z INTER PC 0 = segment[midpoint(m1,bS),midpoint(m1,bF)] /\
    Y INTER (SD:num->real^3->bool) 0 = segment[m1,midpoint(m1,bS)] /\
    Z INTER SD 0 = {midpoint(m1,bS)} /\
    Y INTER (FD:num->real^3->bool) 0 = segment[m1,midpoint(m1,bF)] /\
    Z INTER FD 0 = {midpoint(m1,bF)} /\
    ~((ga:num->real^3) 0 IN Y) /\ ~((gc:num->real^3) 0 IN Y) /\
    ga 0 IN SD 0 /\ gc 0 IN FD 0`
  (LABEL_TAC "L0") THENL
   [FIRST_ASSUM(MP_TAC o SPEC `(P:num->real^3->bool) 0` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Y:real^3->bool`)) (concl th))) THEN
    USE_THEN "inL" (fun th -> REWRITE_TAC[MATCH_MP th (SPEC `n:num` LE_0)]) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)))) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(P:num->real^3->bool) 0`)) THEN
    MP_TAC(ISPEC `{m1:real^3,bS,bF}` EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `(s:num->real^3) 0 IN {m1,bS,bF} /\ (r:num->real^3) 0 IN {m1,bS,bF}`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term ((=) `bS:real^3`)) (concl th) &&
        can (find_term ((=) `s0:real^3`)) (concl th))) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `f(m1:real^3) = &1 /\ f(bS:real^3) = &0 /\ f(bF:real^3) = &0 /\
      f((s:num->real^3) 0) = moi_ftp_w W (s 0) /\
      f((r:num->real^3) 0) = moi_ftp_w W (r 0)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `!x:real^3. x IN {m1,bS,bF} ==> f x = moi_ftp_w W x` MP_TAC THENL
       [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `m1:real^3` th) THEN MP_TAC(SPEC `bS:real^3` th) THEN
        MP_TAC(SPEC `bF:real^3` th) THEN MP_TAC(SPEC `(s:num->real^3) 0` th) THEN
        MP_TAC(SPEC `(r:num->real^3) 0` th)) THEN
      ASM_REWRITE_TAC[IN_INSERT; moi_ftp_w] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `f((ga:num->real^3) 0) < &1 / &2 /\ f((gc:num->real^3) 0) < &1 / &2`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`W:real^3->bool`; `f:real^3->real`; `(s:num->real^3) 0`;
                     `(r:num->real^3) 0`] MOI_FTP_SUBSEG_LEVEL) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        USE_THEN "noW" (fun th -> ACCEPT_TAC(MATCH_MP th (ASSUME `0 < n`)));
        ALL_TAC] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_forall(concl th) &&
        not(is_imp(snd(dest_forall(concl th)))) &&
        can (find_term ((=) `(ga:num->real^3) j`)) (concl th)));
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^3->real`; `Y:real^3->bool`; `Z:real^3->bool`; `m1:real^3`;
                   `bS:real^3`; `bF:real^3`; `(ga:num->real^3) 0`;
                   `(gc:num->real^3) 0`; `P0:real^3->bool`] MOI_FTP_KITE_YZ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `segment[m1:real^3,midpoint(m1,bS)] UNION
                   segment[midpoint(m1,bS),(ga:num->real^3) 0] UNION
                   segment[ga 0,(gc:num->real^3) 0] UNION
                   segment[gc 0,midpoint(m1,bF)] UNION
                   segment[midpoint(m1,bF),m1] SUBSET P0` THEN
      REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(PC:num->real^3->bool) 0 = P0:real^3->bool /\
      (SD:num->real^3->bool) 0 =
        segment[m1,midpoint(m1,bS)] UNION segment[midpoint(m1,bS),(ga:num->real^3) 0] /\
      (FD:num->real^3->bool) 0 =
        segment[m1,midpoint(m1,bF)] UNION segment[midpoint(m1,bF),(gc:num->real^3) 0]`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["PC"; "SD"; "FD"] THEN REWRITE_TAC[moi_ftp_sd; moi_ftp_pc] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  (* the level facts at the end kite *)
  SUBGOAL_THEN
   `Y INTER (PC:num->real^3->bool) n =
      convex hull {m2,midpoint(m2,bS'),midpoint(m2,bF')} /\
    Z INTER PC n = segment[midpoint(m2,bS'),midpoint(m2,bF')] /\
    Y INTER (SD:num->real^3->bool) n = segment[m2,midpoint(m2,bS')] /\
    Z INTER SD n = {midpoint(m2,bS')} /\
    Y INTER (FD:num->real^3->bool) n = segment[m2,midpoint(m2,bF')] /\
    Z INTER FD n = {midpoint(m2,bF')} /\
    ~((ga:num->real^3) (n - 1) IN Y) /\ ~((gc:num->real^3) (n - 1) IN Y) /\
    ga (n - 1) IN SD n /\ gc (n - 1) IN FD n`
  (LABEL_TAC "LN") THENL
   [FIRST_ASSUM(MP_TAC o SPEC `(P:num->real^3->bool) n` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Y:real^3->bool`)) (concl th))) THEN
    USE_THEN "inL" (fun th -> REWRITE_TAC[MATCH_MP th (SPEC `n:num` LE_REFL)]) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)))) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `(P:num->real^3->bool) n`)) THEN
    MP_TAC(ISPEC `{m2:real^3,bS',bF'}` EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN
     `(s:num->real^3) (n - 1) IN {m2,bS',bF'} /\ (r:num->real^3) (n - 1) IN {m2,bS',bF'}`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term ((=) `bS':real^3`)) (concl th) &&
        can (find_term ((=) `(s:num->real^3)(n - 1)`)) (concl th))) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `f(m2:real^3) = &1 /\ f(bS':real^3) = &0 /\ f(bF':real^3) = &0 /\
      f((s:num->real^3) (n - 1)) = moi_ftp_w W (s (n - 1)) /\
      f((r:num->real^3) (n - 1)) = moi_ftp_w W (r (n - 1))`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `!x:real^3. x IN {m2,bS',bF'} ==> f x = moi_ftp_w W x` MP_TAC THENL
       [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `m2:real^3` th) THEN MP_TAC(SPEC `bS':real^3` th) THEN
        MP_TAC(SPEC `bF':real^3` th) THEN MP_TAC(SPEC `(s:num->real^3) (n - 1)` th) THEN
        MP_TAC(SPEC `(r:num->real^3) (n - 1)` th)) THEN
      ASM_REWRITE_TAC[IN_INSERT; moi_ftp_w] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `f((ga:num->real^3) (n - 1)) < &1 / &2 /\ f((gc:num->real^3) (n - 1)) < &1 / &2`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`W:real^3->bool`; `f:real^3->real`; `(s:num->real^3) (n - 1)`;
                     `(r:num->real^3) (n - 1)`] MOI_FTP_SUBSEG_LEVEL) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        USE_THEN "noW" (fun th -> ACCEPT_TAC(MATCH_MP th (ASSUME `(n - 1) < n`)));
        ALL_TAC] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_forall(concl th) &&
        not(is_imp(snd(dest_forall(concl th)))) &&
        can (find_term ((=) `(ga:num->real^3) j`)) (concl th)));
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^3->real`; `Y:real^3->bool`; `Z:real^3->bool`; `m2:real^3`;
                   `bS':real^3`; `bF':real^3`; `(ga:num->real^3) (n - 1)`;
                   `(gc:num->real^3) (n - 1)`; `Pn:real^3->bool`] MOI_FTP_KITE_YZ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `segment[m2:real^3,midpoint(m2,bS')] UNION
                   segment[midpoint(m2,bS'),(ga:num->real^3) (n - 1)] UNION
                   segment[ga (n - 1),(gc:num->real^3) (n - 1)] UNION
                   segment[gc (n - 1),midpoint(m2,bF')] UNION
                   segment[midpoint(m2,bF'),m2] SUBSET Pn` THEN
      REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(PC:num->real^3->bool) n = Pn:real^3->bool /\
      (SD:num->real^3->bool) n =
        segment[m2,midpoint(m2,bS')] UNION segment[midpoint(m2,bS'),(ga:num->real^3) (n - 1)] /\
      (FD:num->real^3->bool) n =
        segment[m2,midpoint(m2,bF')] UNION segment[midpoint(m2,bF'),(gc:num->real^3) (n - 1)]`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["PC"; "SD"; "FD"] THEN REWRITE_TAC[moi_ftp_sd; moi_ftp_pc] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  (* the inner pieces and their sides miss Y and Z *)
  SUBGOAL_THEN
   `!j. 0 < j /\ j < n
        ==> Y INTER (PC:num->real^3->bool) j = {} /\ Z INTER PC j = {} /\
            Y INTER (SD:num->real^3->bool) j = {} /\ Z INTER SD j = {} /\
            Y INTER (FD:num->real^3->bool) j = {} /\ Z INTER FD j = {}`
  (LABEL_TAC "YZ") THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `Y INTER (PC:num->real^3->bool) j = {} /\ Z INTER PC j = {}`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `?i. j = SUC i` (X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THENL
       [EXISTS_TAC `j - 1` THEN UNDISCH_TAC `0 < j` THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `SUC i <= n` ASSUME_TAC THENL
       [UNDISCH_TAC `SUC i < n` THEN ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(MP_TAC o SPEC `(P:num->real^3->bool)(SUC i)` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Y:real^3->bool`)) (concl th))) THEN
      USE_THEN "inL" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `SUC i <= n`)]) THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^3->real` STRIP_ASSUME_TAC) THEN
      USE_THEN "T" (fun th -> MP_TAC(SPEC `f:real^3->real`
        (last(CONJUNCTS(MATCH_MP th (ASSUME `SUC i < n`)))))) THEN
      ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
      USE_THEN "PCP" (fun th -> ASSUME_TAC(MATCH_MP th (ASSUME `SUC i <= n`))) THEN
      MATCH_MP_TAC MOI_FTP_LEVEL_MISS THEN
      MAP_EVERY EXISTS_TAC [`f:real^3->real`; `(P:num->real^3->bool)(SUC i)`] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `j:num <= n` ASSUME_TAC THENL
     [UNDISCH_TAC `j:num < n` THEN ARITH_TAC; ALL_TAC] THEN
    USE_THEN "SUBS" (fun th -> MP_TAC(MATCH_MP th (ASSUME `j:num <= n`))) THEN
    MAP_EVERY UNDISCH_TAC [`Y INTER (PC:num->real^3->bool) j = {}`;
                           `Z INTER (PC:num->real^3->bool) j = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the corridor lies in the link *)
  SUBGOAL_THEN `UNIONS {(PC:num->real^3->bool) j | j <= n} SUBSET UNIONS L` ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "PCP" (fun th -> MP_TAC(MATCH_MP th (ASSUME `j:num <= n`))) THEN
    USE_THEN "inL" (fun th -> MP_TAC(CONJUNCT1(MATCH_MP th (ASSUME `j:num <= n`)))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the two arcs are polyhedra *)
  SUBGOAL_THEN `pl_polyhedron(UNIONS {(SD:num->real^3->bool) j | j <= n}) /\
                pl_polyhedron(UNIONS {(FD:num->real^3->bool) j | j <= n})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4L_PL_POLYHEDRON_UNIONS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LE] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["SD"; "FD"] THEN REWRITE_TAC[moi_ftp_sd] THEN
    REPEAT COND_CASES_TAC THEN SIMP_TAC[PL_POLYHEDRON_UNION; MOI_FTP_SEG_POLY];
    ALL_TAC] THEN
  (* Y and Z on the corridor and on its arcs *)
  SUBGOAL_THEN
   `Y INTER UNIONS {(PC:num->real^3->bool) j | j <= n} =
      convex hull {m1,midpoint(m1,bS),midpoint(m1,bF)} UNION
      convex hull {m2,midpoint(m2,bS'),midpoint(m2,bF')} /\
    Y INTER UNIONS {(SD:num->real^3->bool) j | j <= n} =
      segment[m1,midpoint(m1,bS)] UNION segment[m2,midpoint(m2,bS')] /\
    Y INTER UNIONS {(FD:num->real^3->bool) j | j <= n} =
      segment[m1,midpoint(m1,bF)] UNION segment[m2,midpoint(m2,bF')] /\
    Z INTER UNIONS {(PC:num->real^3->bool) j | j <= n} =
      segment[midpoint(m1,bS),midpoint(m1,bF)] UNION
      segment[midpoint(m2,bS'),midpoint(m2,bF')] /\
    Z INTER UNIONS {(SD:num->real^3->bool) j | j <= n} =
      {midpoint(m1,bS), midpoint(m2,bS')} /\
    Z INTER UNIONS {(FD:num->real^3->bool) j | j <= n} =
      {midpoint(m1,bF), midpoint(m2,bF')}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(GEN_REWRITE_TAC RAND_CONV [SET_RULE `{a:real^3,b} = {a} UNION {b}`]) THEN
    MATCH_MP_TAC MOI_FTP_UNIONS_ENDS THEN
    USE_THEN "L0" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "LN" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "YZ" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `0 < j /\ j < n`)]);
    ALL_TAC] THEN
  (* the arcs leave Y *)
  SUBGOAL_THEN `~(UNIONS {(SD:num->real^3->bool) j | j <= n} SUBSET Y) /\
                ~(UNIONS {(FD:num->real^3->bool) j | j <= n} SUBSET Y)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; NOT_FORALL_THM; NOT_IMP] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `(ga:num->real^3) 0`; EXISTS_TAC `(gc:num->real^3) 0`] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ========================================================================= *)
(* The generalized abstract block.  As tubec's moi_ftc_abl                  *)
(* (a level region Y radial from v over the link sphere L, outer sphere     *)
(* X = Z UNION (Y INTER L), two dual disks G_i with rims R_i, fingers Fg),  *)
(* but the trace Q of the block on L is any 2-cell of L whose boundary is   *)
(* the union of two arcs As, AF from m1 to m2 (the corridor above), meeting *)
(* the dual disks in the corner triangles conv{m_i,p_i,q_i}.  bs and b1 are *)
(* points of As and AF outside Y.  MOI_FTP_AB_... generalizes the           *)
(* corresponding MOI_FTC_AB_... (tubec's wedge is the case of two link      *)
(* triangles, p_i, q_i the midpoints towards bs, b1).                        *)
(* ========================================================================= *)

let moi_ftp_abl = new_definition
 `moi_ftp_abl (v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg <=>
    moi_ftc_rad v L X Y /\ X = Z UNION (Y INTER L) /\ Z SUBSET Y /\
    pl_cell_with_boundary 2 Q (As UNION AF) /\ Q SUBSET L /\
    As INTER AF = {m1,m2} /\ pl_polyhedron As /\ pl_polyhedron AF /\
    bs IN As /\ ~(bs IN Y) /\ b1 IN AF /\ ~(b1 IN Y) /\
    ~collinear {m1,p1,q1} /\ ~collinear {m2,p2,q2} /\
    pl_cell_with_boundary 2 G1 R1 /\ pl_cell_with_boundary 2 G2 R2 /\
    G1 INTER Q = convex hull {m1,p1,q1} /\ G2 INTER Q = convex hull {m2,p2,q2} /\
    G1 INTER As = segment[m1,p1] /\ G1 INTER AF = segment[m1,q1] /\
    G2 INTER As = segment[m2,p2] /\ G2 INTER AF = segment[m2,q2] /\
    R1 INTER Q = segment[p1,q1] /\ R2 INTER Q = segment[p2,q2] /\
    Y INTER L = G1 UNION G2 UNION Fg /\ Fg INTER Q = {} /\
    Fg INTER (G1 UNION G2) = {} /\ G1 INTER G2 = {} /\
    Z INTER G1 = R1 /\ Z INTER G2 = R2`;;

(* The trace Q on the link and its complement Q' are 2-cells with the       *)
(* common boundary circle J = As UNION AF.                                   *)

let MOI_FTP_AB_Q = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg
     ==> pl_cell_with_boundary 2 Q (As UNION AF) /\
         pl_cell_with_boundary 2 ((L DIFF Q) UNION (As UNION AF)) (As UNION AF) /\
         pl_sphere 1 (As UNION AF)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftp_abl; moi_ftc_rad] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FTC_DISK_COMPLEMENT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`1`; `Q:real^N->bool`; `As UNION AF:real^N->bool`] MOI_S4O_CELL_SPHERE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]]);;

let MOI_FTP_AB_SWAP = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg
     ==> moi_ftp_abl v L X Y Z m2 m1 p2 q2 p1 q1 bs b1 Q As AF G2 G1 R2 R1 Fg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftp_abl] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

(* The corner of the dual disk G1 on the trace. *)

let MOI_FTP_AB_G = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg
     ==> ~collinear {m1,p1,q1} /\
         convex hull {m1,p1,q1} SUBSET G1 /\
         G1 INTER Q = convex hull {m1,p1,q1} /\
         R1 INTER Q = segment[p1,q1] /\
         G1 INTER As = segment[m1,p1] /\ G1 INTER AF = segment[m1,q1] /\
         R1 INTER As = {p1} /\ R1 INTER AF = {q1} /\
         m1 IN G1 /\ ~(m1 IN R1) /\ p1 IN R1 /\ q1 IN R1 /\
         ~(bs IN G1) /\ ~(b1 IN G1) /\ R1 SUBSET G1 /\ G1 SUBSET L /\ G1 SUBSET X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftp_abl] THEN STRIP_TAC THEN
  SUBGOAL_THEN `R1 SUBSET (G1:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (G1:real^N->bool) R1`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(As UNION AF) SUBSET (Q:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (Q:real^N->bool) (As UNION AF)`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m1:real^N) IN convex hull {m1,p1,q1} /\ p1 IN convex hull {m1,p1,q1} /\
                q1 IN convex hull {m1,p1,q1} /\ segment[p1,q1] SUBSET convex hull {m1,p1,q1}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]) THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m1:real^N) IN segment[m1,p1] /\ (p1:real^N) IN segment[m1,p1] /\
                (p1:real^N) IN segment[p1,q1] /\ (q1:real^N) IN segment[p1,q1] /\
                (m1:real^N) IN segment[m1,q1] /\ (q1:real^N) IN segment[m1,q1]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m1:real^N`; `p1:real^N`; `q1:real^N`] MOI_FSA_TRI_EDGES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((m1:real^N) IN segment[p1,q1])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear {m1:real^N,p1,q1}` THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SET_RULE `{a:real^N,b,c} = {b,a,c}`] THEN
    MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G1:real^N->bool) SUBSET Y /\ G1 SUBSET L` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `R1 INTER As = {p1:real^N} /\ R1 INTER AF = {q1:real^N}` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`R1 SUBSET (G1:real^N->bool)`; `(As UNION AF) SUBSET (Q:real^N->bool)`;
      `(R1:real^N->bool) INTER Q = segment[p1,q1]`;
      `(G1:real^N->bool) INTER As = segment[m1,p1]`;
      `(G1:real^N->bool) INTER AF = segment[m1,q1]`;
      `segment[m1:real^N,p1] INTER segment[p1,q1] = {p1}`;
      `segment[q1:real^N,m1] INTER segment[m1,p1] = {m1}`;
      `segment[p1:real^N,q1] INTER segment[q1,m1] = {q1}`;
      `(p1:real^N) IN segment[m1,p1]`; `(p1:real^N) IN segment[p1,q1]`;
      `(q1:real^N) IN segment[p1,q1]`; `(q1:real^N) IN segment[m1,q1]`] THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(ASM SET_TAC[]) THEN
  UNDISCH_TAC `X:real^N->bool = Z UNION Y INTER L` THEN
  UNDISCH_TAC `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg` THEN SET_TAC[]);;

(* The two 3-cells of the block: the level region over Q and over Q'. *)

let MOI_FTP_AB_W = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg
     ==> pl_cell_with_boundary 3 (Y INTER moi_ftc_cone v Q)
           ((X INTER moi_ftc_cone v Q) UNION (Y INTER moi_ftc_cone v (As UNION AF))) /\
         pl_cell_with_boundary 3
           (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF)))
           ((X INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) UNION
            (Y INTER moi_ftc_cone v (As UNION AF)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_Q) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftp_abl]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad]) THEN
  ABBREV_TAC `J = (As:real^N->bool) UNION AF` THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET Q` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (Q:real^N->bool) J`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftc_cone] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_SECTOR3 THEN
  MAP_EVERY EXISTS_TAC [`L:real^N->bool`] THENL
   [EXISTS_TAC `(L DIFF Q) UNION (J:real^N->bool)`;
    EXISTS_TAC `Q:real^N->bool`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[moi_ftc_cone]) THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* The two fins of the block and the core arc. *)

let MOI_FTP_AB_R = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg
     ==> pl_cell_with_boundary 1 (X INTER moi_ftc_cone v As) {m1,m2} /\
         pl_cell_with_boundary 2 (Y INTER moi_ftc_cone v As)
           ((X INTER moi_ftc_cone v As) UNION segment[v,m1] UNION segment[v,m2]) /\
         pl_cell_with_boundary 1 (X INTER moi_ftc_cone v AF) {m1,m2} /\
         pl_cell_with_boundary 2 (Y INTER moi_ftc_cone v AF)
           ((X INTER moi_ftc_cone v AF) UNION segment[v,m1] UNION segment[v,m2]) /\
         pl_cell_with_boundary 1 (segment[v,m1] UNION segment[v,m2]) {m1,m2} /\
         Y INTER moi_ftc_cone v {m1,m2} = segment[v,m1] UNION segment[v,m2]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_Q) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_G) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_G o MATCH_MP MOI_FTP_AB_SWAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftp_abl]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad]) THEN
  SUBGOAL_THEN `(As UNION AF) SUBSET (Q:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (Q:real^N->bool) (As UNION AF)`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_sphere 1 ((AF:real^N->bool) UNION As) /\ As UNION AF SUBSET (L:real^N->bool) /\
    AF UNION As SUBSET (L:real^N->bool) /\ AF INTER As = {m1:real^N,m2} /\
    ~(m1:real^N = m2) /\ (m1:real^N) IN X /\ (m2:real^N) IN X /\
    (m1:real^N) IN As /\ (m2:real^N) IN As /\
    ~((As:real^N->bool) SUBSET {m1,m2}) /\ ~((AF:real^N->bool) SUBSET {m1,m2}) /\
    (G1:real^N->bool) SUBSET Y /\ (G2:real^N->bool) SUBSET Y`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(G1:real^N->bool) SUBSET Y /\ (G2:real^N->bool) SUBSET Y`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg` THEN SET_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[UNION_COMM] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(ASM SET_TAC[]) THEN
    MAP_EVERY UNDISCH_TAC
     [`(m1:real^N) IN G1`; `(m2:real^N) IN G2`; `(G1:real^N->bool) INTER G2 = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[moi_ftc_cone]) THEN REWRITE_TAC[moi_ftc_cone] THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `As:real^N->bool`; `AF:real^N->bool`; `m1:real^N`; `m2:real^N`]
    MOI_FTC_SECTOR2) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `AF:real^N->bool`; `As:real^N->bool`; `m1:real^N`; `m2:real^N`]
    MOI_FTC_SECTOR2) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {segment[v:real^N,y] | y | y IN {m1,m2}} = segment[v,m1] UNION segment[v,m2]`
  SUBST1_TAC THENL [REWRITE_TAC[MOI_FTC_CONE_PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^N->bool) INTER (segment[v,m1] UNION segment[v,m2]) =
                segment[v,m1] UNION segment[v,m2]` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET y ==> y INTER s = s`) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `Y:real^N->bool`)) THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN c ==> s SUBSET UNIONS c`) THEN
    REWRITE_TAC[IN_ELIM_THM] THENL
     [EXISTS_TAC `m1:real^N`; EXISTS_TAC `m2:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 (segment[v:real^N,m1] UNION segment[v,m2]) {m1,m2}`
  ASSUME_TAC THENL
   [ALL_TAC; REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC] THEN
  (* the core arc from the boundary circle of the fin *)
  MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
  MAP_EVERY EXISTS_TAC
   [`(X INTER UNIONS {segment[v:real^N,y] | y | y IN As})
     UNION segment[v,m1] UNION segment[v,m2]`;
    `X INTER UNIONS {segment[v:real^N,y] | y | y IN As}`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`1`;
      `Y INTER UNIONS {segment[v:real^N,y] | y | y IN As}`;
      `(X INTER UNIONS {segment[v:real^N,y] | y | y IN As})
       UNION segment[v,m1] UNION segment[v,m2]`] MOI_S4O_CELL_SPHERE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    SET_TAC[];
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
    MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
    MAP_EVERY EXISTS_TAC [`1`; `{m1:real^N,m2}`] THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC CLOSED_UNION THEN REWRITE_TAC[CLOSED_SEGMENT];
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `m1:real^N`]
      MOI_FTC_X_SEG) THEN
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `m2:real^N`]
      MOI_FTC_X_SEG) THEN
    SUBGOAL_THEN `(m1:real^N) IN L /\ (m2:real^N) IN L` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `As UNION AF SUBSET (L:real^N->bool)` THEN
      UNDISCH_TAC `(m1:real^N) IN As` THEN UNDISCH_TAC `(m2:real^N) IN As` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(m1:real^N) IN UNIONS {segment[v,y] | y | y IN As} /\
                  (m2:real^N) IN UNIONS {segment[v,y] | y | y IN As}`
    MP_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THENL
       [EXISTS_TAC `segment[v:real^N,m1]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        EXISTS_TAC `m1:real^N` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `segment[v:real^N,m2]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        EXISTS_TAC `m2:real^N` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v:real^N`; `m1:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`v:real^N`; `m2:real^N`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `(m1:real^N) IN X` THEN UNDISCH_TAC `(m2:real^N) IN X` THEN SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC MOI_FTC_CELL_NOT_SUBSET THEN EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC[LE_REFL];
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `v:real^N` THEN
    REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT; IN_INSERT; NOT_IN_EMPTY] THEN
    MAP_EVERY UNDISCH_TAC [`~((v:real^N) IN X)`; `(m1:real^N) IN X`; `(m2:real^N) IN X`] THEN
    MESON_TAC[]]);;

(* The outer sphere X over Q and over J = As UNION AF: the frontier part Z  *)
(* and the corners of the dual disks.                                       *)

let MOI_FTP_AB_X = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg
     ==> X INTER moi_ftc_cone v Q =
         (Z INTER moi_ftc_cone v Q) UNION convex hull {m1,p1,q1} UNION
         convex hull {m2,p2,q2} /\
         X INTER moi_ftc_cone v (As UNION AF) =
         (Z INTER moi_ftc_cone v (As UNION AF)) UNION
         (segment[m1,p1] UNION segment[m1,q1]) UNION
         (segment[m2,p2] UNION segment[m2,q2]) /\
         Z INTER convex hull {m1,p1,q1} = segment[p1,q1] /\
         Z INTER convex hull {m2,p2,q2} = segment[p2,q2] /\
         Z INTER (segment[m1,p1] UNION segment[m1,q1]) = {p1,q1} /\
         Z INTER (segment[m2,p2] UNION segment[m2,q2]) = {p2,q2}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_G) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_G o MATCH_MP MOI_FTP_AB_SWAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftp_abl]) THEN
  ABBREV_TAC `J = (As:real^N->bool) UNION AF` THEN
  FIRST_ASSUM(LABEL_TAC "Jdef" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `J:real^N->bool`)) THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET Q` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (Q:real^N->bool) J`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `L INTER moi_ftc_cone (v:real^N) Q = Q /\ L INTER moi_ftc_cone v J = J`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_RAD_LINK THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(J:real^N->bool) SUBSET Q`; `(Q:real^N->bool) SUBSET L`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[p1:real^N,q1] SUBSET convex hull {m1,p1,q1} /\
    segment[p2:real^N,q2] SUBSET convex hull {m2,p2,q2} /\
    segment[m1:real^N,p1] UNION segment[m1,q1] SUBSET convex hull {m1,p1,q1} /\
    segment[m2:real^N,p2] UNION segment[m2,q2] SUBSET convex hull {m2,p2,q2}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL; UNION_SUBSET] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^N->bool) INTER L INTER Q =
                convex hull {m1,p1,q1} UNION convex hull {m2,p2,q2}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg` THEN
    UNDISCH_TAC `(G1:real^N->bool) INTER Q = convex hull {m1,p1,q1}` THEN
    UNDISCH_TAC `(G2:real^N->bool) INTER Q = convex hull {m2,p2,q2}` THEN
    UNDISCH_TAC `(Fg:real^N->bool) INTER Q = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(G1:real^N->bool) INTER J = segment[m1,p1] UNION segment[m1,q1] /\
    (G2:real^N->bool) INTER J = segment[m2,p2] UNION segment[m2,q2] /\
    (Fg:real^N->bool) INTER J = {}`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "Jdef" (SUBST1_TAC o SYM) THEN REWRITE_TAC[UNION_OVER_INTER] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Fg:real^N->bool) INTER Q = {}` THEN
    UNDISCH_TAC `(J:real^N->bool) SUBSET Q` THEN USE_THEN "Jdef" (SUBST1_TAC o SYM) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^N->bool) INTER L INTER J =
                (segment[m1,p1] UNION segment[m1,q1]) UNION
                (segment[m2,p2] UNION segment[m2,q2])`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTER_ASSOC] THEN
    UNDISCH_TAC `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg` THEN
    UNDISCH_TAC `(G1:real^N->bool) INTER J = segment[m1,p1] UNION segment[m1,q1]` THEN
    UNDISCH_TAC `(G2:real^N->bool) INTER J = segment[m2,p2] UNION segment[m2,q2]` THEN
    UNDISCH_TAC `(Fg:real^N->bool) INTER J = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!X Z Y L C Q H:real^N->bool.
      X = Z UNION (Y INTER L) /\ L INTER C = Q /\ Y INTER L INTER Q = H
      ==> X INTER C = (Z INTER C) UNION H`
  (LABEL_TAC "r1") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z G R Q H TT:real^N->bool.
      Z INTER G = R /\ R INTER Q = TT /\ G INTER Q = H /\ TT SUBSET H /\ R SUBSET G
      ==> Z INTER H = TT`
  (LABEL_TAC "r2") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z G R A B SA SB p q:real^N.
      Z INTER G = R /\ R SUBSET G /\ G INTER A = SA /\ G INTER B = SB /\
      R INTER A = {p} /\ R INTER B = {q}
      ==> Z INTER (SA UNION SB) = {p,q}`
  (LABEL_TAC "r3") THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "r1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `L:real^N->bool`; `Q:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "r1" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `L:real^N->bool`; `J:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "r2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`G1:real^N->bool`; `R1:real^N->bool`; `Q:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "r2" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`G2:real^N->bool`; `R2:real^N->bool`; `Q:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "r3" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`G1:real^N->bool`; `R1:real^N->bool`;
                          `As:real^N->bool`; `AF:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "r3" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`G2:real^N->bool`; `R2:real^N->bool`;
                          `As:real^N->bool`; `AF:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* The frontier part T = Z INTER cone(Q) of the block boundary is a 2-cell. *)

let MOI_FTP_AB_T = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg
     ==> pl_cell_with_boundary 2 (Z INTER moi_ftc_cone v Q)
           ((Z INTER moi_ftc_cone v (As UNION AF)) UNION
            segment[p1,q1] UNION segment[p2,q2])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_Q) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_X) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_G) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_G o MATCH_MP MOI_FTP_AB_SWAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftp_abl]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad]) THEN
  ABBREV_TAC `J = (As:real^N->bool) UNION AF` THEN
  FIRST_ASSUM(LABEL_TAC "Jdef" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `J:real^N->bool`)) THEN
  ABBREV_TAC `Q' = (L DIFF Q) UNION (J:real^N->bool)` THEN
  ABBREV_TAC `H1 = convex hull {m1:real^N,p1,q1}` THEN
  ABBREV_TAC `H2 = convex hull {m2:real^N,p2,q2}` THEN
  ABBREV_TAC `A1 = segment[m1:real^N,p1] UNION segment[m1,q1]` THEN
  ABBREV_TAC `A2 = segment[m2:real^N,p2] UNION segment[m2,q2]` THEN
  FIRST_ASSUM(LABEL_TAC "A1def" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `A1:real^N->bool`)) THEN
  FIRST_ASSUM(LABEL_TAC "A2def" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `A2:real^N->bool`)) THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET Q` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (Q:real^N->bool) J`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m1:real^N) IN J` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN UNDISCH_TAC `(As:real^N->bool) INTER AF = {m1,m2}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q INTER Q' = (J:real^N->bool) /\ Q UNION Q' = L /\ ~(Q INTER Q' = {}) /\
                Q' SUBSET L`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q'" THEN UNDISCH_TAC `(J:real^N->bool) SUBSET Q` THEN
    UNDISCH_TAC `(Q:real^N->bool) SUBSET L` THEN UNDISCH_TAC `(m1:real^N) IN J` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the radial pieces of X over Q' and the cover of X *)
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (X INTER moi_ftc_cone (v:real^N) Q') (X INTER moi_ftc_cone v J)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cone] THEN MATCH_MP_TAC MOI_FTC_RADIAL_PIECE THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `Q:real^N->bool`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[moi_ftc_cone]) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `Q INTER Q' = (J:real^N->bool)` THEN
    UNDISCH_TAC `Q UNION Q' = (L:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `X = (X INTER moi_ftc_cone (v:real^N) Q) UNION (X INTER moi_ftc_cone v Q') /\
    (X INTER moi_ftc_cone (v:real^N) Q) INTER (X INTER moi_ftc_cone v Q') =
    X INTER moi_ftc_cone v J`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `X SUBSET moi_ftc_cone (v:real^N) Q UNION moi_ftc_cone v Q'`
      MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      SUBGOAL_THEN `moi_ftc_cone (v:real^N) Q UNION moi_ftc_cone v Q' = moi_ftc_cone v L`
      SUBST1_TAC THENL
       [REWRITE_TAC[moi_ftc_cone; GSYM MOI_FTC_CONE_UNION] THEN
        UNDISCH_TAC `(Q:real^N->bool) UNION Q' = L` THEN DISCH_THEN SUBST1_TAC THEN
        REFL_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[SET_RULE `((x:real^N->bool) INTER a) INTER (x INTER b) = x INTER (a INTER b)`] THEN
      AP_TERM_TAC THEN REWRITE_TAC[moi_ftc_cone] THEN
      MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `Q:real^N->bool`; `Q':real^N->bool`]
        MOI_FTC_CONE_INTER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC `Q INTER Q' = (J:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
        REFL_TAC]];
    ALL_TAC] THEN
  (* corner triangles: cells, arcs, traces *)
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 H1 (A1 UNION segment[p1:real^N,q1]) /\
    pl_cell_with_boundary 2 H2 (A2 UNION segment[p2:real^N,q2])`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`m1:real^N`; `p1:real^N`; `q1:real^N`] MOI_FTC_TRI_CELL) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      EXPAND_TAC "A1";
      MP_TAC(ISPECL [`m2:real^N`; `p2:real^N`; `q2:real^N`] MOI_FTC_TRI_CELL) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      EXPAND_TAC "A2"] THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[p1:real^N,m1] INTER segment[m1,q1] = {m1} /\
    segment[p2:real^N,m2] INTER segment[m2,q2] = {m2} /\
    ~(p1:real^N = m1) /\ ~(m1:real^N = q1) /\ ~(p2:real^N = m2) /\ ~(m2:real^N = q2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m1:real^N`; `p1:real^N`; `q1:real^N`] MOI_FSA_TRI_EDGES) THEN
    MP_TAC(ISPECL [`m2:real^N`; `p2:real^N`; `q2:real^N`] MOI_FSA_TRI_EDGES) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `segment[p1:real^N,m1] = segment[m1,p1] /\ segment[q1:real^N,m1] = segment[m1,q1] /\
                  segment[p2:real^N,m2] = segment[m2,p2] /\ segment[q2:real^N,m2] = segment[m2,q2]`
    (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~collinear {m1:real^N,p1,q1}`;
      UNDISCH_TAC `~collinear {m1:real^N,p1,q1}`;
      UNDISCH_TAC `~collinear {m2:real^N,p2,q2}`;
      UNDISCH_TAC `~collinear {m2:real^N,p2,q2}`] THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1:real^N,m1] UNION segment[m1,q1] = A1 /\
                segment[p2:real^N,m2] UNION segment[m2,q2] = A2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A1"; "A2"] THEN REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(A1:real^N->bool) SUBSET H1 /\ (A2:real^N->bool) SUBSET H2 /\
    segment[p1:real^N,q1] SUBSET H1 /\ segment[p2:real^N,q2] SUBSET H2 /\
    {p1:real^N,q1} SUBSET segment[p1,q1] /\ {p2:real^N,q2} SUBSET segment[p2,q2]`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["H1"; "H2"; "A1"; "A2"] THEN
    REWRITE_TAC[UNION_SUBSET; INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_SEGMENT] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(H1:real^N->bool) INTER H2 = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `G1 INTER G2:real^N->bool = {}` THEN
    UNDISCH_TAC `(H1:real^N->bool) SUBSET G1` THEN
    UNDISCH_TAC `(H2:real^N->bool) SUBSET G2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(H1:real^N->bool) INTER J = A1 /\ (H2:real^N->bool) INTER J = A2`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!G1 G2 H1 H2 J As AF A1 A2 S1 F1 S2 F2:real^N->bool.
        J = As UNION AF /\ G1 INTER As = S1 /\ G1 INTER AF = F1 /\
        G2 INTER As = S2 /\ G2 INTER AF = F2 /\ A1 = S1 UNION F1 /\ A2 = S2 UNION F2 /\
        H1 SUBSET G1 /\ H2 SUBSET G2 /\ A1 SUBSET H1 /\ A2 SUBSET H2
        ==> H1 INTER J = A1 /\ H2 INTER J = A2`) THEN
    MAP_EVERY EXISTS_TAC
     [`G1:real^N->bool`; `G2:real^N->bool`; `As:real^N->bool`; `AF:real^N->bool`;
      `segment[m1:real^N,p1]`; `segment[m1:real^N,q1]`;
      `segment[m2:real^N,p2]`; `segment[m2:real^N,q2]`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_ACCEPT_TAC o SYM o check (fun th -> is_eq(concl th) &&
      (rhs(concl th) = `A1:real^N->bool` || rhs(concl th) = `A2:real^N->bool`) &&
      can (find_term ((=) `segment[m1:real^N,p1]`)) (concl th) =
      (rhs(concl th) = `A1:real^N->bool`) &&
      not (can (find_term ((=) `segment[p1:real^N,m1]`)) (concl th)) &&
      not (can (find_term ((=) `segment[p2:real^N,m2]`)) (concl th))));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(H1:real^N->bool) SUBSET X /\ (H1:real^N->bool) SUBSET L /\ H1 SUBSET Q /\
    (H2:real^N->bool) SUBSET X /\ (H2:real^N->bool) SUBSET L /\ H2 SUBSET Q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(H1:real^N->bool) SUBSET G1` THEN UNDISCH_TAC `(H2:real^N->bool) SUBSET G2` THEN
    UNDISCH_TAC `(G1:real^N->bool) SUBSET L` THEN UNDISCH_TAC `(G2:real^N->bool) SUBSET L` THEN
    UNDISCH_TAC `(G1:real^N->bool) SUBSET X` THEN UNDISCH_TAC `(G2:real^N->bool) SUBSET X` THEN
    UNDISCH_TAC `(G1:real^N->bool) INTER Q = H1` THEN
    UNDISCH_TAC `(G2:real^N->bool) INTER Q = H2` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `XQ' = X INTER moi_ftc_cone (v:real^N) Q'` THEN
  SUBGOAL_THEN `L INTER moi_ftc_cone (v:real^N) Q' = Q'` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTC_RAD_LINK THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `XQ' INTER H1 = (A1:real^N->bool) /\ XQ' INTER H2 = (A2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!X C L Q Q' J H1 H2 A1 A2 XQ':real^N->bool.
        XQ' = X INTER C /\ L INTER C = Q' /\ Q' = (L DIFF Q) UNION J /\
        H1 SUBSET X /\ H1 SUBSET L /\ H1 SUBSET Q /\ H1 INTER J = A1 /\
        H2 SUBSET X /\ H2 SUBSET L /\ H2 SUBSET Q /\ H2 INTER J = A2
        ==> XQ' INTER H1 = A1 /\ XQ' INTER H2 = A2`) THEN
    MAP_EVERY EXISTS_TAC
     [`X:real^N->bool`; `moi_ftc_cone (v:real^N) Q'`; `L:real^N->bool`;
      `Q:real^N->bool`; `Q':real^N->bool`; `J:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (XQ':real^N->bool)
      ((Z INTER moi_ftc_cone (v:real^N) J) UNION A1 UNION A2)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `pl_cell_with_boundary 2 (XQ':real^N->bool) (X INTER moi_ftc_cone v J)`)) THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `X INTER moi_ftc_cone (v:real^N) J`));
    ALL_TAC] THEN
  (* glue H1, then H2 *)
  MP_TAC(ISPECL [`XQ':real^N->bool`; `((Z INTER moi_ftc_cone (v:real^N) J) UNION A1 UNION A2)`; `H1:real^N->bool`;
                 `A1 UNION segment[p1:real^N,q1]`; `p1:real^N`; `m1:real^N`; `q1:real^N`]
    MOI_FRS_GLUE2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`XQ' UNION H1:real^N->bool`;
                 `(((Z INTER moi_ftc_cone (v:real^N) J) UNION A1 UNION A2) UNION A1 UNION segment[p1:real^N,q1]) DIFF (A1 DIFF {p1,q1})`;
                 `H2:real^N->bool`; `A2 UNION segment[p2:real^N,q2]`;
                 `p2:real^N`; `m2:real^N`; `q2:real^N`] MOI_FRS_GLUE2) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      UNDISCH_TAC `XQ' INTER H2 = (A2:real^N->bool)` THEN
      UNDISCH_TAC `(H1:real^N->bool) INTER H2 = {}` THEN SET_TAC[];
      UNDISCH_TAC `(H1:real^N->bool) INTER H2 = {}` THEN
      UNDISCH_TAC `(A1:real^N->bool) SUBSET H1` THEN
      UNDISCH_TAC `(A2:real^N->bool) SUBSET H2` THEN SET_TAC[];
      SET_TAC[]];
    DISCH_TAC] THEN
  (* the complement in the sphere X *)
  MP_TAC(ISPECL [`X:real^N->bool`; `(XQ' UNION H1) UNION H2:real^N->bool`;
    `(((((Z INTER moi_ftc_cone (v:real^N) J) UNION A1 UNION A2) UNION A1 UNION segment[p1:real^N,q1]) DIFF (A1 DIFF {p1,q1})) UNION
      A2 UNION segment[p2,q2]) DIFF (A2 DIFF {p2,q2})`] MOI_FTC_DISK_COMPLEMENT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC;
      EXPAND_TAC "XQ'" THEN UNDISCH_TAC `(H1:real^N->bool) SUBSET X` THEN
      UNDISCH_TAC `(H2:real^N->bool) SUBSET X` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* identification *)
  SUBGOAL_THEN
   `(H1:real^N->bool) SUBSET moi_ftc_cone v Q /\ (H2:real^N->bool) SUBSET moi_ftc_cone v Q /\
    (A1:real^N->bool) SUBSET moi_ftc_cone v J /\ (A2:real^N->bool) SUBSET moi_ftc_cone v J /\
    moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!P:real^N->bool. P SUBSET moi_ftc_cone v P` ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[moi_ftc_cone; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `segment[v:real^N,y]` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q` ASSUME_TAC THENL
     [REWRITE_TAC[moi_ftc_cone] THEN MATCH_MP_TAC MOI_FTC_CONE_MONO THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(A1:real^N->bool) SUBSET J /\ (A2:real^N->bool) SUBSET J`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(H1:real^N->bool) INTER J = A1` THEN
      UNDISCH_TAC `(H2:real^N->bool) INTER J = A2` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[p1:real^N,q1] INTER A1 = {p1,q1} /\ segment[p2:real^N,q2] INTER A2 = {p2,q2}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m1:real^N`; `p1:real^N`; `q1:real^N`] MOI_FSA_TRI_EDGES) THEN
    MP_TAC(ISPECL [`m2:real^N`; `p2:real^N`; `q2:real^N`] MOI_FSA_TRI_EDGES) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "A1def" (SUBST1_TAC o SYM) THEN USE_THEN "A2def" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`X:real^N->bool`; `X INTER moi_ftc_cone (v:real^N) Q`; `XQ':real^N->bool`;
    `((Z INTER moi_ftc_cone (v:real^N) J) UNION A1 UNION A2)`; `Z INTER moi_ftc_cone (v:real^N) Q`;
    `Z INTER moi_ftc_cone (v:real^N) J`; `H1:real^N->bool`; `H2:real^N->bool`;
    `A1:real^N->bool`; `A2:real^N->bool`; `segment[p1:real^N,q1]`;
    `segment[p2:real^N,q2]`; `{p1:real^N,q1}`; `{p2:real^N,q2}`] MOI_FTC_T_SETS) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!Z C S P:real^N->bool. Z INTER S = P /\ S SUBSET C ==> (Z INTER C) INTER S = P`
  (LABEL_TAC "zc") THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(USE_THEN "zc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      TRY(MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_ftc_cone (v:real^N) J` THEN
          ASM_REWRITE_TAC[]) THEN NO_TAC) THEN
  UNDISCH_TAC `moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q` THEN SET_TAC[]);;


(* The basic facts of the block, with Q, As, AF, J = As UNION AF and the   *)
(* complement Q' = (L DIFF Q) UNION J.                                       *)

let MOI_FTP_AB_F1 = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg J Q'.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J
     ==> Q INTER Q' = J /\ Q UNION Q' = L /\ J SUBSET Q /\ J SUBSET Q' /\
         Q SUBSET L /\ Q' SUBSET L /\ J SUBSET L /\ As SUBSET J /\ AF SUBSET J /\
         As SUBSET L /\ AF SUBSET L /\
         As INTER AF = {m1,m2} /\ bs IN As /\ b1 IN AF /\ m1 IN J /\ m2 IN J /\
         compact Q /\ compact Q' /\ compact As /\ compact AF /\
         pl_polyhedron As /\ pl_polyhedron AF /\
         pl_cell_with_boundary 2 Q J /\ pl_cell_with_boundary 2 Q' J /\ pl_sphere 1 J /\
         L INTER moi_ftc_cone v Q = Q /\ L INTER moi_ftc_cone v Q' = Q' /\
         L INTER moi_ftc_cone v J = J /\ L INTER moi_ftc_cone v As = As /\
         L INTER moi_ftc_cone v AF = AF /\
         moi_ftc_cone v Q INTER moi_ftc_cone v Q' = moi_ftc_cone v J /\
         moi_ftc_cone v As INTER moi_ftc_cone v AF = segment[v,m1] UNION segment[v,m2] /\
         moi_ftc_cone v As UNION moi_ftc_cone v AF = moi_ftc_cone v J /\
         moi_ftc_cone v J SUBSET moi_ftc_cone v Q /\
         moi_ftc_cone v J SUBSET moi_ftc_cone v Q' /\
         (X INTER moi_ftc_cone v Q) UNION (X INTER moi_ftc_cone v Q') = X /\
         X INTER moi_ftc_cone v Q =
         (Z INTER moi_ftc_cone v Q) UNION convex hull {m1,p1,q1} UNION
         convex hull {m2,p2,q2} /\
         X INTER moi_ftc_cone v Q' =
         (Z INTER moi_ftc_cone v Q') UNION (G1 INTER Q') UNION (G2 INTER Q') UNION Fg /\
         G1 INTER Q = convex hull {m1,p1,q1} /\ G2 INTER Q = convex hull {m2,p2,q2} /\
         convex hull {m1,p1,q1} SUBSET G1 /\ convex hull {m2,p2,q2} SUBSET G2 /\
         G1 INTER As = segment[m1,p1] /\ G1 INTER AF = segment[m1,q1] /\
         G2 INTER As = segment[m2,p2] /\ G2 INTER AF = segment[m2,q2] /\
         R1 INTER Q = segment[p1,q1] /\ R2 INTER Q = segment[p2,q2] /\
         R1 INTER As = {p1} /\ R1 INTER AF = {q1} /\
         R2 INTER As = {p2} /\ R2 INTER AF = {q2} /\
         Fg INTER Q = {} /\ Fg SUBSET Q' /\ Fg SUBSET L /\
         Fg INTER G1 = {} /\ Fg INTER G2 = {} /\ G1 INTER G2 = {} /\
         ~(p1 = q1) /\ ~(p2 = q2) /\ ~(p1 = p2) /\ ~(q1 = q2) /\ ~(p1 = q2) /\
         ~(q1 = p2) /\ p1 IN R1 /\ q1 IN R1 /\ p2 IN R2 /\ q2 IN R2 /\
         segment[p1,q1] SUBSET R1 /\ segment[p2,q2] SUBSET R2 /\
         R1 SUBSET Z /\ R2 SUBSET Z /\ R1 SUBSET G1 /\ R2 SUBSET G2 /\
         G1 SUBSET L /\ G2 SUBSET L /\ G1 SUBSET X /\ G2 SUBSET X /\ Z SUBSET X /\
         pl_cell_with_boundary 2 G1 R1 /\ pl_cell_with_boundary 2 G2 R2 /\
         ~(bs IN G1) /\ ~(bs IN G2) /\ ~(b1 IN G1) /\ ~(b1 IN G2) /\
         bs IN L /\ b1 IN L /\ ~(bs IN Fg) /\ ~(b1 IN Fg) /\
         m1 IN G1 /\ m2 IN G2 /\ ~(m1 IN Z) /\ ~(m2 IN Z) /\ m1 IN L /\ m2 IN L /\
         m1 IN X /\ m2 IN X /\ ~collinear {m1,p1,q1} /\ ~collinear {m2,p2,q2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_Q) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_X) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_G) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_G o MATCH_MP MOI_FTP_AB_SWAP) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftp_abl]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad]) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `X:real^N->bool`)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `Y:real^N->bool`)) THEN
  ABBREV_TAC `J = (As:real^N->bool) UNION AF` THEN
  FIRST_ASSUM(LABEL_TAC "Jdef" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `J:real^N->bool`)) THEN
  ABBREV_TAC `Q' = (L DIFF Q) UNION (J:real^N->bool)` THEN
  FIRST_ASSUM(LABEL_TAC "Q'def" o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `Q':real^N->bool`)) THEN
  SUBGOAL_THEN `(J:real^N->bool) SUBSET Q` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS o check (fun th ->
      concl th = `pl_cell_with_boundary 2 (Q:real^N->bool) J`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m1:real^N) IN J /\ (m2:real^N) IN J /\ (bs:real^N) IN As /\ (b1:real^N) IN AF /\
                As SUBSET (J:real^N->bool) /\ AF SUBSET (J:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "Jdef" (SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`(As:real^N->bool) INTER AF = {m1,m2}`; `(bs:real^N) IN As`;
                           `(b1:real^N) IN AF`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Q INTER Q' = (J:real^N->bool) /\ Q UNION Q' = L /\ Q' SUBSET L /\ J SUBSET Q' /\
                (J:real^N->bool) SUBSET L /\ (As:real^N->bool) SUBSET L /\
                (AF:real^N->bool) SUBSET L`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "Q'def" (SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`(J:real^N->bool) SUBSET Q`; `(Q:real^N->bool) SUBSET L`;
                           `(As:real^N->bool) SUBSET J`; `(AF:real^N->bool) SUBSET J`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (As:real^N->bool) /\ pl_polyhedron (AF:real^N->bool) /\
                compact (As:real^N->bool) /\ compact (AF:real^N->bool) /\
                compact (Q:real^N->bool) /\ compact (Q':real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
    MAP_EVERY EXISTS_TAC [`2`; `J:real^N->bool`] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `L INTER moi_ftc_cone (v:real^N) Q = Q /\ L INTER moi_ftc_cone v Q' = Q' /\
    L INTER moi_ftc_cone v J = J /\ L INTER moi_ftc_cone v As = As /\
    L INTER moi_ftc_cone v AF = AF`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_RAD_LINK THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_cone (v:real^N) Q INTER moi_ftc_cone v Q' = moi_ftc_cone v J`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cone] THEN
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `Q:real^N->bool`; `Q':real^N->bool`]
      MOI_FTC_CONE_INTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `m1:real^N` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_cone (v:real^N) As INTER moi_ftc_cone v AF = segment[v,m1] UNION segment[v,m2]`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cone] THEN
    MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `As:real^N->bool`; `AF:real^N->bool`]
      MOI_FTC_CONE_INTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[MOI_FTC_CONE_PAIR]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_cone (v:real^N) As UNION moi_ftc_cone v AF = moi_ftc_cone v J /\
    moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q /\
    moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q'`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "Jdef" (SUBST1_TAC o SYM) THEN REWRITE_TAC[moi_ftc_cone; MOI_FTC_CONE_UNION];
      REWRITE_TAC[moi_ftc_cone] THEN MATCH_MP_TAC MOI_FTC_CONE_MONO THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_ftc_cone] THEN MATCH_MP_TAC MOI_FTC_CONE_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(X INTER moi_ftc_cone (v:real^N) Q) UNION (X INTER moi_ftc_cone v Q') = X`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `X SUBSET moi_ftc_cone (v:real^N) Q UNION moi_ftc_cone v Q'`
    MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    SUBGOAL_THEN `moi_ftc_cone (v:real^N) Q UNION moi_ftc_cone v Q' = moi_ftc_cone v L`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_ftc_cone; GSYM MOI_FTC_CONE_UNION] THEN
      UNDISCH_TAC `(Q:real^N->bool) UNION Q' = L` THEN DISCH_THEN SUBST1_TAC THEN
      REFL_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fg:real^N->bool) SUBSET L /\ Fg SUBSET Q' /\ Fg INTER G1 = {} /\
                Fg INTER G2 = {}`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "Q'def" (SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC [`(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg`;
                           `(Fg:real^N->bool) INTER Q = {}`;
                           `(Fg:real^N->bool) INTER (G1 UNION G2) = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `X INTER moi_ftc_cone (v:real^N) Q' =
    (Z INTER moi_ftc_cone v Q') UNION (G1 INTER Q') UNION (G2 INTER Q') UNION Fg`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!X Z Y L C Q' G1 G2 Fg:real^N->bool.
        Z UNION (Y INTER L) = X /\ L INTER C = Q' /\ Y INTER L = G1 UNION G2 UNION Fg /\
        Fg SUBSET Q'
        ==> X INTER C = (Z INTER C) UNION (G1 INTER Q') UNION (G2 INTER Q') UNION Fg`) THEN
    EXISTS_TAC `Y:real^N->bool` THEN EXISTS_TAC `L:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p1:real^N = q1) /\ ~(p2:real^N = q2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~collinear {m1:real^N,p1,q1}`;
      UNDISCH_TAC `~collinear {m2:real^N,p2,q2}`] THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p1:real^N = p2) /\ ~(q1:real^N = q2) /\ ~(p1:real^N = q2) /\
                ~(q1:real^N = p2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(R1:real^N->bool) SUBSET G1`; `(R2:real^N->bool) SUBSET G2`;
      `(G1:real^N->bool) INTER G2 = {}`; `(p1:real^N) IN R1`; `(q1:real^N) IN R1`;
      `(p2:real^N) IN R2`; `(q2:real^N) IN R2`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[p1:real^N,q1] SUBSET R1 /\ segment[p2:real^N,q2] SUBSET R2 /\
    (R1:real^N->bool) SUBSET Z /\ (R2:real^N->bool) SUBSET Z /\ (Z:real^N->bool) SUBSET X`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(R1:real^N->bool) INTER Q = segment[p1,q1]`;
      `(R2:real^N->bool) INTER Q = segment[p2,q2]`; `(Z:real^N->bool) INTER G1 = R1`;
      `(Z:real^N->bool) INTER G2 = R2`; `Z UNION Y INTER L = (X:real^N->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(bs:real^N) IN L /\ (b1:real^N) IN L /\ ~(bs IN Fg) /\ ~(b1 IN Fg)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(bs:real^N) IN As`; `(b1:real^N) IN AF`;
      `(As:real^N->bool) SUBSET J`; `(AF:real^N->bool) SUBSET J`;
      `(J:real^N->bool) SUBSET Q`; `(Q:real^N->bool) SUBSET L`;
      `(Fg:real^N->bool) INTER Q = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((m1:real^N) IN Z) /\ ~((m2:real^N) IN Z) /\ (m1:real^N) IN L /\ (m2:real^N) IN L /\
    (m1:real^N) IN X /\ (m2:real^N) IN X`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(m1:real^N) IN G1`; `(m2:real^N) IN G2`;
      `~((m1:real^N) IN R1)`; `~((m2:real^N) IN R2)`; `(Z:real^N->bool) INTER G1 = R1`;
      `(Z:real^N->bool) INTER G2 = R2`; `(G1:real^N->bool) SUBSET L`;
      `(G2:real^N->bool) SUBSET L`; `(G1:real^N->bool) SUBSET X`;
      `(G2:real^N->bool) SUBSET X`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)));;


let MOI_FTP_AB_F2 = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg J Q'.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J
     ==> pl_cell_with_boundary 2 (Z INTER moi_ftc_cone v Q)
           ((Z INTER moi_ftc_cone v J) UNION segment[p1,q1] UNION segment[p2,q2]) /\
         segment[p1,q1] UNION (R1 INTER Q') = R1 /\
         segment[p2,q2] UNION (R2 INTER Q') = R2 /\
         segment[p1,q1] INTER (R1 INTER Q') = {p1,q1} /\
         segment[p2,q2] INTER (R2 INTER Q') = {p2,q2} /\
         segment[p1,q1] INTER J = {p1,q1} /\ segment[p2,q2] INTER J = {p2,q2} /\
         segment[p1,q1] INTER As = {p1} /\ segment[p1,q1] INTER AF = {q1} /\
         segment[p2,q2] INTER As = {p2} /\ segment[p2,q2] INTER AF = {q2} /\
         p1 IN G1 /\ q1 IN G1 /\ p2 IN G2 /\ q2 IN G2 /\
         segment[p1,q1] SUBSET Z /\ segment[p2,q2] SUBSET Z /\
         segment[p1,q1] SUBSET L /\ segment[p2,q2] SUBSET L /\
         R1 SUBSET L /\ R2 SUBSET L /\
         (Z INTER moi_ftc_cone v Q) INTER G1 = segment[p1,q1] /\
         (Z INTER moi_ftc_cone v Q) INTER G2 = segment[p2,q2] /\
         (Z INTER moi_ftc_cone v Q') INTER G1 = R1 INTER Q' /\
         (Z INTER moi_ftc_cone v Q') INTER G2 = R2 INTER Q' /\
         (Z INTER moi_ftc_cone v J) INTER segment[p1,q1] = {p1,q1} /\
         (Z INTER moi_ftc_cone v J) INTER segment[p2,q2] = {p2,q2} /\
         segment[p1,q1] INTER (Z INTER moi_ftc_cone v As) = {p1} /\
         segment[p1,q1] INTER (Z INTER moi_ftc_cone v AF) = {q1} /\
         segment[p2,q2] INTER (Z INTER moi_ftc_cone v As) = {p2} /\
         segment[p2,q2] INTER (Z INTER moi_ftc_cone v AF) = {q2} /\
         (Z INTER moi_ftc_cone v As) INTER (Z INTER moi_ftc_cone v AF) = {} /\
         ~(Z INTER moi_ftc_cone v As SUBSET {p1,p2}) /\
         ~(Z INTER moi_ftc_cone v AF SUBSET {q1,q2}) /\
         Fg INTER (Z INTER moi_ftc_cone v Q) = {} /\
         Z INTER moi_ftc_cone v J SUBSET Z INTER moi_ftc_cone v Q /\
         Z INTER moi_ftc_cone v J SUBSET Z INTER moi_ftc_cone v Q' /\
         (Z INTER moi_ftc_cone v Q) INTER (Z INTER moi_ftc_cone v Q') =
         Z INTER moi_ftc_cone v J /\
         (Z INTER moi_ftc_cone v As) UNION (Z INTER moi_ftc_cone v AF) =
         Z INTER moi_ftc_cone v J /\
         closed (Z INTER moi_ftc_cone v As) /\ closed (Z INTER moi_ftc_cone v AF)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let c = CONJUNCTS th in
    let abl = hd c and defs = tl c in
    ASSUME_TAC abl THEN STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F1 th) THEN
    ASSUME_TAC(REWRITE_RULE (map GSYM defs) (MATCH_MP MOI_FTP_AB_T abl)) THEN
    ASSUME_TAC(SYM(el 0 defs))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftp_abl]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad]) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (lhs(concl th) = `X:real^N->bool` || lhs(concl th) = `Y:real^N->bool`)))) THEN
  SUBGOAL_THEN `(R1:real^N->bool) SUBSET L /\ (R2:real^N->bool) SUBSET L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `G1:real^N->bool`; EXISTS_TAC `G2:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1,q1] UNION (R1 INTER Q') = (R1:real^N->bool) /\
                segment[p2,q2] UNION (R2 INTER Q') = (R2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(R1:real^N->bool) SUBSET L`; `(R2:real^N->bool) SUBSET L`;
      `Q UNION Q' = (L:real^N->bool)`;
      `(R1:real^N->bool) INTER Q = segment[p1,q1]`;
      `(R2:real^N->bool) INTER Q = segment[p2,q2]`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[p1,q1] INTER As = {p1:real^N} /\ segment[p1,q1] INTER AF = {q1:real^N} /\
    segment[p2,q2] INTER As = {p2:real^N} /\ segment[p2,q2] INTER AF = {q2:real^N}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`p1:real^N`; `q1:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`p2:real^N`; `q2:real^N`] ENDS_IN_SEGMENT) THEN
    MAP_EVERY UNDISCH_TAC [`segment[p1:real^N,q1] SUBSET R1`; `segment[p2:real^N,q2] SUBSET R2`;
      `(R1:real^N->bool) INTER As = {p1}`; `(R1:real^N->bool) INTER AF = {q1}`;
      `(R2:real^N->bool) INTER As = {p2}`; `(R2:real^N->bool) INTER AF = {q2}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1,q1] INTER J = {p1:real^N,q1} /\ segment[p2,q2] INTER J = {p2:real^N,q2}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`As UNION AF = (J:real^N->bool)`;
      `segment[p1,q1] INTER As = {p1:real^N}`; `segment[p1,q1] INTER AF = {q1:real^N}`;
      `segment[p2,q2] INTER As = {p2:real^N}`; `segment[p2,q2] INTER AF = {q2:real^N}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1,q1] INTER (R1 INTER Q') = {p1:real^N,q1} /\
                segment[p2,q2] INTER (R2 INTER Q') = {p2:real^N,q2}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(R1:real^N->bool) INTER Q = segment[p1,q1]`;
      `(R2:real^N->bool) INTER Q = segment[p2,q2]`; `Q INTER Q' = (J:real^N->bool)`;
      `segment[p1,q1] INTER J = {p1:real^N,q1}`; `segment[p2,q2] INTER J = {p2:real^N,q2}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p1:real^N) IN G1 /\ (q1:real^N) IN G1 /\ (p2:real^N) IN G2 /\ (q2:real^N) IN G2 /\
    segment[p1:real^N,q1] SUBSET Z /\ segment[p2:real^N,q2] SUBSET Z /\
    segment[p1:real^N,q1] SUBSET L /\ segment[p2:real^N,q2] SUBSET L`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(p1:real^N) IN R1`; `(q1:real^N) IN R1`; `(p2:real^N) IN R2`;
      `(q2:real^N) IN R2`; `(R1:real^N->bool) SUBSET G1`; `(R2:real^N->bool) SUBSET G2`;
      `segment[p1:real^N,q1] SUBSET R1`; `segment[p2:real^N,q2] SUBSET R2`;
      `(R1:real^N->bool) SUBSET Z`; `(R2:real^N->bool) SUBSET Z`;
      `(R1:real^N->bool) SUBSET L`; `(R2:real^N->bool) SUBSET L`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z G R L C Q S:real^N->bool.
      Z INTER G = R /\ R SUBSET L /\ L INTER C = Q /\ R INTER Q = S ==> (Z INTER C) INTER G = S`
  (LABEL_TAC "zg") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Z INTER moi_ftc_cone (v:real^N) Q) INTER G1 = segment[p1,q1] /\
    (Z INTER moi_ftc_cone (v:real^N) Q) INTER G2 = segment[p2,q2] /\
    (Z INTER moi_ftc_cone (v:real^N) Q') INTER G1 = R1 INTER Q' /\
    (Z INTER moi_ftc_cone (v:real^N) Q') INTER G2 = R2 INTER Q'`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "zg" MATCH_MP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`R1:real^N->bool`; `L:real^N->bool`; `Q:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`R2:real^N->bool`; `L:real^N->bool`; `Q:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`R1:real^N->bool`; `L:real^N->bool`; `Q':real^N->bool`];
      MAP_EVERY EXISTS_TAC [`R2:real^N->bool`; `L:real^N->bool`; `Q':real^N->bool`]] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z C L A S P:real^N->bool.
      S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
      ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`
  (LABEL_TAC "zs") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Z INTER moi_ftc_cone (v:real^N) J) INTER segment[p1,q1] = {p1,q1} /\
    (Z INTER moi_ftc_cone (v:real^N) J) INTER segment[p2,q2] = {p2,q2} /\
    segment[p1,q1] INTER (Z INTER moi_ftc_cone (v:real^N) As) = {p1} /\
    segment[p1,q1] INTER (Z INTER moi_ftc_cone (v:real^N) AF) = {q1} /\
    segment[p2,q2] INTER (Z INTER moi_ftc_cone (v:real^N) As) = {p2} /\
    segment[p2,q2] INTER (Z INTER moi_ftc_cone (v:real^N) AF) = {q2}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) J`; `L:real^N->bool`;
                     `J:real^N->bool`; `segment[p1:real^N,q1]`; `{p1:real^N,q1}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`));
      MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) J`; `L:real^N->bool`;
                     `J:real^N->bool`; `segment[p2:real^N,q2]`; `{p2:real^N,q2}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`));
      MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) As`; `L:real^N->bool`;
                     `As:real^N->bool`; `segment[p1:real^N,q1]`; `{p1:real^N}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`));
      MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) AF`; `L:real^N->bool`;
                     `AF:real^N->bool`; `segment[p1:real^N,q1]`; `{q1:real^N}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`));
      MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) As`; `L:real^N->bool`;
                     `As:real^N->bool`; `segment[p2:real^N,q2]`; `{p2:real^N}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`));
      MP_TAC(ISPECL [`Z:real^N->bool`; `moi_ftc_cone (v:real^N) AF`; `L:real^N->bool`;
                     `AF:real^N->bool`; `segment[p2:real^N,q2]`; `{q2:real^N}`] (ASSUME
       `!Z C L A S P:real^N->bool.
          S SUBSET Z /\ S SUBSET L /\ L INTER C = A /\ S INTER A = P
          ==> (Z INTER C) INTER S = P /\ S INTER (Z INTER C) = P`))] THEN
    ANTS_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `X INTER segment[v:real^N,m1] = {m1} /\ X INTER segment[v:real^N,m2] = {m2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_X_SEG THEN EXISTS_TAC `L:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Z INTER moi_ftc_cone (v:real^N) As) INTER (Z INTER moi_ftc_cone v AF) = {}`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`moi_ftc_cone (v:real^N) As INTER moi_ftc_cone v AF =
                            segment[v,m1] UNION segment[v,m2]`;
      `X INTER segment[v:real^N,m1] = {m1}`; `X INTER segment[v:real^N,m2] = {m2}`;
      `(Z:real^N->bool) SUBSET X`; `~((m1:real^N) IN Z)`; `~((m2:real^N) IN Z)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Z INTER moi_ftc_cone (v:real^N) As SUBSET {p1,p2}) /\
                ~(Z INTER moi_ftc_cone (v:real^N) AF SUBSET {q1,q2})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_ZRAY_POINT THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                          `G1:real^N->bool`; `G2:real^N->bool`; `Fg:real^N->bool`] THENL
     [EXISTS_TAC `bs:real^N`; EXISTS_TAC `b1:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Fg INTER (Z INTER moi_ftc_cone (v:real^N) Q) = {} /\
    Z INTER moi_ftc_cone (v:real^N) J SUBSET Z INTER moi_ftc_cone v Q /\
    Z INTER moi_ftc_cone (v:real^N) J SUBSET Z INTER moi_ftc_cone v Q' /\
    (Z INTER moi_ftc_cone (v:real^N) Q) INTER (Z INTER moi_ftc_cone v Q') =
    Z INTER moi_ftc_cone v J /\
    (Z INTER moi_ftc_cone (v:real^N) As) UNION (Z INTER moi_ftc_cone v AF) =
    Z INTER moi_ftc_cone v J`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(Fg:real^N->bool) SUBSET L`;
      `L INTER moi_ftc_cone (v:real^N) Q = Q`; `(Fg:real^N->bool) INTER Q = {}`;
      `moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q`;
      `moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q'`;
      `moi_ftc_cone (v:real^N) Q INTER moi_ftc_cone v Q' = moi_ftc_cone v J`;
      `moi_ftc_cone (v:real^N) As UNION moi_ftc_cone v AF = moi_ftc_cone v J`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (Z INTER moi_ftc_cone (v:real^N) As) /\
                closed (Z INTER moi_ftc_cone (v:real^N) AF)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `compact (Z INTER moi_ftc_cone (v:real^N) Q)` ASSUME_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN MATCH_MP_TAC MOI_S4O_CELL_POLY THEN
      MAP_EVERY EXISTS_TAC
       [`2`; `(Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1,q1] UNION segment[p2,q2]`] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `closed (moi_ftc_cone (v:real^N) As) /\ closed (moi_ftc_cone (v:real^N) AF)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[moi_ftc_cone] THEN CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN MATCH_MP_TAC MOI_FTC_CONE_POLYHEDRON THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `Z INTER moi_ftc_cone (v:real^N) As = (Z INTER moi_ftc_cone v Q) INTER moi_ftc_cone v As /\
      Z INTER moi_ftc_cone (v:real^N) AF = (Z INTER moi_ftc_cone v Q) INTER moi_ftc_cone v AF`
    (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC
       [`moi_ftc_cone (v:real^N) As UNION moi_ftc_cone v AF = moi_ftc_cone v J`;
        `moi_ftc_cone (v:real^N) J SUBSET moi_ftc_cone v Q`] THEN SET_TAC[];
      CONJ_TAC THEN MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC));;

(* The two frontier arcs of the block: alpha over As and beta over AF. *)

let MOI_FTP_AB_ALPHA = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg J Q'.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J
     ==> pl_cell_with_boundary 1 (Z INTER moi_ftc_cone v As) {p1,p2} /\
         pl_cell_with_boundary 1 (Z INTER moi_ftc_cone v AF) {q1,q2}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F1 th) THEN
                       STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F2 th)) THEN
  SUBGOAL_THEN
   `pl_sphere 1 ((Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1,q1] UNION
                 segment[p2,q2])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `Z INTER moi_ftc_cone (v:real^N) Q`;
      `(Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1,q1] UNION segment[p2,q2]`]
      MOI_S4O_CELL_SPHERE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THENL
   [EXISTS_TAC `(Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1,q1] UNION
                segment[p2,q2]` THEN
    EXISTS_TAC `(Z INTER moi_ftc_cone (v:real^N) AF) UNION segment[p1,q1] UNION
                segment[p2,q2]` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(Z INTER moi_ftc_cone (v:real^N) As) UNION (Z INTER moi_ftc_cone v AF) =
                   Z INTER moi_ftc_cone v J` THEN SET_TAC[];
      ASM_SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT];
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC
       [`(Z INTER moi_ftc_cone (v:real^N) As) INTER (Z INTER moi_ftc_cone v AF) = {}`;
        `segment[p1,q1] INTER (Z INTER moi_ftc_cone (v:real^N) As) = {p1}`;
        `segment[p2,q2] INTER (Z INTER moi_ftc_cone (v:real^N) As) = {p2}`] THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `q1:real^N` THEN
      REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT; IN_INSERT; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `~(p1:real^N = q1)` THEN UNDISCH_TAC `~(q1:real^N = p2)` THEN MESON_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    EXISTS_TAC `(Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1,q1] UNION
                segment[p2,q2]` THEN
    EXISTS_TAC `(Z INTER moi_ftc_cone (v:real^N) As) UNION segment[p1,q1] UNION
                segment[p2,q2]` THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(Z INTER moi_ftc_cone (v:real^N) As) UNION (Z INTER moi_ftc_cone v AF) =
                   Z INTER moi_ftc_cone v J` THEN SET_TAC[];
      ASM_SIMP_TAC[CLOSED_UNION; CLOSED_SEGMENT];
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC
       [`(Z INTER moi_ftc_cone (v:real^N) As) INTER (Z INTER moi_ftc_cone v AF) = {}`;
        `segment[p1,q1] INTER (Z INTER moi_ftc_cone (v:real^N) AF) = {q1}`;
        `segment[p2,q2] INTER (Z INTER moi_ftc_cone (v:real^N) AF) = {q2}`] THEN
      SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `p1:real^N` THEN
      REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT; IN_INSERT; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `~(p1:real^N = q1)` THEN UNDISCH_TAC `~(p1:real^N = q2)` THEN MESON_TAC[];
      FIRST_ASSUM ACCEPT_TAC]]);;

(* The frontier cell of the block outside the wedge: B = (Z INTER cone Q')  *)
(* UNION Fg is the complement in X of T UNION G1 UNION G2.                  *)

let MOI_FTP_AB_B = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg J Q'.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J
     ==> pl_cell_with_boundary 2 ((Z INTER moi_ftc_cone v Q') UNION Fg)
           ((Z INTER moi_ftc_cone v J) UNION (R1 INTER Q') UNION (R2 INTER Q'))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F2 th)) THEN
  SUBGOAL_THEN `pl_sphere 2 (X:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_ftp_abl]) THEN
    SIMP_TAC[moi_ftc_rad];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Z INTER moi_ftc_cone (v:real^N) Q`;
                 `(Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1:real^N,q1] UNION
                  segment[p2,q2]`;
                 `G1:real^N->bool`; `R1:real^N->bool`; `p1:real^N`; `q1:real^N`]
    MOI_FTC_GLUE_SEG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(Z INTER moi_ftc_cone (v:real^N) Q) UNION G1`;
                 `(((Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1:real^N,q1] UNION
                    segment[p2,q2]) UNION R1) DIFF (segment[p1,q1] DIFF {p1,q1})`;
                 `G2:real^N->bool`; `R2:real^N->bool`; `p2:real^N`; `q2:real^N`]
    MOI_FTC_GLUE_SEG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MAP_EVERY UNDISCH_TAC
       [`(Z INTER moi_ftc_cone (v:real^N) Q) INTER G2 = segment[p2,q2]`;
        `(G1:real^N->bool) INTER G2 = {}`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`segment[p1:real^N,q1] SUBSET R1`; `segment[p2:real^N,q2] SUBSET R2`;
        `(R1:real^N->bool) SUBSET G1`; `(R2:real^N->bool) SUBSET G2`;
        `(G1:real^N->bool) INTER G2 = {}`] THEN
      SET_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`X:real^N->bool`; `((Z INTER moi_ftc_cone (v:real^N) Q) UNION G1) UNION G2`;
    `((((Z INTER moi_ftc_cone (v:real^N) J) UNION segment[p1:real^N,q1] UNION
        segment[p2,q2]) UNION R1) DIFF (segment[p1,q1] DIFF {p1,q1}) UNION R2) DIFF
     (segment[p2,q2] DIFF {p2,q2})`] MOI_FTC_DISK_COMPLEMENT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MAP_EVERY UNDISCH_TAC [`(Z:real^N->bool) SUBSET X`; `(G1:real^N->bool) SUBSET X`;
                           `(G2:real^N->bool) SUBSET X`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`X:real^N->bool`; `X INTER moi_ftc_cone (v:real^N) Q`; `X INTER moi_ftc_cone (v:real^N) Q'`;
    `Z INTER moi_ftc_cone (v:real^N) Q`; `convex hull {m1:real^N,p1,q1}`;
    `convex hull {m2:real^N,p2,q2}`; `G1:real^N->bool`; `G2:real^N->bool`;
    `G1 INTER Q':real^N->bool`; `G2 INTER Q':real^N->bool`;
    `Z INTER moi_ftc_cone (v:real^N) Q'`; `Fg:real^N->bool`;
    `Z INTER moi_ftc_cone (v:real^N) J`; `segment[p1:real^N,q1]`; `segment[p2:real^N,q2]`;
    `R1 INTER Q':real^N->bool`; `R2 INTER Q':real^N->bool`; `R1:real^N->bool`;
    `R2:real^N->bool`; `{p1:real^N,q1}`; `{p2:real^N,q2}`] MOI_FTC_B_SETS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    MAP_EVERY UNDISCH_TAC
     [`(Z INTER moi_ftc_cone (v:real^N) Q') INTER G1 = R1 INTER Q'`;
      `(Z INTER moi_ftc_cone (v:real^N) Q') INTER G2 = R2 INTER Q'`;
      `segment[p1:real^N,q1] SUBSET R1`; `segment[p2:real^N,q2] SUBSET R2`;
      `(R1:real^N->bool) SUBSET G1`; `(R2:real^N->bool) SUBSET G2`;
      `Fg INTER (Z INTER moi_ftc_cone (v:real^N) Q) = {}`] THEN
    SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN REWRITE_TAC[]]);;

(* The set identities behind the outer part G1 INTER Q' of the dual disk. *)

let MOI_FTP_AB_DISK = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg J Q'.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J
     ==> pl_cell_with_boundary 2 (convex hull {m1,p1,q1})
           ((segment[m1,p1] UNION segment[m1,q1]) UNION segment[p1,q1]) /\
         pl_cell_with_boundary 2 (G1 INTER Q')
           ((segment[m1,p1] UNION segment[m1,q1]) UNION (R1 INTER Q')) /\
         pl_cell_with_boundary 1 (segment[m1,p1]) {m1,p1} /\
         pl_cell_with_boundary 1 (segment[m1,q1]) {m1,q1} /\
         pl_cell_with_boundary 1 (segment[p1,q1]) {p1,q1} /\
         pl_cell_with_boundary 1 (R1 INTER Q') {p1,q1} /\
         G1 INTER J = segment[m1,p1] UNION segment[m1,q1] /\
         segment[p1,q1] INTER (segment[m1,p1] UNION segment[m1,q1]) = {p1,q1} /\
         ~(m1 = p1) /\ ~(m1 = q1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F2 th) THEN
    ASSUME_TAC(SYM(el 0 (tl(CONJUNCTS th))))) THEN
  SUBGOAL_THEN `pl_sphere 2 (L:real^N->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [moi_ftp_abl]) THEN
    SIMP_TAC[moi_ftc_rad];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m1:real^N = p1) /\ ~(m1:real^N = q1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~collinear {m1:real^N,p1,q1}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(G1:real^N->bool) INTER J = segment[m1,p1] UNION segment[m1,q1]`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`As UNION AF = (J:real^N->bool)`;
      `(G1:real^N->bool) INTER As = segment[m1,p1]`;
      `(G1:real^N->bool) INTER AF = segment[m1,q1]`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p1,q1] INTER (segment[m1,p1] UNION segment[m1,q1]) = {p1:real^N,q1}`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`segment[p1:real^N,q1] SUBSET R1`; `(R1:real^N->bool) SUBSET G1`;
      `(G1:real^N->bool) INTER As = segment[m1,p1]`;
      `(G1:real^N->bool) INTER AF = segment[m1,q1]`;
      `segment[p1,q1] INTER As = {p1:real^N}`; `segment[p1,q1] INTER AF = {q1:real^N}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (convex hull {m1:real^N,p1,q1})
                  ((segment[m1,p1] UNION segment[m1,q1]) UNION segment[p1,q1])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m1:real^N`; `p1:real^N`; `q1:real^N`] MOI_FTC_TRI_CELL) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 ((L DIFF G1) UNION R1) (R1:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTC_DISK_COMPLEMENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->bool`; `G1:real^N->bool`; `R1:real^N->bool`;
                 `convex hull {m1:real^N,p1,q1}`; `Q:real^N->bool`; `Q':real^N->bool`;
                 `J:real^N->bool`; `segment[m1:real^N,p1] UNION segment[m1,q1]`;
                 `segment[p1:real^N,q1]`; `{p1:real^N,q1}`; `R1 INTER Q':real^N->bool`]
    MOI_FTC_D_SETS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(FIRST_ASSUM(ACCEPT_TAC o SYM)) THEN TRY REFL_TAC THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; ENDS_IN_SEGMENT];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`(L DIFF G1) UNION R1:real^N->bool`; `R1:real^N->bool`;
                 `convex hull {m1:real^N,p1,q1}`;
                 `(segment[m1:real^N,p1] UNION segment[m1,q1]) UNION segment[p1,q1]`;
                 `p1:real^N`; `q1:real^N`] MOI_FTC_GLUE_SEG) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN SET_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 ((G1:real^N->bool) INTER Q')
                  ((segment[m1,p1] UNION segment[m1,q1]) UNION (R1 INTER Q'))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:real^N->bool`;
                   `((L DIFF G1) UNION R1) UNION convex hull {m1:real^N,p1,q1}`;
                   `(R1 UNION (segment[m1:real^N,p1] UNION segment[m1,q1]) UNION
                     segment[p1,q1]) DIFF (segment[p1,q1] DIFF {p1,q1})`]
      MOI_FTC_DISK_COMPLEMENT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (R1:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`1`; `G1:real^N->bool`; `R1:real^N->bool`] MOI_S4O_CELL_SPHERE) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 1 (R1 INTER Q') {p1:real^N,q1}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
    MAP_EVERY EXISTS_TAC [`R1:real^N->bool`; `segment[p1:real^N,q1]`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[CLOSED_SEGMENT];
      MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
        MATCH_MP_TAC MOI_S4O_SPHERE_POLY THEN EXISTS_TAC `1` THEN FIRST_ASSUM ACCEPT_TAC;
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
      EXISTS_TAC `midpoint(p1:real^N,q1)` THEN
      ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT; IN_INSERT; NOT_IN_EMPTY; MIDPOINT_EQ_ENDPOINT];
      DISCH_TAC THEN
      MP_TAC(ISPEC `R1:real^N->bool` MOI_FTC_SPHERE1_NOT_CONVEX) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `R1 = segment[p1:real^N,q1]` (fun th -> REWRITE_TAC[th; CONVEX_SEGMENT]) THEN
      MP_TAC(ISPECL [`p1:real^N`; `q1:real^N`] ENDS_IN_SEGMENT) THEN
      MAP_EVERY UNDISCH_TAC [`R1 INTER Q' SUBSET {p1:real^N,q1}`;
        `segment[p1,q1] UNION (R1 INTER Q') = (R1:real^N->bool)`;
        `segment[p1:real^N,q1] SUBSET R1`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC MOI_FCL_SEGMENT_CELL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The eighteen cells of the abstract block in the form used                *)
(* by the product assembly: W j = moi_ftc_zd (Y INTER cone Q) (Y INTER cone *)
(* Q') (Y INTER cone As) (Y INTER cone AF) (Z UNION Fg) ([v,m1] UNION        *)
(* [v,m2]) j are the block cells, G1 INTER W j the cells of the dual disk.   *)
(* ========================================================================= *)

let MOI_FTP_AB_F3 = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg J Q'.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J
     ==> Z SUBSET Y /\ G1 SUBSET Y /\ G2 SUBSET Y /\ Fg SUBSET Y /\
         segment[v,m1] UNION segment[v,m2] SUBSET Y INTER moi_ftc_cone v As /\
         segment[v,m1] UNION segment[v,m2] SUBSET Y INTER moi_ftc_cone v AF /\
         Y INTER moi_ftc_cone v J =
         (Y INTER moi_ftc_cone v As) UNION (Y INTER moi_ftc_cone v AF) /\
         X INTER moi_ftc_cone v As =
         (Z INTER moi_ftc_cone v As) UNION segment[m1,p1] UNION segment[m2,p2] /\
         X INTER moi_ftc_cone v AF =
         (Z INTER moi_ftc_cone v AF) UNION segment[m1,q1] UNION segment[m2,q2] /\
         (Z UNION Fg) INTER (Y INTER moi_ftc_cone v Q) = Z INTER moi_ftc_cone v Q /\
         (Z UNION Fg) INTER (Y INTER moi_ftc_cone v Q') = (Z INTER moi_ftc_cone v Q') UNION Fg /\
         (Y INTER moi_ftc_cone v As) INTER (Z UNION Fg) = Z INTER moi_ftc_cone v As /\
         (Y INTER moi_ftc_cone v AF) INTER (Z UNION Fg) = Z INTER moi_ftc_cone v AF /\
         G1 INTER (Y INTER moi_ftc_cone v Q) = convex hull {m1,p1,q1} /\
         G1 INTER (Y INTER moi_ftc_cone v Q') = G1 INTER Q' /\
         G1 INTER (Y INTER moi_ftc_cone v As) = segment[m1,p1] /\
         G1 INTER (Y INTER moi_ftc_cone v AF) = segment[m1,q1] /\
         G1 INTER (Z UNION Fg) = R1 /\
         G1 INTER (segment[v,m1] UNION segment[v,m2]) = {m1} /\
         G2 INTER (Y INTER moi_ftc_cone v Q) = convex hull {m2,p2,q2} /\
         G2 INTER (Y INTER moi_ftc_cone v Q') = G2 INTER Q' /\
         G2 INTER (Y INTER moi_ftc_cone v As) = segment[m2,p2] /\
         G2 INTER (Y INTER moi_ftc_cone v AF) = segment[m2,q2] /\
         G2 INTER (Z UNION Fg) = R2 /\
         G2 INTER (segment[v,m1] UNION segment[v,m2]) = {m2}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let c = CONJUNCTS th in
    let abl = hd c in
    ASSUME_TAC abl THEN STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F1 th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F2 th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTP_AB_R o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_ftp_abl" with Failure _ -> false))
        (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftp_abl] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_ftp_abl" with Failure _ -> false))
        (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_ftc_rad] o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "moi_ftc_rad" with Failure _ -> false))
        (concl th))) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (lhs(concl th) = `X:real^N->bool` || lhs(concl th) = `Y:real^N->bool`)))) THEN
  SUBGOAL_THEN `(G1:real^N->bool) SUBSET Y /\ (G2:real^N->bool) SUBSET Y /\
                (Fg:real^N->bool) SUBSET Y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(Y:real^N->bool) INTER L = G1 UNION G2 UNION Fg` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_cone (v:real^N) {m1,m2} SUBSET moi_ftc_cone v As /\
    moi_ftc_cone (v:real^N) {m1,m2} SUBSET moi_ftc_cone v AF`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_cone] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_FTC_CONE_MONO THEN
    UNDISCH_TAC `As INTER AF = {m1:real^N,m2}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_ftc_cone (v:real^N) {m1,m2} = segment[v,m1] UNION segment[v,m2]`
  ASSUME_TAC THENL [REWRITE_TAC[moi_ftc_cone; MOI_FTC_CONE_PAIR]; ALL_TAC] THEN
  SUBGOAL_THEN `L INTER moi_ftc_cone (v:real^N) {m1,m2} = {m1,m2}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTC_RAD_LINK THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fg:real^N->bool) INTER As = {} /\ (Fg:real^N->bool) INTER AF = {} /\
                (Q':real^N->bool) SUBSET moi_ftc_cone v Q'`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(Fg:real^N->bool) INTER Q = {}`; `(As:real^N->bool) SUBSET J`;
      `(AF:real^N->bool) SUBSET J`; `(J:real^N->bool) SUBSET Q`;
      `L INTER moi_ftc_cone (v:real^N) Q' = Q'`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!X Z Y L C A G1 G2 Fg S1 S2:real^N->bool.
      Z UNION Y INTER L = X /\ L INTER C = A /\ Y INTER L = G1 UNION G2 UNION Fg /\
      G1 INTER A = S1 /\ G2 INTER A = S2 /\ Fg INTER A = {}
      ==> X INTER C = (Z INTER C) UNION S1 UNION S2`
  (LABEL_TAC "xc") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z Y Fg L C P:real^N->bool.
      Z SUBSET Y /\ Fg SUBSET L /\ L INTER C = P /\ Fg INTER P = {}
      ==> (Z UNION Fg) INTER (Y INTER C) = Z INTER C /\
          (Y INTER C) INTER (Z UNION Fg) = Z INTER C`
  (LABEL_TAC "zf") THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!G Y L C P H:real^N->bool.
      G SUBSET Y /\ G SUBSET L /\ L INTER C = P /\ G INTER P = H
      ==> G INTER (Y INTER C) = H`
  (LABEL_TAC "gc") THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MAP_EVERY UNDISCH_TAC
     [`Y INTER moi_ftc_cone (v:real^N) {m1,m2} = segment[v,m1] UNION segment[v,m2]`;
      `moi_ftc_cone (v:real^N) {m1,m2} SUBSET moi_ftc_cone v As`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`Y INTER moi_ftc_cone (v:real^N) {m1,m2} = segment[v,m1] UNION segment[v,m2]`;
      `moi_ftc_cone (v:real^N) {m1,m2} SUBSET moi_ftc_cone v AF`] THEN SET_TAC[];
    UNDISCH_TAC `moi_ftc_cone (v:real^N) As UNION moi_ftc_cone v AF = moi_ftc_cone v J` THEN
    SET_TAC[];
    USE_THEN "xc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `L:real^N->bool`; `As:real^N->bool`;
                          `G1:real^N->bool`; `G2:real^N->bool`; `Fg:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "xc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`Y:real^N->bool`; `L:real^N->bool`; `AF:real^N->bool`;
                          `G1:real^N->bool`; `G2:real^N->bool`; `Fg:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`Z:real^N->bool`; `Y:real^N->bool`; `Fg:real^N->bool`; `L:real^N->bool`;
                   `moi_ftc_cone (v:real^N) Q`; `Q:real^N->bool`]
      (ASSUME `!Z Y Fg L C P:real^N->bool.
                 Z SUBSET Y /\ Fg SUBSET L /\ L INTER C = P /\ Fg INTER P = {}
                 ==> (Z UNION Fg) INTER (Y INTER C) = Z INTER C /\
                     (Y INTER C) INTER (Z UNION Fg) = Z INTER C`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    MAP_EVERY UNDISCH_TAC [`(Z:real^N->bool) SUBSET Y`; `(Fg:real^N->bool) SUBSET Y`;
      `(Fg:real^N->bool) SUBSET Q'`; `(Q':real^N->bool) SUBSET moi_ftc_cone v Q'`] THEN
    SET_TAC[];
    MP_TAC(ISPECL [`Z:real^N->bool`; `Y:real^N->bool`; `Fg:real^N->bool`; `L:real^N->bool`;
                   `moi_ftc_cone (v:real^N) As`; `As:real^N->bool`]
      (ASSUME `!Z Y Fg L C P:real^N->bool.
                 Z SUBSET Y /\ Fg SUBSET L /\ L INTER C = P /\ Fg INTER P = {}
                 ==> (Z UNION Fg) INTER (Y INTER C) = Z INTER C /\
                     (Y INTER C) INTER (Z UNION Fg) = Z INTER C`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    MP_TAC(ISPECL [`Z:real^N->bool`; `Y:real^N->bool`; `Fg:real^N->bool`; `L:real^N->bool`;
                   `moi_ftc_cone (v:real^N) AF`; `AF:real^N->bool`]
      (ASSUME `!Z Y Fg L C P:real^N->bool.
                 Z SUBSET Y /\ Fg SUBSET L /\ L INTER C = P /\ Fg INTER P = {}
                 ==> (Z UNION Fg) INTER (Y INTER C) = Z INTER C /\
                     (Y INTER C) INTER (Z UNION Fg) = Z INTER C`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `Q:real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `Q':real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `As:real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `AF:real^N->bool`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Z:real^N->bool) INTER G1 = R1`; `(Fg:real^N->bool) INTER G1 = {}`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(G1:real^N->bool) SUBSET L`;
      `L INTER moi_ftc_cone (v:real^N) {m1,m2} = {m1,m2}`;
      `moi_ftc_cone (v:real^N) {m1,m2} = segment[v,m1] UNION segment[v,m2]`;
      `(m1:real^N) IN G1`; `(m2:real^N) IN G2`; `(G1:real^N->bool) INTER G2 = {}`] THEN
    SET_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `Q:real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `Q':real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `As:real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "gc" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `AF:real^N->bool`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Z:real^N->bool) INTER G2 = R2`; `(Fg:real^N->bool) INTER G2 = {}`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(G2:real^N->bool) SUBSET L`;
      `L INTER moi_ftc_cone (v:real^N) {m1,m2} = {m1,m2}`;
      `moi_ftc_cone (v:real^N) {m1,m2} = segment[v,m1] UNION segment[v,m2]`;
      `(m1:real^N) IN G1`; `(m2:real^N) IN G2`; `(G1:real^N->bool) INTER G2 = {}`] THEN
    SET_TAC[]]);;

(* The eighteen cells of the generalized abstract block. *)

let MOI_FTP_AB_CELLS = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg J Q' W.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J /\
     W = moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v Q')
                    (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF)
                    (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])
     ==> !j. j < 9
             ==> pl_cell_with_boundary (1 + moi_ftc_dd j) (W j)
                   (UNIONS {W j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)} UNION
                    ((G1 UNION G2) INTER W j)) /\
                 pl_cell_with_boundary (moi_ftc_dd j) (G1 INTER W j)
                   (G1 INTER UNIONS {W j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let c = CONJUNCTS th in
    let abl = hd c and wdef = last c in
    let th10 = end_itlist CONJ (butlast c) in
    let defs = tl (butlast c) in
    SUBST1_TAC wdef THEN ASSUME_TAC abl THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F1 th10) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F2 th10) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F3 th10) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_ALPHA th10) THEN
    ASSUME_TAC(MATCH_MP MOI_FTP_AB_B th10) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_DISK th10) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE (map GSYM defs) (MATCH_MP MOI_FTP_AB_W abl)) THEN
    STRIP_ASSUME_TAC(REWRITE_RULE (map GSYM defs) (MATCH_MP MOI_FTP_AB_R abl))) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    (lhs(concl th) = `X:real^N->bool` || lhs(concl th) = `Y:real^N->bool`)))) THEN
  SUBGOAL_THEN
   `segment[m1:real^N,p1] INTER R1 = {p1} /\ segment[m1:real^N,q1] INTER R1 = {q1} /\
    segment[m2:real^N,p2] INTER R2 = {p2} /\ segment[m2:real^N,q2] INTER R2 = {q2} /\
    R1 INTER convex hull {m1:real^N,p1,q1} = segment[p1,q1] /\
    R2 INTER convex hull {m2:real^N,p2,q2} = segment[p2,q2] /\
    R1 INTER (G1 INTER Q') = R1 INTER (Q':real^N->bool) /\
    R2 INTER (G2 INTER Q') = R2 INTER (Q':real^N->bool) /\
    (m1:real^N) IN segment[m1,p1] /\ (p1:real^N) IN segment[m1,p1] /\
    (m1:real^N) IN segment[m1,q1] /\ (q1:real^N) IN segment[m1,q1] /\
    (m2:real^N) IN segment[m2,p2] /\ (p2:real^N) IN segment[m2,p2] /\
    (m2:real^N) IN segment[m2,q2] /\ (q2:real^N) IN segment[m2,q2]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    MP_TAC(ISPECL [`m1:real^N`; `p1:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`m1:real^N`; `q1:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`m2:real^N`; `p2:real^N`] ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`m2:real^N`; `q2:real^N`] ENDS_IN_SEGMENT) THEN
    MAP_EVERY UNDISCH_TAC
     [`(R1:real^N->bool) INTER As = {p1}`; `(R1:real^N->bool) INTER AF = {q1}`;
      `(R2:real^N->bool) INTER As = {p2}`; `(R2:real^N->bool) INTER AF = {q2}`;
      `(G1:real^N->bool) INTER As = segment[m1,p1]`;
      `(G1:real^N->bool) INTER AF = segment[m1,q1]`;
      `(G2:real^N->bool) INTER As = segment[m2,p2]`;
      `(G2:real^N->bool) INTER AF = segment[m2,q2]`;
      `(R1:real^N->bool) SUBSET G1`; `(R2:real^N->bool) SUBSET G2`;
      `(G1:real^N->bool) INTER Q = convex hull {m1,p1,q1}`;
      `(G2:real^N->bool) INTER Q = convex hull {m2,p2,q2}`;
      `(R1:real^N->bool) INTER Q = segment[p1,q1]`;
      `(R2:real^N->bool) INTER Q = segment[p2,q2]`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `YQ = Y INTER moi_ftc_cone (v:real^N) Q` THEN
  ABBREV_TAC `YQ' = Y INTER moi_ftc_cone (v:real^N) Q'` THEN
  ABBREV_TAC `YS = Y INTER moi_ftc_cone (v:real^N) As` THEN
  ABBREV_TAC `YF = Y INTER moi_ftc_cone (v:real^N) AF` THEN
  ABBREV_TAC `YJ = Y INTER moi_ftc_cone (v:real^N) J` THEN
  ABBREV_TAC `XQ = X INTER moi_ftc_cone (v:real^N) Q` THEN
  ABBREV_TAC `XQ' = X INTER moi_ftc_cone (v:real^N) Q'` THEN
  ABBREV_TAC `XS = X INTER moi_ftc_cone (v:real^N) As` THEN
  ABBREV_TAC `XF = X INTER moi_ftc_cone (v:real^N) AF` THEN
  ABBREV_TAC `TT = Z INTER moi_ftc_cone (v:real^N) Q` THEN
  ABBREV_TAC `ZQ' = Z INTER moi_ftc_cone (v:real^N) Q'` THEN
  ABBREV_TAC `AL = Z INTER moi_ftc_cone (v:real^N) As` THEN
  ABBREV_TAC `BE = Z INTER moi_ftc_cone (v:real^N) AF` THEN
  ABBREV_TAC `ZJ = Z INTER moi_ftc_cone (v:real^N) J` THEN
  ABBREV_TAC `ZF = Z UNION (Fg:real^N->bool)` THEN
  ABBREV_TAC `KK = segment[v:real^N,m1] UNION segment[v,m2]` THEN
  ABBREV_TAC `H1 = convex hull {m1:real^N,p1,q1}` THEN
  ABBREV_TAC `H2 = convex hull {m2:real^N,p2,q2}` THEN
  ABBREV_TAC `s1p = segment[m1:real^N,p1]` THEN
  ABBREV_TAC `s1q = segment[m1:real^N,q1]` THEN
  ABBREV_TAC `s2p = segment[m2:real^N,p2]` THEN
  ABBREV_TAC `s2q = segment[m2:real^N,q2]` THEN
  ABBREV_TAC `t1 = segment[p1:real^N,q1]` THEN
  ABBREV_TAC `t2 = segment[p2:real^N,q2]` THEN
  ABBREV_TAC `GQ1 = G1 INTER (Q':real^N->bool)` THEN
  ABBREV_TAC `GQ2 = G2 INTER (Q':real^N->bool)` THEN
  ABBREV_TAC `K1 = R1 INTER (Q':real^N->bool)` THEN
  ABBREV_TAC `K2 = R2 INTER (Q':real^N->bool)` THEN
  GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o GEN_REWRITE_RULE I [MOI_FTC_LT9]) THEN
  REWRITE_TAC[MOI_FTC_ZD_BD] THEN REWRITE_TAC[moi_ftc_zd; moi_ftc_dd] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[UNION_EMPTY; INTER_EMPTY] THENL
   [CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`YQ:real^N->bool`; `XQ UNION YJ:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`XQ = TT UNION H1 UNION (H2:real^N->bool)`; `YJ = YS UNION (YF:real^N->bool)`; `ZF INTER YQ = (TT:real^N->bool)`; `KK SUBSET (YS:real^N->bool)`; `G1 INTER YQ = (H1:real^N->bool)`; `G2 INTER YQ = (H2:real^N->bool)`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`H1:real^N->bool`; `(s1p UNION s1q) UNION t1:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `G1 INTER YQ = (H1:real^N->bool)`; `R1 INTER H1 = (t1:real^N->bool)`; `G1 INTER KK = {m1:real^N}`; `s1p INTER R1 = {p1:real^N}`; `s1q INTER R1 = {q1:real^N}`; `(m1:real^N) IN s1p`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`YQ':real^N->bool`; `XQ' UNION YJ:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`XQ' = ZQ' UNION GQ1 UNION GQ2 UNION (Fg:real^N->bool)`; `YJ = YS UNION (YF:real^N->bool)`; `ZF INTER YQ' = ZQ' UNION (Fg:real^N->bool)`; `KK SUBSET (YS:real^N->bool)`; `G1 INTER YQ' = (GQ1:real^N->bool)`; `G2 INTER YQ' = (GQ2:real^N->bool)`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`GQ1:real^N->bool`; `(s1p UNION s1q) UNION K1:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `G1 INTER YQ' = (GQ1:real^N->bool)`; `R1 INTER GQ1 = (K1:real^N->bool)`; `G1 INTER KK = {m1:real^N}`; `s1p INTER R1 = {p1:real^N}`; `s1q INTER R1 = {q1:real^N}`; `(m1:real^N) IN s1p`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`YS:real^N->bool`; `XS UNION KK:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`XS = AL UNION s1p UNION (s2p:real^N->bool)`; `YS INTER ZF = (AL:real^N->bool)`; `G1 INTER YS = (s1p:real^N->bool)`; `G2 INTER YS = (s2p:real^N->bool)`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`s1p:real^N->bool`; `{m1:real^N,p1}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER KK = {m1:real^N}`; `G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1p INTER R1 = {p1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`YF:real^N->bool`; `XF UNION KK:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`XF = BE UNION s1q UNION (s2q:real^N->bool)`; `YF INTER ZF = (BE:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `G2 INTER YF = (s2q:real^N->bool)`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`s1q:real^N->bool`; `{m1:real^N,q1}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER KK = {m1:real^N}`; `G1 INTER YF = (s1q:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1q INTER R1 = {q1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`TT:real^N->bool`; `ZJ UNION t1 UNION t2:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`ZF INTER YQ = (TT:real^N->bool)`; `YS INTER ZF = (AL:real^N->bool)`; `YF INTER ZF = (BE:real^N->bool)`; `AL UNION BE = (ZJ:real^N->bool)`; `TT INTER G1 = (t1:real^N->bool)`; `TT INTER G2 = (t2:real^N->bool)`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`t1:real^N->bool`; `{p1:real^N,q1}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER ZF = (R1:real^N->bool)`; `G1 INTER YQ = (H1:real^N->bool)`; `R1 INTER H1 = (t1:real^N->bool)`; `G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `s1p INTER R1 = {p1:real^N}`; `s1q INTER R1 = {q1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`ZQ' UNION Fg:real^N->bool`; `ZJ UNION K1 UNION K2:real^N->bool`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`ZF INTER YQ' = ZQ' UNION (Fg:real^N->bool)`; `YS INTER ZF = (AL:real^N->bool)`; `YF INTER ZF = (BE:real^N->bool)`; `AL UNION BE = (ZJ:real^N->bool)`; `ZQ' INTER G1 = (K1:real^N->bool)`; `ZQ' INTER G2 = (K2:real^N->bool)`; `Fg INTER G1 = {}:real^N->bool`; `Fg INTER G2 = {}:real^N->bool`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`K1:real^N->bool`; `{p1:real^N,q1}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER ZF = (R1:real^N->bool)`; `G1 INTER YQ' = (GQ1:real^N->bool)`; `R1 INTER GQ1 = (K1:real^N->bool)`; `G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `s1p INTER R1 = {p1:real^N}`; `s1q INTER R1 = {q1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`KK:real^N->bool`; `{m1:real^N,m2}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER KK = {m1:real^N}`; `G2 INTER KK = {m2:real^N}`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`{m1:real^N}`; `{}:real^N->bool`] THEN
        REWRITE_TAC[MOI_FCL_POINT_CELL] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER KK = {m1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`AL:real^N->bool`; `{p1:real^N,p2}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`YS INTER ZF = (AL:real^N->bool)`; `G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1p INTER R1 = {p1:real^N}`; `G2 INTER YS = (s2p:real^N->bool)`; `G2 INTER ZF = (R2:real^N->bool)`; `s2p INTER R2 = {p2:real^N}`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`{p1:real^N}`; `{}:real^N->bool`] THEN
        REWRITE_TAC[MOI_FCL_POINT_CELL] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER YS = (s1p:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1p INTER R1 = {p1:real^N}`] THEN SET_TAC[]];
    CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`BE:real^N->bool`; `{q1:real^N,q2}`] THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`YF INTER ZF = (BE:real^N->bool)`; `G1 INTER YF = (s1q:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1q INTER R1 = {q1:real^N}`; `G2 INTER YF = (s2q:real^N->bool)`; `G2 INTER ZF = (R2:real^N->bool)`; `s2q INTER R2 = {q2:real^N}`] THEN SET_TAC[];
       MATCH_MP_TAC MOI_FTC_CELL_EQ THEN
        MAP_EVERY EXISTS_TAC [`{q1:real^N}`; `{}:real^N->bool`] THEN
        REWRITE_TAC[MOI_FCL_POINT_CELL] THEN
        MAP_EVERY UNDISCH_TAC [`G1 INTER YF = (s1q:real^N->bool)`; `G1 INTER ZF = (R1:real^N->bool)`; `s1q INTER R1 = {q1:real^N}`] THEN SET_TAC[]]]);;

(* ========================================================================= *)
(* The level picture of block v as an abstract block.  With                 *)
(* the level homeomorphism h of the stars of V (moi_ftc_lev), Y = h(C_v),   *)
(* Z = h(C_v INTER Fr), G1 = h(C_v INTER C_u), G2 = h(C_v INTER C_u'),      *)
(* Fg = h(fingers at v) form a moi_ftp_abl configuration at v; the six      *)
(* basic sets of the cell structure have images Y INTER cone Q etc.          *)
(* ========================================================================= *)

(* The simplices of sd t at the wedge of block v. *)


(* ========================================================================= *)
(* The level picture at a polygon vertex v.  The vertices of                *)
(* the link of v in t' = sd t that lie on the graph are the midpoints of    *)
(* the edges of l at v (MOI_FTP_LINK_VERT); hence, by the level             *)
(* homeomorphism h of tubec, the level region Y = h(C_v) and its frontier  *)
(* part Z meet every link triangle in the level sets of an affine function  *)
(* with weights 1 at the midpoints m1, m2 of the two polygon edges at v and *)
(* 0 elsewhere (MOI_FTP_VLEVEL), the hypothesis of MOI_FTP_CORRIDOR.        *)
(* ========================================================================= *)

let MOI_FTP_LINK_VERT = prove
 (`!(t:(real^N->bool)->bool) l v S x.
     graph_in_complex t l /\ {v} IN l /\
     S IN simplicial_link (barycentric_subdivision t) v /\ x extreme_point_of S
     ==> (x IN UNIONS l <=> ?w. ~(w = v) /\ segment[v,w] IN l /\ x = midpoint(v,w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FTA_SETUP o
    (fun th -> CONJ th (ASSUME `{v:real^N} IN l`))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  UNDISCH_TAC `S IN simplicial_link (barycentric_subdivision t) (v:real^N)` THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `T0:real^N->bool` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `T0 IN barycentric_subdivision (t:(real^N->bool)->bool)` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `f:(real^N->bool)->bool`; `v:real^N`]
    MOI_FTA_VERTEX_IN_HULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) extreme_point_of convex hull (IMAGE simplex_barycentre f)`
  MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o MATCH_MP EXTREME_POINT_OF_FACE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `f:(real^N->bool)->bool`; `x:real^N`]
    MOI_FTA_BS_EXTREME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN S` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [extreme_point_of] o check (fun th ->
      concl th = `(x:real^N) extreme_point_of S`)) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN t /\ ~(s = {}) /\ (v:real^N) IN s /\ ~(s = {v})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (t:(real^N->bool)->bool) f` THEN
    REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `(x:real^N) = simplex_barycentre s` THEN
      ASM_REWRITE_TAC[MOI_FTA_BARY_SING] THEN DISCH_TAC THEN
      UNDISCH_TAC `(x:real^N) IN S` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) IN l` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `s:real^N->bool`]
        MOI_FCL_BARY_IN_L) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS l` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?w:real^N. w extreme_point_of s /\ ~(w = v)` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `!w:real^N. w extreme_point_of s ==> w = v` ASSUME_TAC THENL
       [UNDISCH_TAC `~(?w:real^N. w extreme_point_of s /\ ~(w = v))` THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [lf_simplicial_complex] o
          check (fun th -> concl th = `lf_simplicial_complex (t:(real^N->bool)->bool)`)) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPEC `s:real^N->bool` KREIN_MILMAN_MINKOWSKI) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; DISCH_TAC] THEN
      SUBGOAL_THEN `{y:real^N | y extreme_point_of s} SUBSET {v}` ASSUME_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(s = {v:real^N})` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[SING_SUBSET] THEN
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [th]) o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `s:real^N->bool`)) THEN
      MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[CONVEX_SING];
      ALL_TAC] THEN
    SUBGOAL_THEN `{w:real^N} IN t` ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o
        GEN_REWRITE_RULE I [lf_simplicial_complex] o
          check (fun th -> concl th = `lf_simplicial_complex (t:(real^N->bool)->bool)`)) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `s:real^N->bool`;
                   `v:real^N`; `w:real^N`] MOI_FTA_GRAPH_TWO_VERTICES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(ACCEPT_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [extreme_point_of] o
        check (fun th -> concl th = `(w:real^N) extreme_point_of s`));
      DISCH_THEN SUBST_ALL_TAC] THEN
    EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) = simplex_barycentre (segment[v,w])` THEN
    REWRITE_TAC[MOI_FTA_BARY_SEGMENT];
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[v:real^N,w]` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `(x:real^N) = midpoint(v,w)`)) THEN
    REWRITE_TAC[MIDPOINT_IN_SEGMENT]]);;

(* The level hypothesis of MOI_FTP_CORRIDOR at a polygon vertex v of degree *)
(* two, with neighbours u and u'.                                           *)

let MOI_FTP_VLEVEL = prove
 (`!(t:(real^N->bool)->bool) l V h k v u u'.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ v IN V /\ {v} IN l /\
     (!w. ~(w = v) /\ segment[v,w] IN l <=> w = u \/ w = u')
     ==> !S. S IN simplicial_link (barycentric_subdivision t) v /\ aff_dim S = &2
             ==> ?f. (!x y c. f((&1 - c) % x + c % y) = (&1 - c) * f x + c * f y) /\
                     (!x. x extreme_point_of S
                          ==> f x = moi_ftp_w {midpoint(v,u), midpoint(v,u')} x) /\
                     IMAGE h (derived_dual_cell t l v) INTER S =
                     {x | x IN S /\ &1 / &2 <= f x} /\
                     IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) INTER S =
                     {x | x IN S /\ f x = &1 / &2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `S:real^N->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    can (find_term ((=) `simplicial_link:((real^N->bool)->bool)->real^N->(real^N->bool)->bool`))
      (concl th))) THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `T0:real^N->bool` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`v:real^N`; `T0:real^N->bool`] o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [moi_ftc_lev] o check (fun th -> is_comb(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "moi_ftc_lev" with Failure _ -> false))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^N->real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(S:real^N->bool) SUBSET T0` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) extreme_point_of T0` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o MATCH_MP EXTREME_POINT_OF_FACE o check
        (fun th -> concl th = `(S:real^N->bool) face_of T0`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^N) extreme_point_of T0`)])
      o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "extreme_point_of"
                                 with Failure _ -> false)) (concl th))) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                   `S:real^N->bool`; `x:real^N`] MOI_FTP_LINK_VERT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[moi_ftp_w; IN_INSERT; NOT_IN_EMPTY] THEN
    SUBGOAL_THEN `(?w. ~(w = v) /\ segment[v,w] IN l /\ (x:real^N) = midpoint(v,w)) <=>
                  x = midpoint(v,u) \/ x = midpoint(v,u')` ASSUME_TAC THENL
     [REWRITE_TAC[CONJ_ASSOC] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `u':real^N`)) (concl th))) THEN
      MESON_TAC[];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN S` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^N) IN T0` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN S` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^N) IN T0` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

(* The level picture at a polygon vertex v of degree two (neighbours u, u'):*)
(* Y = h(C_v) is radial over the link sphere L, and meets L in the two      *)
(* dual disks G1 = h(C_v INTER C_u), G2 = h(C_v INTER C_u') (no fingers).   *)

let MOI_FTP_VPIC_BASE = prove
 (`!(t:(real^N->bool)->bool) l V h k v u u' L X Y Z G1 G2 R1 R2.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ v IN V /\ u IN V /\ u' IN V /\
     ~(u = v) /\ ~(u' = v) /\ ~(u = u') /\ segment[v,u] IN l /\ segment[v,u'] IN l /\
     (!w. ~(w = v) /\ segment[v,w] IN l <=> w = u \/ w = u') /\
     L = UNIONS (simplicial_link (barycentric_subdivision t) v) /\
     Y = IMAGE h (derived_dual_cell t l v) /\
     Z = IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) /\
     X = Z UNION (Y INTER L) /\
     G1 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u) /\
     G2 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u') /\
     R1 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u INTER
                   derived_frontier t l) /\
     R2 = IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u' INTER
                   derived_frontier t l)
     ==> moi_ftc_rad v L X Y /\ Z SUBSET Y /\
         pl_cell_with_boundary 2 G1 R1 /\ pl_cell_with_boundary 2 G2 R2 /\
         Y INTER L = G1 UNION G2 /\ G1 INTER G2 = {} /\
         Z INTER G1 = R1 /\ Z INTER G2 = R2 /\
         G1 = Y INTER IMAGE h (derived_dual_cell t l u) /\
         G2 = Y INTER IMAGE h (derived_dual_cell t l u') /\
         Y INTER IMAGE h (derived_dual_cell t l u) INTER
         IMAGE h (derived_dual_cell t l u') = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) &&
    mem (fst(dest_var(lhs(concl th)))) ["L"; "Y"; "Z"; "X"; "G1"; "G2"; "R1"; "R2"]))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`]
    MOI_FTA_SEG_VERTS) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:(real^N->bool)->bool`; `v:real^N`; `u':real^N`]
    MOI_FTA_SEG_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY (fun w ->
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; w] MOI_FTC_LEV_BASICS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC])
   [`v:real^N`; `u:real^N`; `u':real^N`] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`] MOI_FTC_HRAD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ABBREV_TAC `U = UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))` THEN
  ABBREV_TAC `Fr = derived_frontier t (l:(real^N->bool)->bool)` THEN
  ABBREV_TAC `Cv = derived_dual_cell t l (v:real^N)` THEN
  ABBREV_TAC `Cu = derived_dual_cell t l (u:real^N)` THEN
  ABBREV_TAC `Cu' = derived_dual_cell t l (u':real^N)` THEN
  SUBGOAL_THEN
   `(Cv:real^N->bool) SUBSET U /\ (Cu:real^N->bool) SUBSET U /\ (Cu':real^N->bool) SUBSET U /\
    (L:real^N->bool) SUBSET U`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (v:real^N) IN s}` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    TRY(MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (u:real^N) IN s}` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (u':real^N) IN s}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!A B:real^N->bool. A SUBSET U /\ B SUBSET U
                ==> IMAGE (h:real^N->real^N) A INTER IMAGE h B = IMAGE h (A INTER B)`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cv INTER Cu INTER (Cu':real^N->bool) = {}` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Cv"; "Cu"; "Cu'"] THEN MATCH_MP_TAC MOI_FTC_TRIPLE THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `Cv INTER (L:real^N->bool) = (Cv INTER Cu) UNION (Cv INTER Cu')` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_WALLS_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `{Cv INTER derived_dual_cell t l w | w | w = u \/ w = (u':real^N)} =
                  {Cv INTER Cu, Cv INTER (Cu':real^N->bool)}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      MAP_EVERY UNDISCH_TAC [`derived_dual_cell t l (u:real^N) = Cu`;
                             `derived_dual_cell t l (u':real^N) = Cu'`] THEN
      MESON_TAC[];
      REWRITE_TAC[UNIONS_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 G1 (R1:real^N->bool) /\
                pl_cell_with_boundary 2 G2 (R2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `u:real^N`] MOI_FTA_CELL2) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `u:real^N`] MOI_FTA_DISK_POLY);
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `u':real^N`] MOI_FTA_CELL2) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`;
                     `u':real^N`] MOI_FTA_DISK_POLY)] THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `IMAGE (h:real^N->real^N) (Cv INTER Cu) = G1`)) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `IMAGE (h:real^N->real^N) (Cv INTER Cu INTER Fr) = R1`));
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `IMAGE (h:real^N->real^N) (Cv INTER Cu') = G2`)) THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
        `IMAGE (h:real^N->real^N) (Cv INTER Cu' INTER Fr) = R2`))] THEN
    (MATCH_MP_TAC MOI_FTA_CELL_PLH THEN EXISTS_TAC `k:real^N->real^N` THEN
     CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN
     EXISTS_TAC `U:real^N->bool` THEN EXISTS_TAC `U:real^N->bool` THEN
     ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN ASM SET_TAC[]);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(Cv INTER Fr:real^N->bool) SUBSET U /\ Cv INTER (Cu:real^N->bool) SUBSET U /\
                Cv INTER (Cu':real^N->bool) SUBSET U /\ Cu INTER (Cu':real^N->bool) SUBSET U`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun c -> FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = c)))
   [`IMAGE (h:real^N->real^N) Cv = Y`; `IMAGE (h:real^N->real^N) (Cv INTER Fr) = Z`;
    `IMAGE (h:real^N->real^N) (Cv INTER Cu) = G1`;
    `IMAGE (h:real^N->real^N) (Cv INTER Cu') = G2`;
    `IMAGE (h:real^N->real^N) (Cv INTER Cu INTER Fr) = R1`;
    `IMAGE (h:real^N->real^N) (Cv INTER Cu' INTER Fr) = R2`] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC ONCE_DEPTH_CONV [SYM th]) o check (fun th ->
    concl th = `IMAGE (h:real^N->real^N) L = L`)) THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N) {} = {}` (LABEL_TAC "e0") THENL
   [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    REWRITE_TAC[GSYM IMAGE_UNION] THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
    USE_THEN "e0" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `Cv INTER Cu INTER (Cu':real^N->bool) = {}` THEN SET_TAC[];
    MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `IMAGE (h:real^N->real^N) Cu INTER IMAGE h Cu' = IMAGE h (Cu INTER Cu')`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
      MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "e0" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC MOI_FTC_IMAGE_INTER_EQ THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->real^N`; `U:real^N->bool`] THEN ASM_REWRITE_TAC[]]);;

(* A kite at the polygon edge [v,w]: m = midpoint(v,w), the barycentres of  *)
(* a triangle conv{v,w,y} and a tetrahedron conv{v,w,y,x} of t (in either   *)
(* order as cS, cF).  It is a triangle of the links of v and w in sd t; the *)
(* level regions of v and of w both meet it in its corner at m.            *)

let MOI_FTP_KITE_FACTS = prove
 (`!(t:(real^N->bool)->bool) l V h k v w y x cS cF.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ v IN V /\ w IN V /\
     segment[v,w] IN l /\ moi_ftc_blk t v w y x /\
     ((cS = simplex_barycentre(convex hull {v,w,y}) /\
       cF = simplex_barycentre(convex hull {v,w,y,x})) \/
      (cS = simplex_barycentre(convex hull {v,w,y,x}) /\
       cF = simplex_barycentre(convex hull {v,w,y})))
     ==> convex hull {midpoint(v,w),cS,cF} IN simplicial_link (barycentric_subdivision t) v /\
         ~collinear {midpoint(v,w),cS,cF} /\ ~affine_dependent {midpoint(v,w),cS,cF} /\
         ~(midpoint(v,w) = cS) /\ ~(midpoint(v,w) = cF) /\ ~(cS = cF) /\
         IMAGE h (derived_dual_cell t l v) INTER convex hull {midpoint(v,w),cS,cF} =
         convex hull {midpoint(v,w),midpoint(midpoint(v,w),cS),midpoint(midpoint(v,w),cF)} /\
         IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) INTER
         convex hull {midpoint(v,w),cS,cF} =
         segment[midpoint(midpoint(v,w),cS),midpoint(midpoint(v,w),cF)] /\
         IMAGE h (derived_dual_cell t l w) INTER convex hull {midpoint(v,w),cS,cF} =
         convex hull {midpoint(v,w),midpoint(midpoint(v,w),cS),midpoint(midpoint(v,w),cF)}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  ABBREV_TAC `m = midpoint(v:real^N,w)` THEN
  ABBREV_TAC `bs = simplex_barycentre(convex hull {v:real^N,w,y})` THEN
  ABBREV_TAC `b1 = simplex_barycentre(convex hull {v:real^N,w,y,x})` THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `w:real^N`; `y:real^N`; `x:real^N`;
                 `m:real^N`; `midpoint(v:real^N,y)`; `bs:real^N`; `b1:real^N`]
    MOI_FTC_BLK_SD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`; `w:real^N`; `y:real^N`;
                 `x:real^N`] MOI_FTC_LEV_CORNER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `w:real^N`; `v:real^N`; `y:real^N`;
                 `x:real^N`] MOI_FTC_LEV_CORNER) THEN
  SUBGOAL_THEN `midpoint(w:real^N,v) = m /\
                simplex_barycentre(convex hull {w:real^N,v,y}) = bs /\
                simplex_barycentre(convex hull {w:real^N,v,y,x}) = b1 /\
                segment[w:real^N,v] IN l /\ moi_ftc_blk t w v y x`
  (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["m"; "bs"; "b1"] THEN
    SUBGOAL_THEN `{w:real^N,v,y} = {v,w,y} /\ {w:real^N,v,y,x} = {v,w,y,x}`
    (fun th -> REWRITE_TAC[th]) THENL [SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MIDPOINT_SYM];
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FTC_BLK_PERM) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(m:real^N = bs) /\ ~(m:real^N = b1) /\ ~(bs:real^N = b1) /\
                ~affine_dependent {m:real^N,bs,b1}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear {m:real^N,bs,b1}` THEN
    REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{m:real^N,b1,bs} = {m,bs,b1} /\
    {m:real^N,midpoint(m,b1),midpoint(m,bs)} = {m,midpoint(m,bs),midpoint(m,b1)} /\
    segment[midpoint(m:real^N,b1),midpoint(m,bs)] = segment[midpoint(m,bs),midpoint(m,b1)]`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]);;

(* No simplex of sd t contains the midpoints of two different edges at v. *)

let MOI_FTP_TWO_MID = prove
 (`!(t:(real^N->bool)->bool) v u u' S.
     lf_simplicial_complex t /\ segment[v,u] IN t /\ segment[v,u'] IN t /\
     ~(v = u) /\ ~(v = u') /\ ~(u = u') /\ {u} IN t /\ {u'} IN t /\
     S IN barycentric_subdivision t
     ==> ~(midpoint(v,u) IN S /\ midpoint(v,u') IN S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  UNDISCH_TAC `S IN barycentric_subdivision (t:(real^N->bool)->bool)` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w:real^N. segment[v,w] IN t /\
                           midpoint(v,w) IN convex hull (IMAGE simplex_barycentre f)
                           ==> segment[v,w] IN f`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `{segment[v:real^N,w]}`;
                   `f:(real^N->bool)->bool`; `midpoint(v:real^N,w)`] MOI_FTA_RI_SUBCHAIN) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; RELATIVE_INTERIOR_SING; IN_SING;
                    MOI_FTA_BARY_SEGMENT; SING_SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN
    ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,u] IN f /\ segment[v:real^N,u'] IN f` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`segment[v:real^N,u]`; `segment[v:real^N,u']`] o
    CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [moi_bar_chain]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(u:real^N) extreme_point_of segment[v,u']` MP_TAC THENL
     [MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `segment[v:real^N,u] SUBSET segment[v,u']` THEN
      MP_TAC(ISPECL [`v:real^N`; `u:real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN ASM_MESON_TAC[]];
    SUBGOAL_THEN `(u':real^N) extreme_point_of segment[v,u]` MP_TAC THENL
     [MATCH_MP_TAC MOI_FTA_VERTEX_EXTREME THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `segment[v:real^N,u'] SUBSET segment[v,u]` THEN
      MP_TAC(ISPECL [`v:real^N`; `u':real^N`] ENDS_IN_SEGMENT) THEN SET_TAC[];
      REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN ASM_MESON_TAC[]]]);;

(* Set bookkeeping for the corner facts of the vertex block. *)

let MOI_FTP_VBLK_SETS = prove
 (`!Y Z A A' Q As AF H1 H2 S1 S2 T1 T2 E1 E2 R1 R2 K1 K2:real^N->bool.
     Y INTER Q = H1 UNION H2 /\ Y INTER As = S1 UNION S2 /\ Y INTER AF = T1 UNION T2 /\
     Z INTER Q = E1 UNION E2 /\ Y INTER A INTER A' = {} /\ A INTER K1 = H1 /\
     A' INTER K2 = H2 /\
     S1 SUBSET H1 /\ T1 SUBSET H1 /\ E1 SUBSET H1 /\
     S2 SUBSET H2 /\ T2 SUBSET H2 /\ E2 SUBSET H2 /\
     Z INTER (Y INTER A) = R1 /\ Z INTER (Y INTER A') = R2
     ==> (Y INTER A) INTER Q = H1 /\ (Y INTER A') INTER Q = H2 /\
         (Y INTER A) INTER As = S1 /\ (Y INTER A) INTER AF = T1 /\
         (Y INTER A') INTER As = S2 /\ (Y INTER A') INTER AF = T2 /\
         R1 INTER Q = E1 /\ R2 INTER Q = E2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(H1:real^N->bool) SUBSET Y INTER A /\ (H2:real^N->bool) SUBSET Y INTER A' /\
                A INTER (H2:real^N->bool) = {} /\ A' INTER (H1:real^N->bool) = {}`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(Y:real^N->bool) INTER Q = H1 UNION H2`; `(Y:real^N->bool) INTER A INTER A' = {}`;
      `(A:real^N->bool) INTER K1 = H1`; `(A':real^N->bool) INTER K2 = H2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(Y:real^N->bool) INTER Q = H1 UNION H2`;
      `(H1:real^N->bool) SUBSET Y INTER A`; `(A:real^N->bool) INTER H2 = {}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Y:real^N->bool) INTER Q = H1 UNION H2`;
      `(H2:real^N->bool) SUBSET Y INTER A'`; `(A':real^N->bool) INTER H1 = {}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Y:real^N->bool) INTER As = S1 UNION S2`;
      `(S1:real^N->bool) SUBSET H1`; `(S2:real^N->bool) SUBSET H2`;
      `(H1:real^N->bool) SUBSET Y INTER A`; `(A:real^N->bool) INTER H2 = {}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Y:real^N->bool) INTER AF = T1 UNION T2`;
      `(T1:real^N->bool) SUBSET H1`; `(T2:real^N->bool) SUBSET H2`;
      `(H1:real^N->bool) SUBSET Y INTER A`; `(A:real^N->bool) INTER H2 = {}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Y:real^N->bool) INTER As = S1 UNION S2`;
      `(S1:real^N->bool) SUBSET H1`; `(S2:real^N->bool) SUBSET H2`;
      `(H2:real^N->bool) SUBSET Y INTER A'`; `(A':real^N->bool) INTER H1 = {}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Y:real^N->bool) INTER AF = T1 UNION T2`;
      `(T1:real^N->bool) SUBSET H1`; `(T2:real^N->bool) SUBSET H2`;
      `(H2:real^N->bool) SUBSET Y INTER A'`; `(A':real^N->bool) INTER H1 = {}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Z:real^N->bool) INTER Q = E1 UNION E2`;
      `(Z:real^N->bool) INTER (Y INTER A) = R1`;
      `(E1:real^N->bool) SUBSET H1`; `(E2:real^N->bool) SUBSET H2`;
      `(H1:real^N->bool) SUBSET Y INTER A`; `(A:real^N->bool) INTER H2 = {}`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC [`(Z:real^N->bool) INTER Q = E1 UNION E2`;
      `(Z:real^N->bool) INTER (Y INTER A') = R2`;
      `(E1:real^N->bool) SUBSET H1`; `(E2:real^N->bool) SUBSET H2`;
      `(H2:real^N->bool) SUBSET Y INTER A'`; `(A':real^N->bool) INTER H1 = {}`] THEN SET_TAC[]]);;

(* The block at a polygon vertex v (neighbours u, u', kites at the two      *)
(* polygon edges, labelled by the determinant signs): the generalized       *)
(* abstract block with the corridor of MOI_FTP_CORRIDOR as the trace Q.     *)

let MOI_FTP_VBLK = prove
 (`!(t:(real^3->bool)->bool) l V h k v u u' y1 x1 y2 x2 cS1 cF1 cS2 cF2.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ v IN V /\ u IN V /\ u' IN V /\
     ~(u = v) /\ ~(u' = v) /\ ~(u = u') /\ segment[v,u] IN l /\ segment[v,u'] IN l /\
     (!w. ~(w = v) /\ segment[v,w] IN l <=> w = u \/ w = u') /\
     moi_ftc_blk t v u y1 x1 /\ moi_ftc_blk t v u' y2 x2 /\
     ((cS1 = simplex_barycentre(convex hull {v,u,y1}) /\
       cF1 = simplex_barycentre(convex hull {v,u,y1,x1})) \/
      (cS1 = simplex_barycentre(convex hull {v,u,y1,x1}) /\
       cF1 = simplex_barycentre(convex hull {v,u,y1}))) /\
     ((cS2 = simplex_barycentre(convex hull {v,u',y2}) /\
       cF2 = simplex_barycentre(convex hull {v,u',y2,x2})) \/
      (cS2 = simplex_barycentre(convex hull {v,u',y2,x2}) /\
       cF2 = simplex_barycentre(convex hull {v,u',y2}))) /\
     &0 < det(vector[cS1 - v; cF1 - v; midpoint(v,u) - v]) /\
     det(vector[cS2 - v; cF2 - v; midpoint(v,u') - v]) < &0 /\
     ~(aff_dim(convex hull {midpoint(v,u),cS1,cF1} INTER
               convex hull {midpoint(v,u'),cS2,cF2}) = &1)
     ==> ?Q As AF bs b1.
           moi_ftp_abl v (UNIONS (simplicial_link (barycentric_subdivision t) v))
             (IMAGE h (derived_dual_cell t l v INTER derived_frontier t l) UNION
              (IMAGE h (derived_dual_cell t l v) INTER
               UNIONS (simplicial_link (barycentric_subdivision t) v)))
             (IMAGE h (derived_dual_cell t l v))
             (IMAGE h (derived_dual_cell t l v INTER derived_frontier t l))
             (midpoint(v,u)) (midpoint(v,u'))
             (midpoint(midpoint(v,u),cS1)) (midpoint(midpoint(v,u),cF1))
             (midpoint(midpoint(v,u'),cS2)) (midpoint(midpoint(v,u'),cF2))
             bs b1 Q As AF
             (IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u))
             (IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u'))
             (IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u INTER
                       derived_frontier t l))
             (IMAGE h (derived_dual_cell t l v INTER derived_dual_cell t l u' INTER
                       derived_frontier t l))
             {}`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `V:real^3->bool`;
                 `h:real^3->real^3`; `k:real^3->real^3`; `v:real^3`; `u:real^3`; `y1:real^3`;
                 `x1:real^3`; `cS1:real^3`; `cF1:real^3`] MOI_FTP_KITE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `V:real^3->bool`;
                 `h:real^3->real^3`; `k:real^3->real^3`; `v:real^3`; `u':real^3`; `y2:real^3`;
                 `x2:real^3`; `cS2:real^3`; `cF2:real^3`] MOI_FTP_KITE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `V:real^3->bool`;
                 `h:real^3->real^3`; `k:real^3->real^3`; `v:real^3`; `u:real^3`; `u':real^3`;
                 `UNIONS (simplicial_link (barycentric_subdivision t) (v:real^3))`;
                 `IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_frontier t l)
                  UNION (IMAGE h (derived_dual_cell t l v) INTER
                         UNIONS (simplicial_link (barycentric_subdivision t) v))`;
                 `IMAGE (h:real^3->real^3) (derived_dual_cell t l v)`;
                 `IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_frontier t l)`;
                 `IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_dual_cell t l u)`;
                 `IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_dual_cell t l u')`;
                 `IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_dual_cell t l u INTER
                                          derived_frontier t l)`;
                 `IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_dual_cell t l u' INTER
                                          derived_frontier t l)`] MOI_FTP_VPIC_BASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `V:real^3->bool`;
                 `h:real^3->real^3`; `k:real^3->real^3`; `v:real^3`; `u:real^3`; `u':real^3`]
    MOI_FTP_VLEVEL) THEN
  SUBGOAL_THEN `{v:real^3} IN l /\ {u:real^3} IN l /\ {u':real^3} IN l` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex] o check (fun th ->
      is_comb(concl th) && fst(strip_comb(concl th)) = `graph_in_complex:((real^3->bool)->bool)->((real^3->bool)->bool)->bool`)) THEN
    ASM_MESON_TAC[MOI_FTA_SEG_VERTS];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC `L = UNIONS (simplicial_link (barycentric_subdivision t) (v:real^3))` THEN
  ABBREV_TAC `Y = IMAGE (h:real^3->real^3) (derived_dual_cell t l v)` THEN
  ABBREV_TAC `Z = IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_frontier t l)` THEN
  ABBREV_TAC `G1 = IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_dual_cell t l u)` THEN
  ABBREV_TAC `G2 = IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_dual_cell t l u')` THEN
  ABBREV_TAC `R1 = IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_dual_cell t l u INTER
                                           derived_frontier t l)` THEN
  ABBREV_TAC `R2 = IMAGE (h:real^3->real^3) (derived_dual_cell t l v INTER derived_dual_cell t l u' INTER
                                           derived_frontier t l)` THEN
  ABBREV_TAC `m1 = midpoint(v:real^3,u)` THEN ABBREV_TAC `m2 = midpoint(v:real^3,u')` THEN
  (* the corridor *)
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`; `v:real^3`;
                 `m1:real^3`; `cS1:real^3`; `cF1:real^3`; `m2:real^3`; `cS2:real^3`;
                 `cF2:real^3`; `Y:real^3->bool`; `Z:real^3->bool`] MOI_FTP_CORRIDOR) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `v:real^3`]
    MOI_FTP_POLY_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN REWRITE_TAC[midpoint] THEN
      UNDISCH_TAC `~(u:real^3 = u')` THEN CONV_TAC CONTRAPOS_CONV THEN
      REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      X_GEN_TAC `S:real^3->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `lf_simplicial_complex (t:(real^3->bool)->bool) /\
                    (l:(real^3->bool)->bool) SUBSET t` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `graph_in_complex (t:(real^3->bool)->bool) l` THEN
        SIMP_TAC[graph_in_complex; simplicial_subcomplex];
        ALL_TAC] THEN
      SUBGOAL_THEN `segment[v:real^3,u] IN t /\ segment[v:real^3,u'] IN t /\
                    {u:real^3} IN t /\ {u':real^3} IN t /\
                    S IN barycentric_subdivision (t:(real^3->bool)->bool)`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THEN
        TRY(FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
              concl th = `(l:(real^3->bool)->bool) SUBSET t`)) THEN
            FIRST_ASSUM ACCEPT_TAC) THEN
        UNDISCH_TAC `S IN simplicial_link (barycentric_subdivision t) (v:real^3)` THEN
        REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN SIMP_TAC[];
        ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["m1"; "m2"] THEN MATCH_MP_TAC MOI_FTP_TWO_MID THEN
      EXISTS_TAC `t:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:real^3->bool` (X_CHOOSE_THEN `As:real^3->bool`
    (X_CHOOSE_THEN `AF:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(Q:real^3->bool) SUBSET L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `bs:real^3` o REWRITE_RULE[SUBSET; NOT_FORALL_THM; NOT_IMP] o
    check (fun th -> concl th = `~((As:real^3->bool) SUBSET Y)`)) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `b1:real^3` o REWRITE_RULE[SUBSET; NOT_FORALL_THM; NOT_IMP] o
    check (fun th -> concl th = `~((AF:real^3->bool) SUBSET Y)`)) THEN
  MAP_EVERY EXISTS_TAC [`Q:real^3->bool`; `As:real^3->bool`; `AF:real^3->bool`;
                        `bs:real^3`; `b1:real^3`] THEN
  ABBREV_TAC `p1 = midpoint(m1:real^3,cS1)` THEN ABBREV_TAC `q1 = midpoint(m1:real^3,cF1)` THEN
  ABBREV_TAC `p2 = midpoint(m2:real^3,cS2)` THEN ABBREV_TAC `q2 = midpoint(m2:real^3,cF2)` THEN
  SUBGOAL_THEN
   `~collinear {m1:real^3,p1,q1} /\ ~collinear {m2:real^3,p2,q2} /\
    segment[m1:real^3,p1] SUBSET convex hull {m1,p1,q1} /\
    segment[m1:real^3,q1] SUBSET convex hull {m1,p1,q1} /\
    segment[p1:real^3,q1] SUBSET convex hull {m1,p1,q1} /\
    segment[m2:real^3,p2] SUBSET convex hull {m2,p2,q2} /\
    segment[m2:real^3,q2] SUBSET convex hull {m2,p2,q2} /\
    segment[p2:real^3,q2] SUBSET convex hull {m2,p2,q2}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`m1:real^3`; `cS1:real^3`; `cF1:real^3`] MOI_FTC_CORNER_GEOM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
      MP_TAC(ISPECL [`m2:real^3`; `cS2:real^3`; `cF2:real^3`] MOI_FTC_CORNER_GEOM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1);
      ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftp_abl; UNION_EMPTY; INTER_EMPTY] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `Z INTER (Y INTER IMAGE (h:real^3->real^3) (derived_dual_cell t l u)) = R1 /\
                Z INTER (Y INTER IMAGE (h:real^3->real^3) (derived_dual_cell t l u')) = R2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`Z INTER (G1:real^3->bool) = R1`; `Z INTER (G2:real^3->bool) = R2`;
      `G1 = Y INTER IMAGE (h:real^3->real^3) (derived_dual_cell t l u)`;
      `G2 = Y INTER IMAGE (h:real^3->real^3) (derived_dual_cell t l u')`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FTP_VBLK_SETS THEN
  MAP_EVERY EXISTS_TAC [`Z:real^3->bool`; `convex hull {m1:real^3,cS1,cF1}`;
                        `convex hull {m2:real^3,cS2,cF2}`] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The traces of the nine disk sets of a generalized block on               *)
(* its two dual disks (MOI_FTP_AB_DTR: they depend only on the dual disk,   *)
(* its rim and the corner triangle, so two blocks sharing a dual disk and   *)
(* its kite have the same traces), the disk sets lie in the level region,  *)
(* and their intersection structure (MOI_FTP_AB_ZD_INTER).                  *)
(* ========================================================================= *)

let MOI_FTP_ZD_INTER_LEFT = prove
 (`!(D:real^N->bool) Om Op S Fn Xs Kc j.
     D INTER moi_ftc_zd Om Op S Fn Xs Kc j =
     moi_ftc_zd (D INTER Om) (D INTER Op) (D INTER S) (D INTER Fn) (D INTER Xs)
                (D INTER Kc) j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_zd] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN SET_TAC[]);;

let MOI_FTP_AB_DTR = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg J Q' W.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J /\
     W = moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v Q')
                    (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF)
                    (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])
     ==> (!j. G1 INTER W j =
              moi_ftc_zd (convex hull {m1,p1,q1})
                         ((G1 DIFF convex hull {m1,p1,q1}) UNION
                          (segment[m1,p1] UNION segment[m1,q1]))
                         (segment[m1,p1]) (segment[m1,q1]) R1 {m1} j) /\
         (!j. G2 INTER W j =
              moi_ftc_zd (convex hull {m2,p2,q2})
                         ((G2 DIFF convex hull {m2,p2,q2}) UNION
                          (segment[m2,p2] UNION segment[m2,q2]))
                         (segment[m2,p2]) (segment[m2,q2]) R2 {m2} j) /\
         (!j. W j SUBSET Y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let c = CONJUNCTS th in
    let wdef = last c in
    let th3 = end_itlist CONJ (butlast c) in
    SUBST1_TAC wdef THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F1 th3) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F3 th3) THEN
    ASSUME_TAC(el 1 c) THEN ASSUME_TAC(el 2 c)) THEN
  REWRITE_TAC[MOI_FTP_ZD_INTER_LEFT] THEN
  SUBGOAL_THEN
   `G1 INTER (Q':real^N->bool) =
    (G1 DIFF convex hull {m1,p1,q1}) UNION (segment[m1,p1] UNION segment[m1,q1]) /\
    G2 INTER (Q':real^N->bool) =
    (G2 DIFF convex hull {m2,p2,q2}) UNION (segment[m2,p2] UNION segment[m2,q2])`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`Q' = (L DIFF Q) UNION (J:real^N->bool)`; `J = (As:real^N->bool) UNION AF`;
      `(G1:real^N->bool) INTER Q = convex hull {m1,p1,q1}`;
      `(G2:real^N->bool) INTER Q = convex hull {m2,p2,q2}`;
      `(G1:real^N->bool) INTER As = segment[m1,p1]`;
      `(G1:real^N->bool) INTER AF = segment[m1,q1]`;
      `(G2:real^N->bool) INTER As = segment[m2,p2]`;
      `(G2:real^N->bool) INTER AF = segment[m2,q2]`;
      `(G1:real^N->bool) SUBSET L`; `(G2:real^N->bool) SUBSET L`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    is_var(lhs(concl th)) && mem (fst(dest_var(lhs(concl th)))) ["J"; "Q'"]))) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN REWRITE_TAC[moi_ftc_zd] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  MAP_EVERY UNDISCH_TAC
   [`(Z:real^N->bool) SUBSET Y`; `(Fg:real^N->bool) SUBSET Y`;
    `segment[v:real^N,m1] UNION segment[v,m2] SUBSET Y INTER moi_ftc_cone v As`] THEN
  SET_TAC[]);;

(* The core arcs of a block miss the frontier part and the fingers. *)

let MOI_FTP_CORE_XS = prove
 (`!(v:real^N) L X Z Fg m.
     (!x y. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
     (!x y. x IN X /\ y IN X /\ y IN segment[v,x] ==> y = x) /\
     Z SUBSET X /\ Fg SUBSET L /\ m IN X /\ m IN L /\ ~(m IN Z) /\ ~(m IN Fg)
     ==> segment[v,m] INTER (Z UNION Fg) = {}`,
  REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_UNION; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* The intersection structure of the nine disk sets of a block. *)

let MOI_FTP_AB_ZD_INTER = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg J Q' W.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg /\
     J = As UNION AF /\ Q' = (L DIFF Q) UNION J /\
     W = moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v Q')
                    (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF)
                    (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])
     ==> !j j'. j < 9 /\ j' < 9
                ==> W j INTER W j' =
                    UNIONS {W j'' | j'' | j'' < 9 /\ moi_ftc_dface j j'' /\
                                          moi_ftc_dface j' j''}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let c = CONJUNCTS th in
    let wdef = last c in
    let th3 = end_itlist CONJ (butlast c) in
    SUBST1_TAC wdef THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F1 th3) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FTP_AB_F3 th3) THEN
    ASSUME_TAC(CONJUNCT1(GEN_REWRITE_RULE I [moi_ftp_abl] (hd c)))) THEN
  SUBGOAL_THEN
   `(!x y:real^N. x IN L /\ y IN L /\ y IN segment[v,x] ==> y = x) /\
    (!x y:real^N. x IN X /\ y IN X /\ y IN segment[v,x] ==> y = x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_ftc_rad (v:real^N) L X Y` THEN SIMP_TAC[moi_ftc_rad]; ALL_TAC] THEN
  SUBGOAL_THEN `~((m1:real^N) IN Fg) /\ ~((m2:real^N) IN Fg)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(m1:real^N) IN G1`; `(m2:real^N) IN G2`;
      `(Fg:real^N->bool) INTER G1 = {}`; `(Fg:real^N->bool) INTER G2 = {}`] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FTC_ZD_INTER THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE `((y:real^N->bool) INTER a) INTER (y INTER b) = y INTER (a INTER b)`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SET_RULE `((y:real^N->bool) INTER a) INTER (y INTER b) = y INTER (a INTER b)`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `segment[v:real^N,m1] UNION segment[v,m2] SUBSET Y INTER moi_ftc_cone v As` THEN
    SET_TAC[];
    REWRITE_TAC[SET_RULE `((a:real^N->bool) UNION b) INTER c = (a INTER c) UNION (b INTER c)`;
                EMPTY_UNION] THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_FTP_CORE_XS THEN
    MAP_EVERY EXISTS_TAC [`L:real^N->bool`; `X:real^N->bool`] THEN ASM_REWRITE_TAC[]]);;

(* Gluing the block disk sets: if each block meets the disk sets of every   *)
(* other block only inside its own, the global sets ZA j (the k-images of   *)
(* the block sets) have the block sets as traces.                           *)

let MOI_FTP_GLUE_IMAGE = prove
 (`!(h:real^N->real^N) k U (C:num->real^N->bool) (W:num->num->real^N->bool) n.
     (!x. x IN U ==> h x IN U /\ k (h x) = x) /\ (!y. y IN U ==> k y IN U /\ h (k y) = y) /\
     (!i. i < n ==> C i SUBSET U) /\
     (!i j. i < n ==> W i j SUBSET IMAGE h (C i)) /\
     (!i i' j. i < n /\ i' < n ==> IMAGE h (C i) INTER W i' j SUBSET W i j)
     ==> !i j. i < n
               ==> IMAGE h (C i INTER UNIONS {IMAGE k (W i' j) | i' | i' < n}) = W i j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hU") (CONJUNCTS_THEN2 (LABEL_TAC "kU")
    (CONJUNCTS_THEN2 (LABEL_TAC "CU") (CONJUNCTS_THEN2 (LABEL_TAC "WY") (LABEL_TAC "WW"))))) THEN
  SUBGOAL_THEN `!i' j y. i' < n /\ y IN (W:num->num->real^N->bool) i' j
                         ==> ?x. x IN C i' /\ x IN U /\ y = h x /\ y IN U /\ k y = x`
  (LABEL_TAC "WU") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "WY" (fun th -> MP_TAC(SPEC `j:num` (MATCH_MP th (ASSUME `i':num < n`)))) THEN
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "CU" (fun th -> MP_TAC(MATCH_MP th (ASSUME `i':num < n`))) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    USE_THEN "hU" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN U`))) THEN
    SIMP_TAC[] THEN DISCH_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `i':num` (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC))))))) THEN
    USE_THEN "WU" (MP_TAC o SPECL [`i':num`; `j:num`; `z:real^N`]) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(h:real^N->real^N) ((k:real^N->real^N) z) = z` SUBST1_TAC THENL
     [USE_THEN "kU" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^N) IN U`))) THEN SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "WW" (MP_TAC o SPECL [`i:num`; `i':num`; `j:num`]) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    EXISTS_TAC `(k:real^N->real^N) z` THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    USE_THEN "kU" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(z:real^N) IN U`))) THEN SIMP_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE h ((C:num->real^N->bool) i)` MP_TAC THENL
     [USE_THEN "WY" (fun th -> MP_TAC(SPEC `j:num` (MATCH_MP th (ASSUME `i:num < n`)))) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `(h:real^N->real^N) x` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN
      USE_THEN "CU" (fun th -> MP_TAC(MATCH_MP th (ASSUME `i:num < n`))) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
      USE_THEN "hU" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN U`))) THEN SIMP_TAC[];
      UNDISCH_TAC `(y:real^N) IN W (i:num) (j:num)` THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The necklace labels.  For a cyclic family C 0, ..., C(n-1)               *)
(* (n >= 3) whose non-consecutive members are disjoint and whose triple     *)
(* intersections are empty, the 2n block labels (a < n: the arc C a;       *)
(* n + b: the bead C b INTER C(nx b)) satisfy the intersection hypothesis  *)
(* of MOI_FTC_PROD_ASSEMBLY (MOI_FTP_NECKLACE).                             *)
(* ========================================================================= *)

let moi_ftp_nx = new_definition
 `moi_ftp_nx n i = if SUC i = n then 0 else SUC i`;;

let moi_ftp_pv = new_definition
 `moi_ftp_pv n i = if i = 0 then n - 1 else i - 1`;;

let moi_ftp_cb = new_definition
 `moi_ftp_cb n (C:num->A->bool) a =
    if a < n then C a else C (a - n) INTER C (moi_ftp_nx n (a - n))`;;

let moi_ftp_bface = new_definition
 `moi_ftp_bface n a a' <=> a' = a \/ (a < n /\ (a' = n + a \/ a' = n + moi_ftp_pv n a))`;;

let moi_ftp_bdim = new_definition
 `moi_ftp_bdim (n:num) (a:num) = if a < n then 1 else 0`;;

let MOI_FTP_NXPV = prove
 (`!n i. 3 <= n /\ i < n
         ==> moi_ftp_nx n i < n /\ moi_ftp_pv n i < n /\
             moi_ftp_nx n (moi_ftp_pv n i) = i /\ moi_ftp_pv n (moi_ftp_nx n i) = i /\
             ~(moi_ftp_nx n i = i) /\ ~(moi_ftp_pv n i = i) /\
             ~(moi_ftp_nx n i = moi_ftp_pv n i) /\
             ~(moi_ftp_nx n (moi_ftp_nx n i) = i) /\
             (!j. j < n /\ moi_ftp_nx n j = i ==> j = moi_ftp_pv n i) /\
             (!j. j < n /\ moi_ftp_pv n j = i ==> j = moi_ftp_nx n i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_ftp_nx; moi_ftp_pv] THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let MOI_FTP_CB_FACE = prove
 (`!(C:num->A->bool) n a a''.
     3 <= n /\ a < n + n /\ moi_ftp_bface n a a''
     ==> a'' < n + n /\ moi_ftp_cb n C a'' SUBSET moi_ftp_cb n C a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftp_bface] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MP_TAC(SPECL [`n:num`; `a:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_ftp_cb] THEN ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `n + a < n + n /\ n + moi_ftp_pv n a < n + n /\ ~(n + a < n) /\
                 ~(n + moi_ftp_pv n a < n) /\ (n + a) - n = a /\
                 (n + moi_ftp_pv n a) - n = moi_ftp_pv n a`
   STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `a:num < n` THEN UNDISCH_TAC `moi_ftp_pv n a < n` THEN ARITH_TAC;
     ASM_REWRITE_TAC[] THEN SET_TAC[]]));;

let MOI_FTP_NECKLACE = prove
 (`!(C:num->A->bool) n.
     3 <= n /\
     (!i j. i < n /\ j < n /\ ~(i = j) /\ ~(j = moi_ftp_nx n i) /\ ~(i = moi_ftp_nx n j)
            ==> C i INTER C j = {}) /\
     (!i j. i < n /\ j < n /\ ~(j = i) /\ ~(j = moi_ftp_nx n i)
            ==> C i INTER C (moi_ftp_nx n i) INTER C j = {})
     ==> !a a'. a < n + n /\ a' < n + n
                ==> moi_ftp_cb n C a INTER moi_ftp_cb n C a' =
                    UNIONS {moi_ftp_cb n C a'' | a'' | a'' < n + n /\ moi_ftp_bface n a a'' /\
                                                       moi_ftp_bface n a' a''}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "H2") (LABEL_TAC "H3"))) THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `a':num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `a'':num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`C:num->A->bool`; `n:num`; `a:num`; `a'':num`] MOI_FTP_CB_FACE) THEN
    MP_TAC(ISPECL [`C:num->A->bool`; `n:num`; `a':num`; `a'':num`] MOI_FTP_CB_FACE) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]] THEN
  (* each nonempty intersection lies in one common face *)
  SUBGOAL_THEN
   `moi_ftp_cb n (C:num->A->bool) a INTER moi_ftp_cb n C a' = {} \/
    ?a''. a'' < n + n /\ moi_ftp_bface n a a'' /\ moi_ftp_bface n a' a'' /\
          moi_ftp_cb n C a INTER moi_ftp_cb n C a' SUBSET moi_ftp_cb n C a''`
  MP_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_ftp_cb n (C:num->A->bool) a''` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `a'':num` THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[moi_ftp_bface] THEN
  ASM_CASES_TAC `a:num < n` THEN ASM_CASES_TAC `a':num < n` THEN ASM_REWRITE_TAC[] THENL
   [(* two arcs *)
    MP_TAC(SPECL [`n:num`; `a:num`] MOI_FTP_NXPV) THEN
    MP_TAC(SPECL [`n:num`; `a':num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[moi_ftp_cb] THEN
    ASM_CASES_TAC `a':num = a` THENL
     [DISJ2_TAC THEN EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `a':num = moi_ftp_nx n a` THENL
     [DISJ2_TAC THEN EXISTS_TAC `n + a:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `n + a:num < n + n <=> a < n`;
                      ARITH_RULE `~(n + a:num < n)`; ADD_SUB2] THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `a:num = moi_ftp_nx n a'` THENL
     [DISJ2_TAC THEN EXISTS_TAC `n + a':num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `n + a:num < n + n <=> a < n`;
                      ARITH_RULE `~(n + a:num < n)`; ADD_SUB2] THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISJ1_TAC THEN USE_THEN "H2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* an arc and a bead *)
    ABBREV_TAC `b = a' - n:num` THEN
    SUBGOAL_THEN `a' = n + b:num /\ b < n` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`a' - n:num = b`; `~(a':num < n)`; `a':num < n + n`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`n:num`; `a:num`] MOI_FTP_NXPV) THEN
    MP_TAC(SPECL [`n:num`; `b:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[moi_ftp_cb; ARITH_RULE `~(n + b:num < n)`; ADD_SUB2] THEN
    ASM_CASES_TAC `b:num = a` THENL
     [DISJ2_TAC THEN EXISTS_TAC `n + b:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `~(n + b:num < n)`; ADD_SUB2] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `b:num = moi_ftp_pv n a` THENL
     [DISJ2_TAC THEN EXISTS_TAC `n + b:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `~(n + b:num < n)`; ADD_SUB2] THEN SET_TAC[];
      ALL_TAC] THEN
    DISJ1_TAC THEN
    USE_THEN "H3" (MP_TAC o SPECL [`b:num`; `a:num`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `~(b:num = moi_ftp_pv n a)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_ftp_nx n j`)) (concl th) && 
        can (find_term ((=) `moi_ftp_pv n a`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    (* a bead and an arc *)
    ABBREV_TAC `b = a - n:num` THEN
    SUBGOAL_THEN `a = n + b:num /\ b < n` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`a - n:num = b`; `~(a:num < n)`; `a:num < n + n`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`n:num`; `a':num`] MOI_FTP_NXPV) THEN
    MP_TAC(SPECL [`n:num`; `b:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[moi_ftp_cb; ARITH_RULE `~(n + b:num < n)`; ADD_SUB2] THEN
    ASM_CASES_TAC `b:num = a'` THENL
     [DISJ2_TAC THEN EXISTS_TAC `n + b:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `~(n + b:num < n)`; ADD_SUB2] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `b:num = moi_ftp_pv n a'` THENL
     [DISJ2_TAC THEN EXISTS_TAC `n + b:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `~(n + b:num < n)`; ADD_SUB2] THEN SET_TAC[];
      ALL_TAC] THEN
    DISJ1_TAC THEN
    USE_THEN "H3" (MP_TAC o SPECL [`b:num`; `a':num`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `~(b:num = moi_ftp_pv n a')` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_ftp_nx n j`)) (concl th) && 
        can (find_term ((=) `moi_ftp_pv n a'`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      SET_TAC[]];
    (* two beads *)
    ABBREV_TAC `b = a - n:num` THEN ABBREV_TAC `b' = a' - n:num` THEN
    SUBGOAL_THEN `a = n + b:num /\ b < n /\ a' = n + b':num /\ b' < n` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`a - n:num = b`; `~(a:num < n)`; `a:num < n + n`;
                             `a' - n:num = b'`; `~(a':num < n)`; `a':num < n + n`] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      (lhs(concl th) = `a:num` || lhs(concl th) = `a':num`)))) THEN
    REWRITE_TAC[EQ_ADD_LCANCEL; ARITH_RULE `~(n + b:num < n)`] THEN
    ASM_CASES_TAC `b:num = b'` THENL
     [DISJ2_TAC THEN EXISTS_TAC `n + b:num` THEN
      ASM_REWRITE_TAC[ARITH_RULE `n + b:num < n + n <=> b < n`] THEN SET_TAC[];
      ALL_TAC] THEN
    DISJ1_TAC THEN REWRITE_TAC[moi_ftp_cb; ARITH_RULE `~(n + b:num < n)`; ADD_SUB2] THEN
    MP_TAC(SPECL [`n:num`; `b:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `b':num = moi_ftp_nx n b` THENL
     [SUBGOAL_THEN `C b INTER C(moi_ftp_nx n b) INTER
                    (C:num->A->bool)(moi_ftp_nx n (moi_ftp_nx n b)) = {}` MP_TAC THENL
       [USE_THEN "H3" MATCH_MP_TAC THEN
        MP_TAC(SPECL [`n:num`; `moi_ftp_nx n b`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      SUBGOAL_THEN `C b INTER C(moi_ftp_nx n b) INTER (C:num->A->bool) b' = {}` MP_TAC THENL
       [USE_THEN "H3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SET_TAC[]]]]);;

let MOI_FTP_BLABELS = prove
 (`!n:num. 3 <= n
       ==> FINITE {a:num | a < n + n} /\
           (!a. a < n + n ==> moi_ftp_bface n a a) /\
           (!a j. a < n + n /\ j < 9 ==> moi_ftp_bdim n a + moi_ftc_dd j <= 3) /\
           (!a a'. a < n + n /\ moi_ftp_bface n a a'
                   ==> a' < n + n /\ (a' = a \/ moi_ftp_bdim n a' < moi_ftp_bdim n a))`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[FINITE_NUMSEG_LT; moi_ftp_bface] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[moi_ftp_bdim; moi_ftc_dd] THEN
    REPEAT COND_CASES_TAC THEN ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`a:num`; `a':num`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`n:num`; `a:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[moi_ftp_bdim] THEN
    UNDISCH_TAC `a:num < n` THEN UNDISCH_TAC `moi_ftp_pv n a < n` THEN ARITH_TAC]);;

(* ========================================================================= *)
(* The blocks of the polygon.  moi_ftp_blocks bundles the                   *)
(* generalized abstract blocks at the polygon vertices S i (i < n), with    *)
(* the kite at the edge [S i, S(SUC i)] labelled (cS i, cF i) and used by   *)
(* block i (end kite) and block i + 1 (start kite); moi_ftp_bw gives the    *)
(* nine local disk sets of block i.  MOI_FTP_AB_PKG collects the block      *)
(* facts used by the assembly.                                               *)
(* ========================================================================= *)

let moi_ftp_blocks = new_definition
 `moi_ftp_blocks (t:(real^N->bool)->bool) l (h:real^N->real^N) (n:num) (S:num->real^N)
                 (cS:num->real^N) (cF:num->real^N) Q As AF bs b1 <=>
    !i. i < n ==>
      moi_ftp_abl (S i) (UNIONS (simplicial_link (barycentric_subdivision t) (S i)))
        (IMAGE h (derived_dual_cell t l (S i) INTER derived_frontier t l) UNION
         (IMAGE h (derived_dual_cell t l (S i)) INTER
          UNIONS (simplicial_link (barycentric_subdivision t) (S i))))
        (IMAGE h (derived_dual_cell t l (S i)))
        (IMAGE h (derived_dual_cell t l (S i) INTER derived_frontier t l))
        (midpoint(S i,S(i + n - 1))) (midpoint(S i,S(SUC i)))
        (midpoint(midpoint(S i,S(i + n - 1)),cS(i + n - 1)))
        (midpoint(midpoint(S i,S(i + n - 1)),cF(i + n - 1)))
        (midpoint(midpoint(S i,S(SUC i)),cS i)) (midpoint(midpoint(S i,S(SUC i)),cF i))
        (bs i) (b1 i) (Q i) (As i) (AF i)
        (IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(i + n - 1))))
        (IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(SUC i))))
        (IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(i + n - 1)) INTER
                  derived_frontier t l))
        (IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(SUC i)) INTER
                  derived_frontier t l))
        {}`;;

let moi_ftp_bw = new_definition
 `moi_ftp_bw (t:(real^N->bool)->bool) l (h:real^N->real^N) (n:num) (S:num->real^N)
             (Q:num->real^N->bool) As AF i =
    moi_ftc_zd (IMAGE h (derived_dual_cell t l (S i)) INTER moi_ftc_cone (S i) (Q i))
               (IMAGE h (derived_dual_cell t l (S i)) INTER
                moi_ftc_cone (S i) ((UNIONS (simplicial_link (barycentric_subdivision t) (S i))
                                     DIFF Q i) UNION (As i UNION AF i)))
               (IMAGE h (derived_dual_cell t l (S i)) INTER moi_ftc_cone (S i) (As i))
               (IMAGE h (derived_dual_cell t l (S i)) INTER moi_ftc_cone (S i) (AF i))
               (IMAGE h (derived_dual_cell t l (S i) INTER derived_frontier t l) UNION {})
               (segment[S i,midpoint(S i,S(i + n - 1))] UNION
                segment[S i,midpoint(S i,S(SUC i))])`;;

(* The facts of one generalized block used by the assembly. *)

let MOI_FTP_AB_PKG = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg W.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg /\
     W = moi_ftc_zd (Y INTER moi_ftc_cone v Q)
                    (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF)))
                    (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF)
                    (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])
     ==> (!j. j < 9
              ==> pl_cell_with_boundary (1 + moi_ftc_dd j) (W j)
                    (UNIONS {W j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)} UNION
                     ((G1 UNION G2) INTER W j)) /\
                  pl_cell_with_boundary (moi_ftc_dd j) (G1 INTER W j)
                    (G1 INTER UNIONS {W j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})) /\
         (!j. G1 INTER W j =
              moi_ftc_zd (convex hull {m1,p1,q1})
                         ((G1 DIFF convex hull {m1,p1,q1}) UNION
                          (segment[m1,p1] UNION segment[m1,q1]))
                         (segment[m1,p1]) (segment[m1,q1]) R1 {m1} j) /\
         (!j. G2 INTER W j =
              moi_ftc_zd (convex hull {m2,p2,q2})
                         ((G2 DIFF convex hull {m2,p2,q2}) UNION
                          (segment[m2,p2] UNION segment[m2,q2]))
                         (segment[m2,p2]) (segment[m2,q2]) R2 {m2} j) /\
         (!j. W j SUBSET Y) /\
         (!j j'. j < 9 /\ j' < 9
                 ==> W j INTER W j' =
                     UNIONS {W j'' | j'' | j'' < 9 /\ moi_ftc_dface j j'' /\
                                           moi_ftc_dface j' j''})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `Z:real^N->bool`; `m1:real^N`; `m2:real^N`; `p1:real^N`; `q1:real^N`;
                 `p2:real^N`; `q2:real^N`; `bs:real^N`; `b1:real^N`; `Q:real^N->bool`;
                 `As:real^N->bool`; `AF:real^N->bool`; `G1:real^N->bool`; `G2:real^N->bool`;
                 `R1:real^N->bool`; `R2:real^N->bool`; `Fg:real^N->bool`;
                 `As UNION AF:real^N->bool`; `(L DIFF Q) UNION (As UNION AF):real^N->bool`;
                 `W:num->real^N->bool`] MOI_FTP_AB_CELLS) THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `Z:real^N->bool`; `m1:real^N`; `m2:real^N`; `p1:real^N`; `q1:real^N`;
                 `p2:real^N`; `q2:real^N`; `bs:real^N`; `b1:real^N`; `Q:real^N->bool`;
                 `As:real^N->bool`; `AF:real^N->bool`; `G1:real^N->bool`; `G2:real^N->bool`;
                 `R1:real^N->bool`; `R2:real^N->bool`; `Fg:real^N->bool`;
                 `As UNION AF:real^N->bool`; `(L DIFF Q) UNION (As UNION AF):real^N->bool`;
                 `W:num->real^N->bool`] MOI_FTP_AB_DTR) THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `Z:real^N->bool`; `m1:real^N`; `m2:real^N`; `p1:real^N`; `q1:real^N`;
                 `p2:real^N`; `q2:real^N`; `bs:real^N`; `b1:real^N`; `Q:real^N->bool`;
                 `As:real^N->bool`; `AF:real^N->bool`; `G1:real^N->bool`; `G2:real^N->bool`;
                 `R1:real^N->bool`; `R2:real^N->bool`; `Fg:real^N->bool`;
                 `As UNION AF:real^N->bool`; `(L DIFF Q) UNION (As UNION AF):real^N->bool`;
                 `W:num->real^N->bool`] MOI_FTP_AB_ZD_INTER) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Periodic sequences. *)

let MOI_FTP_PER_MOD = prove
 (`!(f:num->A) n. 0 < n /\ (!i. f(i + n) = f i) ==> !i. f i = f (i MOD n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!q r. (f:num->A)(r + q * n) = f r` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `r + q * n + n:num = (r + q * n) + n`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_TAC THEN
  MP_TAC(SPECL [`i:num`; `n:num`] DIVISION) THEN ANTS_TAC THENL
   [UNDISCH_TAC `0 < n` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONJUNCT1 th]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_FTP_PER_EQ = prove
 (`!(S:num->A) n.
     0 < n /\ (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j)
     ==> !a b. S a = S b <=> a MOD n = b MOD n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FTP_PER_MOD o
    (fun th -> CONJ (ASSUME `0 < n`) th) o check (fun th -> is_forall(concl th) &&
      not(is_imp(snd(dest_forall(concl th)))))) THEN
  REPEAT GEN_TAC THEN
  FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [th]) o check (fun th ->
    is_forall(concl th) && can (find_term (fun t -> try fst(dest_const t) = "MOD"
                                           with Failure _ -> false)) (concl th))) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MOD_LT_EQ_LT] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    SIMP_TAC[]]);;

let MOI_FTP_PER_SHIFT = prove
 (`!(f:num->A) n a b c.
     0 < n /\ (!i. f(i + n) = f i) /\ a MOD n = b MOD n ==> f(a + c) = f(b + c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->A`; `n:num`] MOI_FTP_PER_MOD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_REWRITE_TAC[]);;

(* Two blocks sharing a dual disk D with the same traces on D: a block meets *)
(* the disk sets of the other only in its own.                              *)

let MOI_FTP_SHARE = prove
 (`!(Y:real^N->bool) Y' (W:num->real^N->bool) (W':num->real^N->bool) D.
     Y INTER Y' = D /\ (!j. W' j SUBSET Y') /\ (!j. D INTER W' j = D INTER W j)
     ==> !j. Y INTER W' j SUBSET W j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `D:real^N->bool`)) (concl th))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN
  UNDISCH_TAC `(Y:real^N->bool) INTER Y' = D` THEN SET_TAC[]);;


(* The same, with the local disk sets written out. *)

let MOI_FTP_AB_PKG2 = prove
 (`!(v:real^N) L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg.
     moi_ftp_abl v L X Y Z m1 m2 p1 q1 p2 q2 bs b1 Q As AF G1 G2 R1 R2 Fg
     ==> (!j. j < 9
              ==> pl_cell_with_boundary (1 + moi_ftc_dd j) ((moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j)
                    (UNIONS {(moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)} UNION
                     ((G1 UNION G2) INTER (moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j)) /\
                  pl_cell_with_boundary (moi_ftc_dd j) (G1 INTER (moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j)
                    (G1 INTER UNIONS {(moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})) /\
         (!j. G1 INTER (moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j =
              moi_ftc_zd (convex hull {m1,p1,q1})
                         ((G1 DIFF convex hull {m1,p1,q1}) UNION
                          (segment[m1,p1] UNION segment[m1,q1]))
                         (segment[m1,p1]) (segment[m1,q1]) R1 {m1} j) /\
         (!j. G2 INTER (moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j =
              moi_ftc_zd (convex hull {m2,p2,q2})
                         ((G2 DIFF convex hull {m2,p2,q2}) UNION
                          (segment[m2,p2] UNION segment[m2,q2]))
                         (segment[m2,p2]) (segment[m2,q2]) R2 {m2} j) /\
         (!j. (moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j SUBSET Y) /\
         (!j j'. j < 9 /\ j' < 9
                 ==> (moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j INTER (moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j' =
                     UNIONS {(moi_ftc_zd (Y INTER moi_ftc_cone v Q) (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF))) (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg) (segment[v,m1] UNION segment[v,m2])) j'' | j'' | j'' < 9 /\ moi_ftc_dface j j'' /\
                                           moi_ftc_dface j' j''})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`v:real^N`; `L:real^N->bool`; `X:real^N->bool`; `Y:real^N->bool`;
                 `Z:real^N->bool`; `m1:real^N`; `m2:real^N`; `p1:real^N`; `q1:real^N`;
                 `p2:real^N`; `q2:real^N`; `bs:real^N`; `b1:real^N`; `Q:real^N->bool`;
                 `As:real^N->bool`; `AF:real^N->bool`; `G1:real^N->bool`; `G2:real^N->bool`;
                 `R1:real^N->bool`; `R2:real^N->bool`; `Fg:real^N->bool`;
                 `moi_ftc_zd (Y INTER moi_ftc_cone v Q)
                    (Y INTER moi_ftc_cone v ((L DIFF Q) UNION (As UNION AF)))
                    (Y INTER moi_ftc_cone v As) (Y INTER moi_ftc_cone v AF) (Z UNION Fg)
                    (segment[v,m1] UNION segment[v:real^N,m2])`] MOI_FTP_AB_PKG) THEN
  ASM_REWRITE_TAC[]);;

(* The block package of block i in terms of moi_ftp_bw. *)

let MOI_FTP_BLOCK_PKG = prove
 (`!(t:(real^N->bool)->bool) l h n (S:num->real^N) cS cF Q As AF bs b1 i.
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1 /\ i < n
     ==> (!j. j < 9
              ==> pl_cell_with_boundary (1 + moi_ftc_dd j) (moi_ftp_bw t l h n S Q As AF i j)
                    (UNIONS {moi_ftp_bw t l h n S Q As AF i j' | j' |
                             j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)} UNION
                     ((IMAGE h (derived_dual_cell t l (S i) INTER
                                derived_dual_cell t l (S(i + n - 1))) UNION
                       IMAGE h (derived_dual_cell t l (S i) INTER
                                derived_dual_cell t l (S(SUC i)))) INTER
                      moi_ftp_bw t l h n S Q As AF i j)) /\
                  pl_cell_with_boundary (moi_ftc_dd j)
                    (IMAGE h (derived_dual_cell t l (S i) INTER
                              derived_dual_cell t l (S(i + n - 1))) INTER
                     moi_ftp_bw t l h n S Q As AF i j)
                    (IMAGE h (derived_dual_cell t l (S i) INTER
                              derived_dual_cell t l (S(i + n - 1))) INTER
                     UNIONS {moi_ftp_bw t l h n S Q As AF i j' | j' |
                             j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})) /\
         (!j. IMAGE h (derived_dual_cell t l (S i) INTER
                       derived_dual_cell t l (S(i + n - 1))) INTER
              moi_ftp_bw t l h n S Q As AF i j =
              moi_ftc_zd
                (convex hull {midpoint(S i,S(i + n - 1)),
                              midpoint(midpoint(S i,S(i + n - 1)),cS(i + n - 1)),
                              midpoint(midpoint(S i,S(i + n - 1)),cF(i + n - 1))})
                ((IMAGE h (derived_dual_cell t l (S i) INTER
                           derived_dual_cell t l (S(i + n - 1))) DIFF
                  convex hull {midpoint(S i,S(i + n - 1)),
                               midpoint(midpoint(S i,S(i + n - 1)),cS(i + n - 1)),
                               midpoint(midpoint(S i,S(i + n - 1)),cF(i + n - 1))}) UNION
                 (segment[midpoint(S i,S(i + n - 1)),
                          midpoint(midpoint(S i,S(i + n - 1)),cS(i + n - 1))] UNION
                  segment[midpoint(S i,S(i + n - 1)),
                          midpoint(midpoint(S i,S(i + n - 1)),cF(i + n - 1))]))
                (segment[midpoint(S i,S(i + n - 1)),
                         midpoint(midpoint(S i,S(i + n - 1)),cS(i + n - 1))])
                (segment[midpoint(S i,S(i + n - 1)),
                         midpoint(midpoint(S i,S(i + n - 1)),cF(i + n - 1))])
                (IMAGE h (derived_dual_cell t l (S i) INTER
                          derived_dual_cell t l (S(i + n - 1)) INTER derived_frontier t l))
                {midpoint(S i,S(i + n - 1))} j) /\
         (!j. IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(SUC i))) INTER
              moi_ftp_bw t l h n S Q As AF i j =
              moi_ftc_zd
                (convex hull {midpoint(S i,S(SUC i)), midpoint(midpoint(S i,S(SUC i)),cS i),
                              midpoint(midpoint(S i,S(SUC i)),cF i)})
                ((IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(SUC i))) DIFF
                  convex hull {midpoint(S i,S(SUC i)), midpoint(midpoint(S i,S(SUC i)),cS i),
                               midpoint(midpoint(S i,S(SUC i)),cF i)}) UNION
                 (segment[midpoint(S i,S(SUC i)),midpoint(midpoint(S i,S(SUC i)),cS i)] UNION
                  segment[midpoint(S i,S(SUC i)),midpoint(midpoint(S i,S(SUC i)),cF i)]))
                (segment[midpoint(S i,S(SUC i)),midpoint(midpoint(S i,S(SUC i)),cS i)])
                (segment[midpoint(S i,S(SUC i)),midpoint(midpoint(S i,S(SUC i)),cF i)])
                (IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(SUC i)) INTER
                          derived_frontier t l))
                {midpoint(S i,S(SUC i))} j) /\
         (!j. moi_ftp_bw t l h n S Q As AF i j SUBSET IMAGE h (derived_dual_cell t l (S i))) /\
         (!j j'. j < 9 /\ j' < 9
                 ==> moi_ftp_bw t l h n S Q As AF i j INTER moi_ftp_bw t l h n S Q As AF i j' =
                     UNIONS {moi_ftp_bw t l h n S Q As AF i j'' | j'' |
                             j'' < 9 /\ moi_ftc_dface j j'' /\ moi_ftc_dface j' j''})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftp_blocks] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FTP_AB_PKG2) THEN
  REWRITE_TAC[GSYM moi_ftp_bw]);;

(* Consistency of the disk sets of the blocks: block i meets the disk sets  *)
(* of block i' only inside its own.                                         *)

let MOI_FTP_BLOCKS_CONS = prove
 (`!(t:(real^N->bool)->bool) l V h k n (S:num->real^N) cS cF Q As AF bs b1.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. S i IN V) /\ (!i. {S i} IN l) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)) /\
     (!i. cS(i + n) = cS i) /\ (!i. cF(i + n) = cF i) /\
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1
     ==> !i i' j. i < n /\ i' < n
                  ==> IMAGE h (derived_dual_cell t l (S i)) INTER
                      moi_ftp_bw t l h n S Q As AF i' j
                      SUBSET moi_ftp_bw t l h n S Q As AF i j`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "per") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (CONJUNCTS_THEN2 (LABEL_TAC "inV") (CONJUNCTS_THEN2 (LABEL_TAC "inl")
    (CONJUNCTS_THEN2 (LABEL_TAC "deg") (CONJUNCTS_THEN2 (LABEL_TAC "pS")
    (CONJUNCTS_THEN2 (LABEL_TAC "pF") (LABEL_TAC "blk"))))))))))) THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `i':num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `0 < n` ASSUME_TAC THENL
   [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `U = UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))` THEN
  SUBGOAL_THEN
   `(!a. derived_dual_cell t l ((S:num->real^N) a) SUBSET U) /\
    (!y:real^N. y IN U ==> (k:real^N->real^N) ((h:real^N->real^N) y) = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `a:num` THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                     `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) a`]
        MOI_FTC_LEV_BASICS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (S:num->real^N) a IN s}` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                     `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) 0`]
        MOI_FTC_LEV_BASICS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) a)) INTER
          IMAGE h (derived_dual_cell t l (S b)) =
          IMAGE h (derived_dual_cell t l (S a) INTER derived_dual_cell t l (S b))`
  (LABEL_TAC "hinj") THENL
   [REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTA_IMAGE_INTER_INJ THEN
    EXISTS_TAC `k:real^N->real^N` THEN EXISTS_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^N`;
                 `n:num`; `S:num->real^N`; `cS:num->real^N`; `cF:num->real^N`;
                 `Q:num->real^N->bool`; `As:num->real^N->bool`; `AF:num->real^N->bool`;
                 `bs:num->real^N`; `b1:num->real^N`; `i:num`] MOI_FTP_BLOCK_PKG) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^N`;
                 `n:num`; `S:num->real^N`; `cS:num->real^N`; `cF:num->real^N`;
                 `Q:num->real^N->bool`; `As:num->real^N->bool`; `AF:num->real^N->bool`;
                 `bs:num->real^N`; `b1:num->real^N`; `i':num`] MOI_FTP_BLOCK_PKG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "d1'")
    (CONJUNCTS_THEN2 (LABEL_TAC "d2'") (CONJUNCTS_THEN2 (LABEL_TAC "s'") (K ALL_TAC))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "d1")
    (CONJUNCTS_THEN2 (LABEL_TAC "d2") (CONJUNCTS_THEN2 (LABEL_TAC "s") (K ALL_TAC))))) THEN
  ASM_CASES_TAC `i':num = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `(S:num->real^N) i' = S(SUC i)` THENL
   [(* i' is the next block: they share the disk at the edge [S i, S(SUC i)] *)
    SUBGOAL_THEN `i' MOD n = (SUC i) MOD n` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`S:num->real^N`; `n:num`] MOI_FTP_PER_EQ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "inj" ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(S:num->real^N)(i' + n - 1) = S i /\ (cS:num->real^N)(i' + n - 1) = cS i /\
                  (cF:num->real^N)(i' + n - 1) = cF i`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `SUC i + n - 1 = i + n` ASSUME_TAC THENL
       [UNDISCH_TAC `0 < n` THEN ARITH_TAC; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `i':num`; `SUC i`; `n - 1`] MOI_FTP_PER_SHIFT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN USE_THEN "per" ACCEPT_TAC;
        MP_TAC(ISPECL [`cS:num->real^N`; `n:num`; `i':num`; `SUC i`; `n - 1`] MOI_FTP_PER_SHIFT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN USE_THEN "pS" ACCEPT_TAC;
        MP_TAC(ISPECL [`cF:num->real^N`; `n:num`; `i':num`; `SUC i`; `n - 1`] MOI_FTP_PER_SHIFT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN USE_THEN "pF" ACCEPT_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i))`;
                   `IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i'))`;
                   `moi_ftp_bw (t:(real^N->bool)->bool) l h n S Q As AF i`;
                   `moi_ftp_bw (t:(real^N->bool)->bool) l h n S Q As AF i'`;
                   `IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i) INTER
                                              derived_dual_cell t l (S(SUC i)))`]
      MOI_FTP_SHARE) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN(MATCH_ACCEPT_TAC o SPEC `j:num`)] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "hinj" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      USE_THEN "s'" ACCEPT_TAC;
      X_GEN_TAC `j0:num` THEN USE_THEN "d2" (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN
       `derived_dual_cell t l ((S:num->real^N)(SUC i)) INTER derived_dual_cell t l (S i) =
        derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(SUC i)) /\
        derived_dual_cell t l ((S:num->real^N)(SUC i)) INTER derived_dual_cell t l (S i) INTER
        derived_frontier t l =
        derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(SUC i)) INTER
        derived_frontier t l /\
        midpoint((S:num->real^N)(SUC i),S i) = midpoint(S i,S(SUC i))`
      (LABEL_TAC "nrm") THENL
       [REWRITE_TAC[MIDPOINT_SYM] THEN SET_TAC[]; ALL_TAC] THEN
      USE_THEN "d1'" (MP_TAC o SPEC `j0:num`) THEN
      REWRITE_TAC[ASSUME `(S:num->real^N) i' = S(SUC i)`;
                  ASSUME `(S:num->real^N)(i' + n - 1) = S i`;
                  ASSUME `(cS:num->real^N)(i' + n - 1) = cS i`;
                  ASSUME `(cF:num->real^N)(i' + n - 1) = cF i`] THEN
      USE_THEN "nrm" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(S:num->real^N) i' = S(i + n - 1)` THENL
   [(* i' is the previous block: they share the disk at [S(i + n - 1), S i] *)
    SUBGOAL_THEN `i' MOD n = (i + n - 1) MOD n` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`S:num->real^N`; `n:num`] MOI_FTP_PER_EQ) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN USE_THEN "inj" ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(S:num->real^N)(SUC i') = S i /\ (cS:num->real^N) i' = cS(i + n - 1) /\
                  (cF:num->real^N) i' = cF(i + n - 1)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(i + n - 1) + 1 = i + n /\ SUC i' = i' + 1` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `0 < n` THEN ARITH_TAC; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `i':num`; `i + n - 1`; `1`] MOI_FTP_PER_SHIFT) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN USE_THEN "per" ACCEPT_TAC;
        MP_TAC(ISPECL [`cS:num->real^N`; `n:num`; `i':num`; `i + n - 1`; `0`] MOI_FTP_PER_SHIFT) THEN
        ASM_REWRITE_TAC[ADD_CLAUSES];
        MP_TAC(ISPECL [`cF:num->real^N`; `n:num`; `i':num`; `i + n - 1`; `0`] MOI_FTP_PER_SHIFT) THEN
        ASM_REWRITE_TAC[ADD_CLAUSES]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i))`;
                   `IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i'))`;
                   `moi_ftp_bw (t:(real^N->bool)->bool) l h n S Q As AF i`;
                   `moi_ftp_bw (t:(real^N->bool)->bool) l h n S Q As AF i'`;
                   `IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i) INTER
                                              derived_dual_cell t l (S(i + n - 1)))`]
      MOI_FTP_SHARE) THEN
    ANTS_TAC THENL [ALL_TAC; DISCH_THEN(MATCH_ACCEPT_TAC o SPEC `j:num`)] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "hinj" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      USE_THEN "s'" ACCEPT_TAC;
      X_GEN_TAC `j0:num` THEN USE_THEN "d1" (fun th -> REWRITE_TAC[th]) THEN
      SUBGOAL_THEN
       `derived_dual_cell t l ((S:num->real^N)(i + n - 1)) INTER derived_dual_cell t l (S i) =
        derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(i + n - 1)) /\
        derived_dual_cell t l ((S:num->real^N)(i + n - 1)) INTER derived_dual_cell t l (S i) INTER
        derived_frontier t l =
        derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(i + n - 1)) INTER
        derived_frontier t l /\
        midpoint((S:num->real^N)(i + n - 1),S i) = midpoint(S i,S(i + n - 1))`
      (LABEL_TAC "nrm") THENL
       [REWRITE_TAC[MIDPOINT_SYM] THEN SET_TAC[]; ALL_TAC] THEN
      USE_THEN "d2'" (MP_TAC o SPEC `j0:num`) THEN
      REWRITE_TAC[ASSUME `(S:num->real^N) i' = S(i + n - 1)`;
                  ASSUME `(S:num->real^N)(SUC i') = S i`;
                  ASSUME `(cS:num->real^N) i' = cS(i + n - 1)`;
                  ASSUME `(cF:num->real^N) i' = cF(i + n - 1)`] THEN
      USE_THEN "nrm" (fun th -> REWRITE_TAC[th]) THEN DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  (* non-adjacent blocks are disjoint *)
  SUBGOAL_THEN `derived_dual_cell t l ((S:num->real^N) i) INTER
                derived_dual_cell t l (S i') = {}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CELLS_DISJOINT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(i':num = i)` THEN REWRITE_TAC[] THEN
      USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      USE_THEN "deg" (MP_TAC o SPECL [`i:num`; `(S:num->real^N) i'`]) THEN
      REWRITE_TAC[ASSUME `segment[(S:num->real^N) i,S i'] IN l`;
                  ASSUME `~((S:num->real^N) i' = S(SUC i))`;
                  ASSUME `~((S:num->real^N) i' = S(i + n - 1))`] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(i':num = i)` THEN REWRITE_TAC[] THEN
      USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!Y':real^N->bool. Y INTER Y' = {} /\ W' SUBSET Y'
                         ==> Y INTER W' SUBSET W`) THEN
  EXISTS_TAC `IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i'))` THEN
  CONJ_TAC THENL
   [USE_THEN "hinj" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[IMAGE_CLAUSES];
    USE_THEN "s'" MATCH_ACCEPT_TAC]);;

(* ========================================================================= *)
(* The cell structure of the union of the dual cells of the                 *)
(* polygon vertices: the global disk sets ZA j (the k-images of the block   *)
(* disk sets), their traces on the blocks, the intersection structures of   *)
(* the block labels and of the disk labels, and the cells CA a INTER ZA j   *)
(* (pulled back from the level picture by tubec's MOI_FTC_PULL_CELLS).      *)
(* ========================================================================= *)

let MOI_FTP_NXPV_PER = prove
 (`!(f:num->A) n i.
     0 < n /\ (!i. f(i + n) = f i) /\ i < n
     ==> f(moi_ftp_nx n i) = f(SUC i) /\ f(moi_ftp_pv n i) = f(i + n - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_ftp_nx; moi_ftp_pv] THEN
  CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN UNDISCH_TAC `0 < n` THEN ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
    SUBGOAL_THEN `(i - 1) + n = i + n - 1` (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC [`~(i = 0)`; `0 < n`] THEN ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC]]);;

(* The global disk sets of the polygon and their traces on the blocks. *)

let moi_ftp_za = new_definition
 `moi_ftp_za (t:(real^N->bool)->bool) l (h:real^N->real^N) (k:real^N->real^N) (n:num)
             (S:num->real^N) Q As AF (j:num) =
    UNIONS {IMAGE k (moi_ftp_bw t l h n S Q As AF i j) | i | i < n}`;;

let MOI_FTP_DOM_TRACE = prove
 (`!(t:(real^N->bool)->bool) l V h k n (S:num->real^N) cS cF Q As AF bs b1.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. S i IN V) /\ (!i. {S i} IN l) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)) /\
     (!i. cS(i + n) = cS i) /\ (!i. cF(i + n) = cF i) /\
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1
     ==> !i j. i < n
               ==> IMAGE h (derived_dual_cell t l (S i) INTER moi_ftp_za t l h k n S Q As AF j) =
                   moi_ftp_bw t l h n S Q As AF i j /\
                   derived_dual_cell t l (S i) INTER moi_ftp_za t l h k n S Q As AF j =
                   IMAGE k (moi_ftp_bw t l h n S Q As AF i j)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "cons" o MATCH_MP MOI_FTP_BLOCKS_CONS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  ABBREV_TAC `U = UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))` THEN
  SUBGOAL_THEN
   `(!x:real^N. x IN U ==> h x IN U /\ k (h x) = x) /\
    (!y:real^N. y IN U ==> k y IN U /\ h (k y) = y) /\
    (!a. derived_dual_cell t l ((S:num->real^N) a) SUBSET U)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) 0`]
      MOI_FTC_LEV_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `pl_homeomorphism (U:real^N->bool,U) (h,k)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `a:num` THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) a`]
      MOI_FTC_LEV_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (S:num->real^N) a IN s}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`; `U:real^N->bool`;
                 `\i. derived_dual_cell t l ((S:num->real^N) i)`;
                 `moi_ftp_bw (t:(real^N->bool)->bool) l h n S Q As AF`; `n:num`]
    MOI_FTP_GLUE_IMAGE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
     (REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^N`;
                     `n:num`; `S:num->real^N`; `cS:num->real^N`; `cF:num->real^N`;
                     `Q:num->real^N->bool`; `As:num->real^N->bool`; `AF:num->real^N->bool`;
                     `bs:num->real^N`; `b1:num->real^N`; `i:num`] MOI_FTP_BLOCK_PKG) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]);
    DISCH_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^N)
                  (derived_dual_cell t l ((S:num->real^N) i) INTER
                   moi_ftp_za t l h k n S Q As AF j) =
                moi_ftp_bw t l h n S Q As AF i j` ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftp_za] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) o check
    (fun th -> concl th = `IMAGE (h:real^N->real^N)
                  (derived_dual_cell t l ((S:num->real^N) i) INTER
                   moi_ftp_za t l h k n S Q As AF j) =
                moi_ftp_bw t l h n S Q As AF i j`)) THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (f:real^N->real^N) x = x) ==> s = IMAGE f s`) THEN
  REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN U` (fun th -> ASM_SIMP_TAC[th]) THEN ASM SET_TAC[]);;

(* Global intersection structure from the block-wise one. *)

let MOI_FTP_UNION_INTER = prove
 (`!(C:num->A->bool) (B:num->num->A->bool) (Z:num->A->bool) n (R:num->num->num->bool) j j'.
     (!j. Z j = UNIONS {B i j | i | i < n}) /\ (!i j. i < n ==> C i INTER Z j = B i j) /\
     (!i. i < n ==> B i j INTER B i j' = UNIONS {B i j'' | j'' | R j j' j''})
     ==> Z j INTER Z j' = UNIONS {Z j'' | j'' | R j j' j''}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `i':num` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:A) IN B (i:num) (j':num)` ASSUME_TAC THENL
     [FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME `i:num < n`))]) o
        check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `(C:num->A->bool)`)) (concl th))) THEN
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `j:num` (MATCH_MP th (ASSUME `i:num < n`)))) o
          check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `(C:num->A->bool)`)) (concl th))) THEN
        ASM SET_TAC[];
        ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `i':num` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:A) IN B (i:num) (j:num) INTER B i j'` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < n`)]) o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `R:num->num->num->bool`))
                         (concl th))) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `j'':num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j'':num` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:num` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `j'':num` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(x:A) IN B (i:num) (j:num) INTER B i j'` MP_TAC THENL
     [FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < n`)]) o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `R:num->num->num->bool`))
                           (concl th))) THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `j'':num` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN CONJ_TAC THEN EXISTS_TAC `i:num` THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_FTP_DOM_ZA = prove
 (`!(t:(real^N->bool)->bool) l V h k n (S:num->real^N) cS cF Q As AF bs b1.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. S i IN V) /\ (!i. {S i} IN l) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)) /\
     (!i. cS(i + n) = cS i) /\ (!i. cF(i + n) = cF i) /\
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1
     ==> !j j'. j < 9 /\ j' < 9
                ==> moi_ftp_za t l h k n S Q As AF j INTER moi_ftp_za t l h k n S Q As AF j' =
                    UNIONS {moi_ftp_za t l h k n S Q As AF j'' | j'' |
                            j'' < 9 /\ moi_ftc_dface j j'' /\ moi_ftc_dface j' j''}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "tr" o MATCH_MP MOI_FTP_DOM_TRACE) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `U = UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))` THEN
  SUBGOAL_THEN
   `(!y:real^N. y IN U ==> h (k y) = y) /\
    (!i j. i < n ==> moi_ftp_bw t l h n S Q As AF i j SUBSET (U:real^N->bool))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) 0`]
      MOI_FTC_LEV_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `pl_homeomorphism (U:real^N->bool,U) (h,k)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j0:num`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^N`;
                   `n:num`; `S:num->real^N`; `cS:num->real^N`; `cF:num->real^N`;
                   `Q:num->real^N->bool`; `As:num->real^N->bool`; `AF:num->real^N->bool`;
                   `bs:num->real^N`; `b1:num->real^N`; `i:num`] MOI_FTP_BLOCK_PKG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `j0:num` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) i`]
      MOI_FTC_LEV_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `derived_dual_cell t l ((S:num->real^N) i) SUBSET U` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (S:num->real^N) i IN s}` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o check (fun th ->
      concl th = `IMAGE (h:real^N->real^N) U = U`)) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i. derived_dual_cell t l ((S:num->real^N) i)`;
                 `\i j. IMAGE (k:real^N->real^N) (moi_ftp_bw t l h n S Q As AF i j)`;
                 `moi_ftp_za (t:(real^N->bool)->bool) l h k n S Q As AF`; `n:num`;
                 `\j j' j''. j'' < 9 /\ moi_ftc_dface j j'' /\ moi_ftc_dface j' j''`;
                 `j:num`; `j':num`] MOI_FTP_UNION_INTER) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_ftp_za];
    REPEAT STRIP_TAC THEN USE_THEN "tr" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < n`)]);
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^N`;
                   `n:num`; `S:num->real^N`; `cS:num->real^N`; `cF:num->real^N`;
                   `Q:num->real^N->bool`; `As:num->real^N->bool`; `AF:num->real^N->bool`;
                   `bs:num->real^N`; `b1:num->real^N`; `i:num`] MOI_FTP_BLOCK_PKG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`j:num`; `j':num`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
               CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `IMAGE (k:real^N->real^N) (moi_ftp_bw t l h n S Q As AF i j) INTER
      IMAGE k (moi_ftp_bw t l h n S Q As AF i j') =
      IMAGE k (moi_ftp_bw t l h n S Q As AF i j INTER moi_ftp_bw t l h n S Q As AF i j')`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTA_IMAGE_INTER_INJ THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `U:real^N->bool`] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      can (find_term ((=) `moi_ftc_dface`)) (concl th))) THEN
    MATCH_MP_TAC MOI_FTC_IMAGE_UNIONS1 THEN REWRITE_TAC[]]);;

(* The cells of block i in the original world. *)

let MOI_FTP_BLK_ORIG = prove
 (`!(t:(real^N->bool)->bool) l V h k n (S:num->real^N) cS cF Q As AF bs b1.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. S i IN V) /\ (!i. {S i} IN l) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)) /\
     (!i. cS(i + n) = cS i) /\ (!i. cF(i + n) = cF i) /\
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1
     ==> !i j. i < n /\ j < 9
               ==> pl_cell_with_boundary (1 + moi_ftc_dd j)
                     (derived_dual_cell t l (S i) INTER moi_ftp_za t l h k n S Q As AF j)
                     ((derived_dual_cell t l (S i) INTER
                       UNIONS {moi_ftp_za t l h k n S Q As AF j' | j' |
                               j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}) UNION
                      (((derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(i + n - 1))) UNION
                        (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(SUC i)))) INTER
                       moi_ftp_za t l h k n S Q As AF j)) /\
                   pl_cell_with_boundary (moi_ftc_dd j)
                     ((derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(i + n - 1))) INTER
                      moi_ftp_za t l h k n S Q As AF j)
                     ((derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(i + n - 1))) INTER
                      UNIONS {moi_ftp_za t l h k n S Q As AF j' | j' |
                              j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "tr" o MATCH_MP MOI_FTP_DOM_TRACE) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) i`]
    MOI_FTC_LEV_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^N`;
                 `n:num`; `S:num->real^N`; `cS:num->real^N`; `cF:num->real^N`;
                 `Q:num->real^N->bool`; `As:num->real^N->bool`; `AF:num->real^N->bool`;
                 `bs:num->real^N`; `b1:num->real^N`; `i:num`] MOI_FTP_BLOCK_PKG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`h:real^N->real^N`; `k:real^N->real^N`;
                 `UNIONS (moi_ftc_cs (barycentric_subdivision t) (V:real^N->bool))`;
                 `derived_dual_cell t l ((S:num->real^N) i)`;
                 `derived_dual_cell t l ((S:num->real^N) i) INTER
                  derived_dual_cell t l (S(i + n - 1))`;
                 `derived_dual_cell t l ((S:num->real^N) i) INTER
                  derived_dual_cell t l (S(SUC i))`;
                 `moi_ftp_za (t:(real^N->bool)->bool) l h k n S Q As AF`;
                 `moi_ftp_bw (t:(real^N->bool)->bool) l h n S Q As AF i`;
                 `IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i) INTER
                                            derived_dual_cell t l (S(i + n - 1)))`;
                 `IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i) INTER
                                            derived_dual_cell t l (S(SUC i)))`]
    MOI_FTC_PULL_CELLS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (S:num->real^N) i IN s}` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      USE_THEN "tr" (fun th -> REWRITE_TAC[CONJUNCT1(SPEC `j':num` (MATCH_MP th (ASSUME `i:num < n`)))])];
    DISCH_THEN(ACCEPT_TAC o C MP (ASSUME `j < 9`) o SPEC `j:num`)]);;

(* The cells CA a INTER ZA j of the polygon in the form of                  *)
(* MOI_FTC_PROD_ASSEMBLY (block labels: arcs a < n and beads n + b).        *)

let MOI_FTP_DOM_CELLS = prove
 (`!(t:(real^N->bool)->bool) l V h k n (S:num->real^N) cS cF Q As AF bs b1.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. S i IN V) /\ (!i. {S i} IN l) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)) /\
     (!i. cS(i + n) = cS i) /\ (!i. cF(i + n) = cF i) /\
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1
     ==> !a j. a < n + n /\ j < 9
               ==> pl_cell_with_boundary (moi_ftp_bdim n a + moi_ftc_dd j)
                     (moi_ftp_cb n (\i. derived_dual_cell t l (S i)) a INTER
                      moi_ftp_za t l h k n S Q As AF j)
                     ((moi_ftp_cb n (\i. derived_dual_cell t l (S i)) a INTER
                       UNIONS {moi_ftp_za t l h k n S Q As AF j' | j' |
                               j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}) UNION
                      (UNIONS {moi_ftp_cb n (\i. derived_dual_cell t l (S i)) a' | a' |
                               a' < n + n /\ moi_ftp_bface n a a' /\ ~(a' = a)} INTER
                       moi_ftp_za t l h k n S Q As AF j))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "orig" o MATCH_MP MOI_FTP_BLK_ORIG) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `j:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `0 < n` ASSUME_TAC THENL [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `a:num < n` THENL
   [(* an arc *)
    MP_TAC(SPECL [`n:num`; `a:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `a:num`] MOI_FTP_NXPV_PER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `UNIONS {moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i)) a' | a' |
              a' < n + n /\ moi_ftp_bface n a a' /\ ~(a' = a)} =
      (derived_dual_cell t l (S a) INTER derived_dual_cell t l (S(a + n - 1))) UNION
      (derived_dual_cell t l (S a) INTER derived_dual_cell t l (S(SUC a)))`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `{moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i)) a' | a' |
         a' < n + n /\ moi_ftp_bface n a a' /\ ~(a' = a)} =
        {moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i)) (n + a),
         moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i)) (n + moi_ftp_pv n a)}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY; moi_ftp_bface] THEN
        X_GEN_TAC `x:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `n + a < n + n /\ n + moi_ftp_pv n a < n + n /\ ~(n + a = a) /\
                      ~(n + moi_ftp_pv n a = a)` STRIP_ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`a:num < n`; `moi_ftp_pv n a < n`; `0 < n`] THEN ARITH_TAC;
          ALL_TAC] THEN
        EQ_TAC THENL
         [DISCH_THEN(X_CHOOSE_THEN `a':num` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
          ASM_MESON_TAC[];
          STRIP_TAC THENL
           [EXISTS_TAC `n + a:num`; EXISTS_TAC `n + moi_ftp_pv n a`] THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[UNIONS_2; moi_ftp_cb] THEN
      SUBGOAL_THEN `~(n + a < n) /\ ~(n + moi_ftp_pv n a < n) /\ (n + a) - n = a /\
                    (n + moi_ftp_pv n a) - n = moi_ftp_pv n a` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_ftp_pv n a < n` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_ftp_cb; moi_ftp_bdim] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "orig" (fun th -> ACCEPT_TAC(CONJUNCT1(MATCH_MP th
      (CONJ (ASSUME `a:num < n`) (ASSUME `j < 9`)))));
    (* a bead *)
    ABBREV_TAC `b = a - n:num` THEN
    SUBGOAL_THEN `a = n + b:num /\ b < n` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`a - n:num = b`; `~(a:num < n)`; `a:num < n + n`] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`n:num`; `b:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `{moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i)) a' | a' |
       a' < n + n /\ moi_ftp_bface n (n + b) a' /\ ~(a' = n + b)} = {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; moi_ftp_bface;
                  ARITH_RULE `~(n + b:num < n)`] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[UNIONS_0; INTER_EMPTY; UNION_EMPTY; moi_ftp_cb; moi_ftp_bdim;
                ARITH_RULE `~(n + b:num < n)`; ADD_SUB2; ADD_CLAUSES] THEN
    USE_THEN "orig" (fun th -> MP_TAC(CONJUNCT2(MATCH_MP (SPECL [`moi_ftp_nx n b`; `j:num`] th)
      (CONJ (ASSUME `moi_ftp_nx n b < n`) (ASSUME `j < 9`))))) THEN
    SUBGOAL_THEN `(S:num->real^N)(moi_ftp_nx n b + n - 1) = S b` SUBST1_TAC THENL
     [REWRITE_TAC[moi_ftp_nx] THEN COND_CASES_TAC THENL
       [REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN UNDISCH_TAC `SUC b = n` THEN ARITH_TAC;
        SUBGOAL_THEN `SUC b + n - 1 = b + n` SUBST1_TAC THENL
         [UNDISCH_TAC `0 < n` THEN ARITH_TAC; ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `derived_dual_cell t l ((S:num->real^N)(moi_ftp_nx n b)) INTER
                  derived_dual_cell t l (S b) =
                  derived_dual_cell t l (S b) INTER derived_dual_cell t l (S(moi_ftp_nx n b))`
    SUBST1_TAC THENL [REWRITE_TAC[INTER_COMM]; SIMP_TAC[]]]);;

(* The level homeomorphism fixes the half edges of the graph. *)

let MOI_FTP_HALF_FIX = prove
 (`!(t:(real^N->bool)->bool) l V h k v w.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ v IN V /\ {v} IN l /\
     segment[v,w] IN t /\ ~(v = w)
     ==> IMAGE h (segment[v,midpoint(v,w)]) = segment[v,midpoint(v,w)]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `v:real^N`] MOI_FTC_LEV_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> try fst(dest_const t) = "face_of" with Failure _ -> false))
        (concl th))) THEN
  EXISTS_TAC `segment[v:real^N,midpoint(v,w)]` THEN
  REWRITE_TAC[ENDS_IN_SEGMENT] THEN
  SIMP_TAC[FACE_OF_REFL; CONVEX_SEGMENT] THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  EXISTS_TAC `{{v:real^N}, segment[v,w]}` THEN
  REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT;
              GSYM SEGMENT_CONVEX_HULL] THEN
  REWRITE_TAC[moi_bar_chain; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_subcomplex]) THEN
  SUBGOAL_THEN `{v:real^N} IN t` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; SEGMENT_EQ_EMPTY;
                  SET_RULE `~({} = {a:real^N})`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  REWRITE_TAC[SING_SUBSET; ENDS_IN_SEGMENT]);;

(* The two disk sets 0 and 1 cover each block. *)

let MOI_FTP_BLK_COVER = prove
 (`!(t:(real^N->bool)->bool) l V h k n (S:num->real^N) cS cF Q As AF bs b1 i.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ S i IN V /\ {S i} IN l /\
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1 /\ i < n
     ==> IMAGE h (derived_dual_cell t l (S i)) =
         moi_ftp_bw t l h n S Q As AF i 0 UNION moi_ftp_bw t l h n S Q As AF i 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_ftp_blocks (t:(real^N->bool)->bool) l h n S cS cF Q As AF bs b1` THEN
  REWRITE_TAC[moi_ftp_blocks] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `L = UNIONS (simplicial_link (barycentric_subdivision t) ((S:num->real^N) i))` THEN
  ABBREV_TAC `Y = IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i))` THEN
  SUBGOAL_THEN `(Q:num->real^N->bool) i UNION ((L DIFF Q i) UNION (As i UNION AF i)) = L`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FTP_AB_F1 o
      (fun th -> CONJ th (CONJ (REFL `(As:num->real^N->bool) i UNION AF i`)
        (REFL `(L DIFF (Q:num->real^N->bool) i) UNION (As i UNION AF i)`)))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Y:real^N->bool) SUBSET moi_ftc_cone ((S:num->real^N) i) L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) i`]
      MOI_FTC_LEV_STAR) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) i`]
      MOI_FTC_HRAD) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftp_bw; moi_ftc_zd] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `moi_ftc_cone ((S:num->real^N) i) (Q i) UNION
    moi_ftc_cone (S i) ((L DIFF Q i) UNION (As i UNION AF i)) = moi_ftc_cone (S i) L`
  MP_TAC THENL
   [REWRITE_TAC[moi_ftc_cone; GSYM MOI_FTC_CONE_UNION] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `(Y:real^N->bool) SUBSET moi_ftc_cone ((S:num->real^N) i) L` THEN
    SET_TAC[]]);;

(* The block labels of the polygon form a necklace. *)

let MOI_FTP_DOM_NECK = prove
 (`!(t:(real^N->bool)->bool) l n (S:num->real^N).
     graph_in_complex t l /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. {S i} IN l) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i))
     ==> !a a'. a < n + n /\ a' < n + n
                ==> moi_ftp_cb n (\i. derived_dual_cell t l (S i)) a INTER
                    moi_ftp_cb n (\i. derived_dual_cell t l (S i)) a' =
                    UNIONS {moi_ftp_cb n (\i. derived_dual_cell t l (S i)) a'' | a'' |
                            a'' < n + n /\ moi_ftp_bface n a a'' /\ moi_ftp_bface n a' a''}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (LABEL_TAC "per") (CONJUNCTS_THEN2 (LABEL_TAC "inj") (CONJUNCTS_THEN2 (LABEL_TAC "inl")
    (LABEL_TAC "deg")))))) THEN
  SUBGOAL_THEN `0 < n` ASSUME_TAC THENL [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FTP_NECKLACE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `i:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `i:num`] MOI_FTP_NXPV_PER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CELLS_DISJOINT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[] THEN
      USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      USE_THEN "deg" (MP_TAC o SPECL [`i:num`; `(S:num->real^N) j`]) THEN
      SUBGOAL_THEN `~((S:num->real^N) j = S i)` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(i:num = j)` THEN REWRITE_TAC[] THEN
        USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[ASSUME `~((S:num->real^N) j = S i)`;
                  ASSUME `segment[(S:num->real^N) i,S j] IN l`] THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th ->
        concl th = `(S:num->real^N)(moi_ftp_nx n i) = S(SUC i)`)) THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th ->
        concl th = `(S:num->real^N)(moi_ftp_pv n i) = S(i + n - 1)`)) THEN
      STRIP_TAC THENL
       [SUBGOAL_THEN `j = moi_ftp_pv n i` ASSUME_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `~(i = moi_ftp_nx n j)` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `~(j = moi_ftp_nx n i)` THEN REWRITE_TAC[] THEN
        USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    MATCH_MP_TAC MOI_FTC_TRIPLE THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    DISCH_TAC THENL
     [UNDISCH_TAC `~(moi_ftp_nx n i = i)`; UNDISCH_TAC `~(j:num = i)`;
      UNDISCH_TAC `~(j = moi_ftp_nx n i)`] THEN
    REWRITE_TAC[] THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The cells cover the union of the dual cells of the polygon vertices. *)

let MOI_FTP_DOM_UNION = prove
 (`!(t:(real^N->bool)->bool) l V h k n (S:num->real^N) cS cF Q As AF bs b1.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. S i IN V) /\ (!i. {S i} IN l) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)) /\
     (!i. cS(i + n) = cS i) /\ (!i. cF(i + n) = cF i) /\
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1
     ==> UNIONS {moi_ftp_cb n (\i. derived_dual_cell t l (S i)) a INTER
                 moi_ftp_za t l h k n S Q As AF j | a,j | a < n + n /\ j < 9} =
         UNIONS {derived_dual_cell t l (S i) | i | i < n}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "tr" o MATCH_MP MOI_FTP_DOM_TRACE) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `c:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET u ==> s INTER z SUBSET u`) THEN
    REWRITE_TAC[moi_ftp_cb] THEN BETA_TAC THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN f ==> s INTER t SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `a - n:num` THEN REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`a:num < n + n`; `~(a:num < n)`] THEN ARITH_TAC];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `n:num`; `S:num->real^N`;
                   `cS:num->real^N`; `cF:num->real^N`; `Q:num->real^N->bool`;
                   `As:num->real^N->bool`; `AF:num->real^N->bool`; `bs:num->real^N`;
                   `b1:num->real^N`; `i:num`] MOI_FTP_BLK_COVER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) i`]
      MOI_FTC_LEV_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS (moi_ftc_cs (barycentric_subdivision t) V)`
    ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(x:real^N) IN derived_dual_cell t l ((S:num->real^N) i)`;
        `derived_dual_cell t l ((S:num->real^N) i) SUBSET
         UNIONS {s | s IN barycentric_subdivision t /\ S i IN s}`;
        `UNIONS {s | s IN barycentric_subdivision t /\ (S:num->real^N) i IN s} SUBSET
         UNIONS (moi_ftc_cs (barycentric_subdivision t) V)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^N) x IN moi_ftp_bw t l h n S Q As AF i 0 \/
                  h x IN moi_ftp_bw t l h n S Q As AF i 1` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^N->real^N) (derived_dual_cell t l ((S:num->real^N) i)) =
                   moi_ftp_bw t l h n S Q As AF i 0 UNION moi_ftp_bw t l h n S Q As AF i 1` THEN
      UNDISCH_TAC `(x:real^N) IN derived_dual_cell t l ((S:num->real^N) i)` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN STRIP_TAC THENL
     [EXISTS_TAC `moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i)) i INTER
                  moi_ftp_za t l h k n S Q As AF 0` THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`i:num`; `0`] THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i:num < n` THEN ARITH_TAC;
        ALL_TAC];
      EXISTS_TAC `moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i)) i INTER
                  moi_ftp_za t l h k n S Q As AF 1` THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`i:num`; `1`] THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i:num < n` THEN ARITH_TAC;
        ALL_TAC]] THEN
    ASM_REWRITE_TAC[moi_ftp_cb] THEN
    USE_THEN "tr" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC_ALL(MATCH_MP th (ASSUME `i:num < n`)))]) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:real^N->real^N) x` THEN ASM_SIMP_TAC[]]);;

(* The core cells: the half edges of the polygon at its vertices. *)

let MOI_FTP_DOM_CORE = prove
 (`!(t:(real^N->bool)->bool) l V h k n (S:num->real^N) cS cF Q As AF bs b1.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. S i IN V) /\ (!i. {S i} IN l) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)) /\
     (!i. cS(i + n) = cS i) /\ (!i. cF(i + n) = cF i) /\
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1
     ==> UNIONS {moi_ftp_cb n (\i. derived_dual_cell t l (S i)) a INTER
                 moi_ftp_za t l h k n S Q As AF 6 | a | a < n + n} =
         UNIONS {segment[S i,S(SUC i)] | i | i < n}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(LABEL_TAC "tr" o MATCH_MP MOI_FTP_DOM_TRACE) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (fun th -> is_conj(concl th))) THEN
  SUBGOAL_THEN `0 < n` ASSUME_TAC THENL [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  (* the core trace of block i *)
  SUBGOAL_THEN
   `!i. i < n
        ==> derived_dual_cell t l ((S:num->real^N) i) INTER moi_ftp_za t l h k n S Q As AF 6 =
            segment[S i,midpoint(S i,S(i + n - 1))] UNION segment[S i,midpoint(S i,S(SUC i))]`
  (LABEL_TAC "ct") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    USE_THEN "tr" (fun th -> REWRITE_TAC[CONJUNCT2(SPEC `6` (MATCH_MP th (ASSUME `i:num < n`)))]) THEN
    REWRITE_TAC[moi_ftp_bw; moi_ftc_zd] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[IMAGE_UNION] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) i`]
      MOI_FTC_LEV_BASICS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex] o check (fun th ->
      is_comb(concl th) &&
      fst(strip_comb(concl th)) = `graph_in_complex:((real^N->bool)->bool)->((real^N->bool)->bool)->bool`)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_subcomplex] o check (fun th ->
      is_comb(concl th) &&
      fst(strip_comb(concl th)) = `simplicial_subcomplex:((real^N->bool)->bool)->((real^N->bool)->bool)->bool`)) THEN
    SUBGOAL_THEN `!w. ~(w = (S:num->real^N) i) /\ segment[S i,w] IN l
                      ==> IMAGE (k:real^N->real^N) (segment[S i,midpoint(S i,w)]) =
                          segment[S i,midpoint(S i,w)]` (LABEL_TAC "hk") THENL
     [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                     `h:real^N->real^N`; `k:real^N->real^N`; `(S:num->real^N) i`; `w:real^N`]
        MOI_FTP_HALF_FIX) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `(l:(real^N->bool)->bool) SUBSET t`)) THEN
        FIRST_ASSUM ACCEPT_TAC;
        DISCH_TAC] THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
      REWRITE_TAC[GSYM IMAGE_o] THEN
      MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (f:real^N->real^N) x = x) ==> IMAGE f s = s`) THEN
      REWRITE_TAC[o_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(k:real^N->real^N) ((h:real^N->real^N) y)`)) (concl th))) THEN
      SUBGOAL_THEN `segment[(S:num->real^N) i,midpoint(S i,w)] SUBSET
                    UNIONS (moi_ftc_cs (barycentric_subdivision t) V)` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `UNIONS {s | s IN barycentric_subdivision t /\ (S:num->real^N) i IN s}` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN f ==> s SUBSET UNIONS f`) THEN
        REWRITE_TAC[IN_ELIM_THM; ENDS_IN_SEGMENT] THEN
        REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `{{(S:num->real^N) i}, segment[S i,w]}` THEN
        REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; MOI_FTA_BARY_SEGMENT;
                    GSYM SEGMENT_CONVEX_HULL] THEN
        REWRITE_TAC[moi_bar_chain; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
        SUBGOAL_THEN `{(S:num->real^N) i} IN t /\ segment[S i,w] IN t` STRIP_ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; SEGMENT_EQ_EMPTY;
                        SET_RULE `~({} = {a:real^N})`] THEN
        REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
        REWRITE_TAC[SING_SUBSET; ENDS_IN_SEGMENT];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    BINOP_TAC THEN USE_THEN "hk" MATCH_MP_TAC THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `segment[(S:num->real^N) i,w]`)) (concl th) &&
      can (find_term ((=) `(S:num->real^N)(SUC i)`)) (concl th))) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  (* both unions *)
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?i. i < n /\
                      (x:real^N) IN derived_dual_cell t l (S i) INTER
                                    moi_ftp_za t l h k n S Q As AF 6`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i)) a
                                 INTER moi_ftp_za t l h k n S Q As AF 6` THEN
      REWRITE_TAC[moi_ftp_cb] THEN BETA_TAC THEN COND_CASES_TAC THENL
       [DISCH_TAC THEN EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN EXISTS_TAC `a - n:num` THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`a:num < n + n`; `~(a:num < n)`] THEN ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN derived_dual_cell t l ((S:num->real^N) i) INTER
                              moi_ftp_za t l h k n S Q As AF 6` THEN
    USE_THEN "ct" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < n`)]) THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [EXISTS_TAC `moi_ftp_pv n i` THEN
      MP_TAC(SPECL [`n:num`; `i:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(S:num->real^N)(moi_ftp_pv n i) = S(i + n - 1) /\
                    S(SUC(moi_ftp_pv n i)) = S i` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `i:num`] MOI_FTP_NXPV_PER) THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[];
          MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `moi_ftp_pv n i`] MOI_FTP_NXPV_PER) THEN
          ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^N) IN segment[S i,midpoint(S i,S(i + n - 1))]` THEN
      SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN REWRITE_TAC[MIDPOINT_IN_SEGMENT; ENDS_IN_SEGMENT];
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^N) IN segment[S i,midpoint(S i,S(SUC i))]` THEN
      SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT; MIDPOINT_IN_SEGMENT]];
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `segment[(S:num->real^N) i,S(SUC i)] =
                  segment[S i,midpoint(S i,S(SUC i))] UNION
                  segment[S(SUC i),midpoint(S(SUC i),S i)]` MP_TAC THENL
     [SUBGOAL_THEN `midpoint((S:num->real^N)(SUC i),S i) = midpoint(S i,S(SUC i))`
      SUBST1_TAC THENL [REWRITE_TAC[MIDPOINT_SYM]; ALL_TAC] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SEGMENT_SYM] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC UNION_SEGMENT THEN
      REWRITE_TAC[MIDPOINT_IN_SEGMENT];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `(x:real^N) IN segment[S i,S(SUC i)]` THEN
      REWRITE_TAC[th; IN_UNION]) THEN STRIP_TAC THENL
     [EXISTS_TAC `i:num` THEN CONJ_TAC THENL
       [UNDISCH_TAC `i:num < n` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[moi_ftp_cb] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "ct" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `i:num < n`)]) THEN
      ASM_REWRITE_TAC[IN_UNION];
      EXISTS_TAC `moi_ftp_nx n i` THEN
      MP_TAC(SPECL [`n:num`; `i:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONJ_TAC THENL [UNDISCH_TAC `moi_ftp_nx n i < n` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[moi_ftp_cb] THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "ct" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `moi_ftp_nx n i < n`)]) THEN
      MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `i:num`] MOI_FTP_NXPV_PER) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(S:num->real^N)(moi_ftp_nx n i + n - 1) = S i` SUBST1_TAC THENL
       [REWRITE_TAC[moi_ftp_nx] THEN COND_CASES_TAC THENL
         [REWRITE_TAC[ADD_CLAUSES] THEN AP_TERM_TAC THEN UNDISCH_TAC `SUC i = n` THEN ARITH_TAC;
          SUBGOAL_THEN `SUC i + n - 1 = i + n` SUBST1_TAC THENL
           [UNDISCH_TAC `0 < n` THEN ARITH_TAC; ASM_REWRITE_TAC[]]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_UNION]]]);;

(* ========================================================================= *)
(* The n-gon model of the circle factor.  The vertices                      *)
(* (0,0), (1,0), ..., (n-2,0), (n-2,1) of real^2 in this cyclic order: the *)
(* boundary of the triangle conv{(0,0),(n-2,0),(n-2,1)} with its bottom     *)
(* side cut into unit segments.  Edges moi_ftp_me n i, i < n.               *)
(* ========================================================================= *)

let moi_ftp_mw = new_definition
 `moi_ftp_mw (n:num) (i:num) =
    if i MOD n < n - 1 then vector[&(i MOD n); &0]:real^2 else vector[&(n - 2); &1]`;;

let moi_ftp_me = new_definition
 `moi_ftp_me (n:num) (i:num) = segment[moi_ftp_mw n i, moi_ftp_mw n (SUC i)]`;;

let MOI_FTP_MW_PER = prove
 (`!n i. moi_ftp_mw n (i + n) = moi_ftp_mw n i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftp_mw] THEN
  SUBGOAL_THEN `(i + n) MOD n = i MOD n` (fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`1`; `n:num`; `i:num`] (CONJUNCT1(CONJUNCT2(CONJUNCT2 MOD_MULT_ADD)))) THEN
  REWRITE_TAC[MULT_CLAUSES]);;

let MOI_FTP_ME_PER = prove
 (`!n i. moi_ftp_me n (i + n) = moi_ftp_me n i`,
  REWRITE_TAC[moi_ftp_me; ARITH_RULE `SUC(i + n) = SUC i + n`; MOI_FTP_MW_PER]);;

(* The three kinds of edges. *)

let MOI_FTP_ME_CASES = prove
 (`!n i. 3 <= n /\ i < n
         ==> (i < n - 2 ==> moi_ftp_me n i = segment[vector[&i;&0], vector[&i + &1;&0]]) /\
             (i = n - 2 ==> moi_ftp_me n i =
                            segment[vector[&(n - 2);&0], vector[&(n - 2);&1]]) /\
             (i = n - 1 ==> moi_ftp_me n i = segment[vector[&(n - 2);&1], vector[&0;&0]])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_ftp_me; moi_ftp_mw] THEN
  SUBGOAL_THEN `i MOD n = i` SUBST1_TAC THENL [ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(SUC i) MOD n = SUC i /\ i < n - 1 /\ SUC i < n - 1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC MOD_LT; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`i < n - 2`; `3 <= n`] THEN ARITH_TAC;
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC]];
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(SUC(n - 2)) MOD n = SUC(n - 2) /\ n - 2 < n - 1 /\ ~(SUC(n - 2) < n - 1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC MOD_LT; ALL_TAC] THEN
      UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(SUC(n - 1)) MOD n = 0 /\ ~(n - 1 < n - 1) /\ 0 < n - 1` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `SUC(n - 1) = n` SUBST1_TAC THENL
       [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOD_REFL; LT_REFL] THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
      ASM_REWRITE_TAC[]]]);;

(* Membership in the three kinds of edges. *)

let MOI_FTP_SEG_BOT = prove
 (`!a x:real^2. x IN segment[vector[a;&0], vector[a + &1;&0]] <=>
                x$2 = &0 /\ a <= x$1 /\ x$1 <= a + &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
    VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `(x:real^2)$1 - a` THEN ASM_REAL_ARITH_TAC]);;

let MOI_FTP_SEG_VERT = prove
 (`!a x:real^2. x IN segment[vector[a;&0], vector[a;&1]] <=>
                x$1 = a /\ &0 <= x$2 /\ x$2 <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
    VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `(x:real^2)$2` THEN ASM_REAL_ARITH_TAC]);;

let MOI_FTP_SEG_HYP = prove
 (`!a x:real^2. x IN segment[vector[a;&1], vector[&0;&0]] <=>
                x$1 = a * x$2 /\ &0 <= x$2 /\ x$2 <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
    VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN CONV_TAC REAL_RING;
    STRIP_TAC THEN EXISTS_TAC `&1 - (x:real^2)$2` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN CONV_TAC REAL_RING]);;

let MOI_FTP_ME_IN = prove
 (`!n i (x:real^2).
     3 <= n /\ i < n
     ==> (x IN moi_ftp_me n i <=>
          (i < n - 2 /\ x$2 = &0 /\ &i <= x$1 /\ x$1 <= &i + &1) \/
          (i = n - 2 /\ x$1 = &(n - 2) /\ &0 <= x$2 /\ x$2 <= &1) \/
          (i = n - 1 /\ x$1 = &(n - 2) * x$2 /\ &0 <= x$2 /\ x$2 <= &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `i:num`] MOI_FTP_ME_CASES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < n - 2 \/ i = n - 2 \/ i = n - 1` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < n`; `3 <= n`] THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `~(i = n - 2) /\ ~(i = n - 1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `i < n - 2` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FTP_SEG_BOT];
    SUBGOAL_THEN `~(i < n - 2) /\ ~(i = n - 1)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `i = n - 2` THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FTP_SEG_VERT];
    SUBGOAL_THEN `~(i < n - 2) /\ ~(i = n - 2)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `i = n - 1` THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FTP_SEG_HYP]]);;

(* Numeric consequences of real bounds. *)

let MOI_FTP_NUM_BOUNDS = prove
 (`(!i j:num x. &i <= x /\ x <= &i + &1 /\ &j <= x /\ x <= &j + &1
                ==> i <= j + 1 /\ j <= i + 1) /\
   (!i m:num x. &i <= x /\ x <= &i + &1 /\ x = &m ==> i <= m /\ m <= i + 1) /\
   (!i:num x. &i <= x /\ x = &0 ==> i = 0)`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* Non-consecutive edges of the model are disjoint. *)

let MOI_FTP_ME_DISJ = prove
 (`!n i j. 3 <= n /\ i < n /\ j < n /\ ~(i = j) /\ ~(j = moi_ftp_nx n i) /\
           ~(i = moi_ftp_nx n j)
           ==> moi_ftp_me n i INTER moi_ftp_me n j = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(SUC i < n ==> ~(j = SUC i)) /\ (SUC i = n ==> ~(j = 0)) /\
                (SUC j < n ==> ~(i = SUC j)) /\ (SUC j = n ==> ~(i = 0))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(j = moi_ftp_nx n i)`; `~(i = moi_ftp_nx n j)`] THEN
    REWRITE_TAC[moi_ftp_nx] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^2` THEN
  ASM_SIMP_TAC[MOI_FTP_ME_IN] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    (lhs(concl th) = `i:num` || lhs(concl th) = `j:num`)))) THEN
  TRY(MP_TAC(SPECL [`i:num`; `j:num`; `(x:real^2)$1`] (CONJUNCT1 MOI_FTP_NUM_BOUNDS)) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`~(i:num = j)`; `SUC i < n ==> ~(j = SUC i)`;
                             `SUC j < n ==> ~(i = SUC j)`; `i < n - 2`; `j < n - 2`] THEN
      ARITH_TAC) THEN
  TRY(MP_TAC(SPECL [`i:num`; `n - 2`; `(x:real^2)$1`]
        (CONJUNCT1(CONJUNCT2 MOI_FTP_NUM_BOUNDS))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`SUC i < n ==> ~(n - 2 = SUC i)`; `i < n - 2`; `3 <= n`] THEN
      ARITH_TAC) THEN
  TRY(MP_TAC(SPECL [`j:num`; `n - 2`; `(x:real^2)$1`]
        (CONJUNCT1(CONJUNCT2 MOI_FTP_NUM_BOUNDS))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`SUC j < n ==> ~(n - 2 = SUC j)`; `j < n - 2`; `3 <= n`] THEN
      ARITH_TAC) THEN
  TRY(MP_TAC(SPECL [`i:num`; `(x:real^2)$1`] (CONJUNCT2(CONJUNCT2 MOI_FTP_NUM_BOUNDS))) THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_TAC THEN
      MAP_EVERY UNDISCH_TAC [`SUC(n - 1) = n ==> ~(i = 0)`; `i = 0`; `3 <= n`] THEN
      ARITH_TAC) THEN
  TRY(MP_TAC(SPECL [`j:num`; `(x:real^2)$1`] (CONJUNCT2(CONJUNCT2 MOI_FTP_NUM_BOUNDS))) THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_TAC THEN
      MAP_EVERY UNDISCH_TAC [`SUC(n - 1) = n ==> ~(j = 0)`; `j = 0`; `3 <= n`] THEN
      ARITH_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_ARITH_TAC);;

let MOI_FTP_PV_NXNX = prove
 (`!n i. 4 <= n /\ i < n ==> ~(moi_ftp_pv n i = moi_ftp_nx n (moi_ftp_nx n i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_ftp_nx; moi_ftp_pv] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let MOI_FTP_ME3_TRIPLE = prove
 (`!x:real^2. ~(x IN moi_ftp_me 3 0 /\ x IN moi_ftp_me 3 1 /\ x IN moi_ftp_me 3 2)`,
  GEN_TAC THEN
  SIMP_TAC[MOI_FTP_ME_IN; LE_REFL; ARITH_RULE `0 < 3 /\ 1 < 3 /\ 2 < 3`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

(* No point lies on two consecutive edges and a third edge. *)

let MOI_FTP_ME_TRIPLE = prove
 (`!n i j. 3 <= n /\ i < n /\ j < n /\ ~(j = i) /\ ~(j = moi_ftp_nx n i)
           ==> moi_ftp_me n i INTER moi_ftp_me n (moi_ftp_nx n i) INTER moi_ftp_me n j = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `i:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i = moi_ftp_nx n j` THENL
   [SUBGOAL_THEN `j = moi_ftp_pv n i` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `moi_ftp_nx n j`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `n = 3` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^2` THEN
      MP_TAC(SPEC `x:real^2` MOI_FTP_ME3_TRIPLE) THEN
      UNDISCH_TAC `i < 3` THEN
      SPEC_TAC(`i:num`,`i:num`) THEN REWRITE_TAC[ARITH_RULE `i < 3 <=> i = 0 \/ i = 1 \/ i = 2`] THEN
      GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
      REWRITE_TAC[moi_ftp_nx; moi_ftp_pv] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC TAUT;
      MATCH_MP_TAC(SET_RULE `(b:real^2->bool) INTER c = {} ==> a INTER b INTER c = {}`) THEN
      MATCH_MP_TAC MOI_FTP_ME_DISJ THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`n:num`; `i:num`] MOI_FTP_PV_NXNX) THEN ANTS_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`3 <= n`; `~(n = 3)`; `i:num < n`] THEN ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`n:num`; `moi_ftp_pv n i`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(moi_ftp_nx n i = moi_ftp_pv n i)` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC(SET_RULE `(a:real^2->bool) INTER c = {} ==> a INTER b INTER c = {}`) THEN
    MATCH_MP_TAC MOI_FTP_ME_DISJ THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* The vertices of the model. *)

let MOI_FTP_MW_VALS = prove
 (`!n. 3 <= n
       ==> (!i. i < n - 1 ==> moi_ftp_mw n i = vector[&i;&0]) /\
           moi_ftp_mw n (n - 1) = vector[&(n - 2);&1] /\
           moi_ftp_mw n n = vector[&0;&0] /\
           moi_ftp_mw n (SUC n) = vector[&1;&0]`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. i < n - 1 ==> moi_ftp_mw n i = vector[&i;&0]` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[moi_ftp_mw] THEN
    SUBGOAL_THEN `i MOD n = i` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `i < n - 1` THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_ftp_mw] THEN
    SUBGOAL_THEN `(n - 1) MOD n = n - 1` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
      REWRITE_TAC[LT_REFL]];
    MP_TAC(SPECL [`n:num`; `0`] MOI_FTP_MW_PER) THEN REWRITE_TAC[ADD_CLAUSES] THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
    MP_TAC(SPECL [`n:num`; `1`] MOI_FTP_MW_PER) THEN REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `3 <= n` THEN ARITH_TAC]);;

let MOI_FTP_MW_NX = prove
 (`!n i. moi_ftp_mw n (moi_ftp_nx n i) = moi_ftp_mw n (SUC i) /\
         moi_ftp_mw n (SUC(moi_ftp_nx n i)) = moi_ftp_mw n (SUC(SUC i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftp_nx] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  MP_TAC(SPECL [`n:num`; `0`] MOI_FTP_MW_PER) THEN
  MP_TAC(SPECL [`n:num`; `SUC 0`] MOI_FTP_MW_PER) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN SIMP_TAC[]);;

let MOI_FTP_MW_PV = prove
 (`!n i. 1 <= n ==> moi_ftp_mw n (SUC(moi_ftp_pv n i)) = moi_ftp_mw n i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_ftp_pv] THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    SUBGOAL_THEN `SUC(n - 1) = n` SUBST1_TAC THENL
     [UNDISCH_TAC `1 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `0`] MOI_FTP_MW_PER) THEN REWRITE_TAC[ADD_CLAUSES];
    AP_TERM_TAC THEN UNDISCH_TAC `~(i = 0)` THEN ARITH_TAC]);;

(* Consecutive edges meet in their common vertex. *)

let MOI_FTP_ME_CONSEC = prove
 (`!n i. 3 <= n /\ i < n
         ==> moi_ftp_me n i INTER moi_ftp_me n (moi_ftp_nx n i) = {moi_ftp_mw n (SUC i)} /\
             ~(moi_ftp_mw n i = moi_ftp_mw n (SUC i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_ftp_me; MOI_FTP_MW_NX] THEN
  MP_TAC(SPEC `n:num` MOI_FTP_MW_VALS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lo") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?a b c:real^2. moi_ftp_mw n i = a /\ moi_ftp_mw n (SUC i) = b /\
                   moi_ftp_mw n (SUC(SUC i)) = c /\
                   (b IN segment[a,c] \/ ~collinear {a,b,c}) /\ ~(a = b)`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2` (X_CHOOSE_THEN `c:real^2`
      (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTER_SEGMENT THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `i < n - 3 \/ i = n - 3 \/ i = n - 2 \/ i = n - 1` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`i:num < n`; `3 <= n`] THEN ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THENL
   [(* two bottom edges *)
    MAP_EVERY EXISTS_TAC [`vector[&i;&0]:real^2`; `vector[&(SUC i);&0]:real^2`;
                          `vector[&(SUC(SUC i));&0]:real^2`] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "lo" MATCH_MP_TAC THEN UNDISCH_TAC `i < n - 3` THEN ARITH_TAC;
      USE_THEN "lo" MATCH_MP_TAC THEN UNDISCH_TAC `i < n - 3` THEN ARITH_TAC;
      USE_THEN "lo" MATCH_MP_TAC THEN UNDISCH_TAC `i < n - 3` THEN ARITH_TAC;
      DISJ1_TAC THEN
      SUBGOAL_THEN `vector[&(SUC i);&0]:real^2 =
                    midpoint(vector[&i;&0],vector[&(SUC(SUC i));&0])`
      SUBST1_TAC THENL
       [REWRITE_TAC[midpoint; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_ADD_COMPONENT;
                    VECTOR_MUL_COMPONENT; GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
        REWRITE_TAC[MIDPOINT_IN_SEGMENT]];
      REWRITE_TAC[MOI_FPS_VECTOR2_EQ; REAL_OF_NUM_EQ] THEN ARITH_TAC];
    (* bottom edge n - 3 and the vertical edge *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `SUC(n - 3) = n - 2 /\ SUC(SUC(n - 3)) = n - 1` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `moi_ftp_mw n (n - 3) = vector[&(n - 3);&0] /\
                  moi_ftp_mw n (n - 2) = vector[&(n - 2);&0]` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "lo" MATCH_MP_TAC THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`vector[&(n - 3);&0]:real^2`; `vector[&(n - 2);&0]:real^2`;
                          `vector[&(n - 2);&1]:real^2`] THEN
    ASM_REWRITE_TAC[COLLINEAR_3_2D; MOI_FPS_VECTOR2_EQ; VECTOR_2] THEN
    SUBGOAL_THEN `&(n - 2) = &(n - 3) + &1` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL [DISJ2_TAC THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    (* the vertical edge and the hypotenuse *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `SUC(n - 2) = n - 1 /\ SUC(SUC(n - 2)) = n` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `moi_ftp_mw n (n - 2) = vector[&(n - 2);&0]` ASSUME_TAC THENL
     [USE_THEN "lo" MATCH_MP_TAC THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`vector[&(n - 2);&0]:real^2`; `vector[&(n - 2);&1]:real^2`;
                          `vector[&0;&0]:real^2`] THEN
    ASM_REWRITE_TAC[COLLINEAR_3_2D; MOI_FPS_VECTOR2_EQ; VECTOR_2] THEN
    SUBGOAL_THEN `&1 <= &(n - 2)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    CONV_TAC REAL_ARITH;
    (* the hypotenuse and the first bottom edge *)
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `SUC(n - 1) = n` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`vector[&(n - 2);&1]:real^2`; `vector[&0;&0]:real^2`;
                          `vector[&1;&0]:real^2`] THEN
    ASM_REWRITE_TAC[COLLINEAR_3_2D; MOI_FPS_VECTOR2_EQ; VECTOR_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;

(* Membership in a horizontal segment. *)

let MOI_FTP_SEG_H = prove
 (`!a b x:real^2.
     a < b
     ==> (x IN segment[vector[a;&0], vector[b;&0]] <=> x$2 = &0 /\ a <= x$1 /\ x$1 <= b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= u * (b - a) /\ &0 <= (&1 - u) * (b - a)
                             ==> a <= (&1 - u) * a + u * b /\ (&1 - u) * a + u * b <= b`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < b - a /\ ~(b - a = &0)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `((x:real^2)$1 - a) / (b - a)` THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `~(b - a = &0)` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID]]]);;

(* The model circle: the boundary of the triangle, a PL 1-sphere, is the     *)
(* union of the n model edges.                                               *)

let moi_ftp_mc = new_definition
 `moi_ftp_mc (n:num) =
    relative_frontier(convex hull {vector[&0;&0]:real^2, vector[&(n - 2);&0],
                                   vector[&(n - 2);&1]})`;;

let MOI_FTP_MC = prove
 (`!n. 3 <= n
       ==> pl_sphere 1 (moi_ftp_mc n) /\
           moi_ftp_mc n = UNIONS {moi_ftp_me n i | i | i < n}`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= &(n - 2) /\ &0 < &(n - 2)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear {vector[&0;&0]:real^2, vector[&(n - 2);&0], vector[&(n - 2);&1]}`
  ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_3_2D; VECTOR_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[moi_ftp_mc] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[ARITH] (SPEC `1` PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX)) THEN
    REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    MAP_EVERY EXISTS_TAC [`vector[&0;&0]:real^2`; `vector[&(n - 2);&0]:real^2`;
                          `vector[&(n - 2);&1]:real^2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^2` THEN
  REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[MOI_FTP_SEG_H; MOI_FTP_SEG_VERT; MOI_FTP_SEG_HYP] THEN
  EQ_TAC THENL
   [STRIP_TAC THENL
     [MP_TAC(SPEC `(x:real^2)$1` FLOOR_POS) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
      MP_TAC(SPEC `(x:real^2)$1` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_CASES_TAC `m < n - 2` THENL
       [EXISTS_TAC `m:num` THEN
        SUBGOAL_THEN `m:num < n` ASSUME_TAC THENL [UNDISCH_TAC `m < n - 2` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[MOI_FTP_ME_IN] THEN ASM_REAL_ARITH_TAC;
        EXISTS_TAC `n - 2` THEN
        SUBGOAL_THEN `n - 2 < n /\ &(n - 2) <= &m` STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LE] THEN MAP_EVERY UNDISCH_TAC [`~(m < n - 2)`; `3 <= n`] THEN
          ARITH_TAC;
          ALL_TAC] THEN
        ASM_SIMP_TAC[MOI_FTP_ME_IN] THEN ASM_REAL_ARITH_TAC];
      EXISTS_TAC `n - 2` THEN
      SUBGOAL_THEN `n - 2 < n` ASSUME_TAC THENL [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[MOI_FTP_ME_IN] THEN ASM_REAL_ARITH_TAC;
      EXISTS_TAC `n - 1` THEN
      SUBGOAL_THEN `n - 1 < n` ASSUME_TAC THENL [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[MOI_FTP_ME_IN] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^2) IN moi_ftp_me n i` THEN ASM_SIMP_TAC[MOI_FTP_ME_IN] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN
      SUBGOAL_THEN `&i + &1 <= &(n - 2)` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN UNDISCH_TAC `i < n - 2` THEN ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `i:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* The block labels of the model: arcs and their end points. *)

let MOI_FTP_MCB_FACTS = prove
 (`!n a. 3 <= n /\ a < n + n
         ==> moi_ftp_cb n (moi_ftp_me n) a SUBSET moi_ftp_mc n /\
             polytope (moi_ftp_cb n (moi_ftp_me n) a) /\
             aff_dim (moi_ftp_cb n (moi_ftp_me n) a) = &(moi_ftp_bdim n a) /\
             relative_frontier (moi_ftp_cb n (moi_ftp_me n) a) =
             UNIONS {moi_ftp_cb n (moi_ftp_me n) a' | a' |
                     a' < n + n /\ moi_ftp_bface n a a' /\ ~(a' = a)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `n:num` MOI_FTP_MC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  ASM_CASES_TAC `a:num < n` THENL
   [(* an arc *)
    MP_TAC(SPECL [`n:num`; `a:num`] MOI_FTP_NXPV) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `a:num`] MOI_FTP_ME_CONSEC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `moi_ftp_pv n a`] MOI_FTP_ME_CONSEC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `moi_ftp_mw n (SUC(moi_ftp_pv n a)) = moi_ftp_mw n a` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_FTP_MW_PV THEN UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `!a'. a' < n + n /\ moi_ftp_bface n a a' /\ ~(a' = a) <=>
           a' = n + a \/ a' = n + moi_ftp_pv n a`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[moi_ftp_bface] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`a:num < n`; `moi_ftp_pv n a < n`] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SET_RULE `UNIONS {(f:num->real^2->bool) x | x | x = p \/ x = q} =
                          f p UNION f q`] THEN
    REWRITE_TAC[moi_ftp_cb] THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(n + a:num < n)`; ADD_SUB2; moi_ftp_bdim] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(s:real^2->bool) IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_ftp_me; POLYTOPE_SEGMENT];
      ASM_REWRITE_TAC[moi_ftp_me; AFF_DIM_SEGMENT];
      ASM_SIMP_TAC[moi_ftp_me; MOI_S4O_RF_SEGMENT] THEN SET_TAC[]];
    (* an end point *)
    ABBREV_TAC `b = a - n:num` THEN
    SUBGOAL_THEN `a = n + b:num /\ b < n` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`a - n:num = b`; `~(a:num < n)`; `a:num < n + n`] THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `moi_ftp_me n b SUBSET UNIONS {moi_ftp_me n i | i | i < n}` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(s:real^2->bool) IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `b:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!a'. a' < n + n /\ moi_ftp_bface n (n + b) a' /\ ~(a' = n + b) <=> F`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[moi_ftp_bface; ARITH_RULE `~(n + b:num < n)`] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_ftp_cb; ARITH_RULE `~(n + b:num < n)`; ADD_SUB2; moi_ftp_bdim] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_ftp_me n b SUBSET UNIONS {moi_ftp_me n i | i | i < n}` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `b:num`] MOI_FTP_ME_CONSEC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    REWRITE_TAC[POLYTOPE_SING; AFF_DIM_SING; RELATIVE_FRONTIER_SING] THEN SET_TAC[]]);;

(* The model blocks: arcs times the square, the circle times the model disk *)
(* sets of tubec.                                                            *)

let moi_ftp_mcb = new_definition
 `moi_ftp_mcb (n:num) (a:num) =
    moi_ftp_cb n (moi_ftp_me n) a PCROSS interval[--vec 1:real^2,vec 1]`;;

let moi_ftp_mzd = new_definition
 `moi_ftp_mzd (n:num) (j:num) =
    moi_ftp_mc n PCROSS
    moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq {vec 0:real^2} j`;;

let MOI_FTP_MODEL_INTER = prove
 (`!n. 3 <= n
       ==> (!a a'. a < n + n /\ a' < n + n
                   ==> moi_ftp_mcb n a INTER moi_ftp_mcb n a' =
                       UNIONS {moi_ftp_mcb n a'' | a'' | a'' < n + n /\ moi_ftp_bface n a a'' /\
                                                         moi_ftp_bface n a' a''}) /\
           (!j j'. j < 9 /\ j' < 9
                   ==> moi_ftp_mzd n j INTER moi_ftp_mzd n j' =
                       UNIONS {moi_ftp_mzd n j'' | j'' | j'' < 9 /\ moi_ftc_dface j j'' /\
                                                         moi_ftc_dface j' j''})`,
  GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_ftp_mcb; moi_ftp_mzd; INTER_PCROSS; INTER_IDEMPOT;
              MOI_FTC_PCROSS_UNIONS_GSPEC] THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`moi_ftp_me n`; `n:num`] MOI_FTP_NECKLACE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC MOI_FTP_ME_DISJ THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_FTP_ME_TRIPLE THEN ASM_REWRITE_TAC[]];
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    AP_TERM_TAC THEN
    MP_TAC MOI_FTC_DISK_MODEL THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FTP_MODEL_CELLS = prove
 (`!n a j. 3 <= n /\ a < n + n /\ j < 9
           ==> pl_cell_with_boundary (moi_ftp_bdim n a + moi_ftc_dd j)
                 (moi_ftp_mcb n a INTER moi_ftp_mzd n j)
                 ((moi_ftp_mcb n a INTER
                   UNIONS {moi_ftp_mzd n j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}) UNION
                  (UNIONS {moi_ftp_mcb n a' | a' | a' < n + n /\ moi_ftp_bface n a a' /\
                                                   ~(a' = a)} INTER
                   moi_ftp_mzd n j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `a:num`] MOI_FTP_MCB_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_FTC_DISK_MODEL THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "dcell") (LABEL_TAC "dsub"))) THEN
  REWRITE_TAC[moi_ftp_mcb; moi_ftp_mzd] THEN
  ABBREV_TAC `C = moi_ftp_mc n` THEN
  ABBREV_TAC `D = interval[--vec 1:real^2,vec 1]` THEN
  ABBREV_TAC `cb = moi_ftp_cb n (moi_ftp_me n)` THEN
  ABBREV_TAC `zd = moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq
                              {vec 0:real^2}` THEN
  SUBGOAL_THEN
   `UNIONS {(zd:num->real^2->bool) j' | j' | j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}
    SUBSET D`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_FTC_IN_UNIONS_GSPEC] THEN X_GEN_TAC `y:real^2` THEN
    DISCH_THEN(X_CHOOSE_THEN `j':num` STRIP_ASSUME_TAC) THEN
    USE_THEN "dsub" (fun th -> MP_TAC(MATCH_MP (SPEC `j':num` th) (ASSUME `j' < 9`))) THEN
    REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier ((cb:num->real^2->bool) a) SUBSET C` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(cb:num->real^2->bool) a` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[relative_frontier] THEN
      MP_TAC(ISPEC `(cb:num->real^2->bool) a` CLOSURE_CLOSED) THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED] THEN SET_TAC[];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_FTC_PCROSS_UNIONS_GSPEC] THEN
  FIRST_X_ASSUM((fun th -> REWRITE_TAC[SYM th]) o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `relative_frontier ((cb:num->real^2->bool) a)`)) THEN
  MP_TAC(ISPECL [`(cb:num->real^2->bool) a`; `C:real^2->bool`;
                 `relative_frontier ((cb:num->real^2->bool) a)`; `D:real^2->bool`;
                 `(zd:num->real^2->bool) j`;
                 `UNIONS {(zd:num->real^2->bool) j' | j' |
                          j' < 9 /\ moi_ftc_dface j j' /\ ~(j' = j)}`]
    MOI_FTC_PCROSS_CELL_SETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "dsub" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
  MATCH_MP_TAC MOI_FTC_PROD_CELL THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    USE_THEN "dcell" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MP_TAC(SPEC `n:num` MOI_FTP_BLABELS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:num`; `j:num`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FTP_MODEL_UNION = prove
 (`!n. 3 <= n
       ==> UNIONS {moi_ftp_mcb n a INTER moi_ftp_mzd n j | a,j | a < n + n /\ j < 9} =
           moi_ftp_mc n PCROSS interval[--vec 1:real^2,vec 1] /\
           UNIONS {moi_ftp_mcb n a INTER moi_ftp_mzd n 6 | a | a < n + n} =
           moi_ftp_mc n PCROSS {vec 0:real^2}`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!x:real^2. x IN moi_ftp_mc n ==> ?a. a < n /\ x IN moi_ftp_cb n (moi_ftp_me n) a`
  (LABEL_TAC "cin") THENL
   [GEN_TAC THEN MP_TAC(SPEC `n:num` MOI_FTP_MC) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `a:num` THEN
    ASM_REWRITE_TAC[moi_ftp_cb];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a. a < n + n ==> moi_ftp_cb n (moi_ftp_me n) a SUBSET moi_ftp_mc n`
  (LABEL_TAC "csub") THENL
   [REPEAT STRIP_TAC THEN MP_TAC(SPECL [`n:num`; `a:num`] MOI_FTP_MCB_FACTS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq {vec 0:real^2} 0 =
    moi_ftc_dom /\
    moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq {vec 0:real^2} 1 =
    moi_ftc_dop /\
    moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq {vec 0:real^2} 6 =
    {vec 0}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_ftc_zd] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC MOI_FTC_DISK_MODEL THEN
  DISCH_THEN(LABEL_TAC "dsub" o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[moi_ftp_mcb; moi_ftp_mzd] THEN CONJ_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIONS; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^(2,2)finite_sum->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `a:num` (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    USE_THEN "cin" (fun th -> MP_TAC(MP (SPEC `x:real^2` th) (ASSUME `(x:real^2) IN moi_ftp_mc n`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?j. j < 9 /\
                  (y:real^2) IN moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff
                                           moi_fps_sq {vec 0:real^2} j`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^2) IN interval[--vec 1,vec 1]` THEN
      REWRITE_TAC[GSYM MOI_FTC_DISK_UNION; IN_UNION] THEN STRIP_TAC THENL
       [EXISTS_TAC `0`; EXISTS_TAC `1`] THEN ASM_REWRITE_TAC[ARITH];
      ALL_TAC] THEN
    EXISTS_TAC `(moi_ftp_cb n (moi_ftp_me n) a PCROSS interval[--vec 1:real^2,vec 1]) INTER
                (moi_ftp_mc n PCROSS
                 moi_ftc_zd moi_ftc_dom moi_ftc_dop moi_ftc_dsf moi_ftc_dff moi_fps_sq
                            {vec 0:real^2} j)` THEN
    CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `a:num < n` THEN ARITH_TAC;
      ASM_REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS]];
    DISCH_THEN(X_CHOOSE_THEN `t:real^(2,2)finite_sum->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS; IN_SING] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    USE_THEN "cin" (fun th -> MP_TAC(MP (SPEC `x:real^2` th) (ASSUME `(x:real^2) IN moi_ftp_mc n`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(moi_ftp_cb n (moi_ftp_me n) a PCROSS interval[--vec 1:real^2,vec 1]) INTER
                (moi_ftp_mc n PCROSS {vec 0:real^2})` THEN
    CONJ_TAC THENL
     [EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `a:num < n` THEN ARITH_TAC;
      ASM_REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS; IN_SING] THEN
      UNDISCH_TAC `(y:real^2) IN {vec 0}` THEN REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[IN_INTERVAL; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The necklace is a solid torus.  MOI_FTC_PROD_ASSEMBLY with               *)
(* the 2n block labels and tubec's 9 disk labels glues a PL embedding of    *)
(* the union of the dual cells onto the model circle PCROSS square, with   *)
(* the polygon going to the core circle PCROSS {0}; tubec's                 *)
(* MOI_FTC_TORUS_SPINE then gives the solid torus and its spine.            *)
(* ========================================================================= *)

let MOI_FTP_NECK_ASSEMBLY = prove
 (`!(t:(real^N->bool)->bool) l V h k n (S:num->real^N) cS cF Q As AF bs b1.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. S i IN V) /\ (!i. {S i} IN l) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)) /\
     (!i. cS(i + n) = cS i) /\ (!i. cF(i + n) = cF i) /\
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1
     ==> ?f. pl_map_on (UNIONS {derived_dual_cell t l (S i) | i | i < n}) f /\
             (!x y. x IN UNIONS {derived_dual_cell t l (S i) | i | i < n} /\
                    y IN UNIONS {derived_dual_cell t l (S i) | i | i < n} /\ f x = f y
                    ==> x = y) /\
             (!a j. a < n + n /\ j < 9
                    ==> IMAGE f (moi_ftp_cb n (\i. derived_dual_cell t l (S i)) a INTER
                                 moi_ftp_za t l h k n S Q As AF j) =
                        moi_ftp_mcb n a INTER moi_ftp_mzd n j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`{a:num | a < n + n}`; `moi_ftp_bface n`; `moi_ftp_bdim n`;
                 `{j:num | j < 9}`; `moi_ftc_dface`; `moi_ftc_dd`;
                 `moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i))`;
                 `moi_ftp_za (t:(real^N->bool)->bool) l h k n S Q As AF`;
                 `moi_ftp_mcb n`; `moi_ftp_mzd n`] MOI_FTC_PROD_ASSEMBLY) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [MP_TAC(SPEC `n:num` MOI_FTP_BLABELS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC MOI_FTC_LABELS THEN STRIP_TAC THEN
    MP_TAC(SPEC `n:num` MOI_FTP_MODEL_INTER) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `n:num`;
                   `S:num->real^N`] MOI_FTP_DOM_NECK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `n:num`; `S:num->real^N`;
                   `cS:num->real^N`; `cF:num->real^N`; `Q:num->real^N->bool`;
                   `As:num->real^N->bool`; `AF:num->real^N->bool`; `bs:num->real^N`;
                   `b1:num->real^N`] MOI_FTP_DOM_ZA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                   `h:real^N->real^N`; `k:real^N->real^N`; `n:num`; `S:num->real^N`;
                   `cS:num->real^N`; `cF:num->real^N`; `Q:num->real^N->bool`;
                   `As:num->real^N->bool`; `AF:num->real^N->bool`; `bs:num->real^N`;
                   `b1:num->real^N`] MOI_FTP_DOM_CELLS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    TRY CONJ_TAC THEN ASM_SIMP_TAC[MOI_FTP_MODEL_CELLS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `n:num`; `S:num->real^N`;
                 `cS:num->real^N`; `cF:num->real^N`; `Q:num->real^N->bool`;
                 `As:num->real^N->bool`; `AF:num->real^N->bool`; `bs:num->real^N`;
                 `b1:num->real^N`] MOI_FTP_DOM_UNION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN ACCEPT_TAC);;

let MOI_FTP_NECK_TORUS = prove
 (`!(t:(real^N->bool)->bool) l V h k n (S:num->real^N) cS cF Q As AF bs b1.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. S i IN V) /\ (!i. {S i} IN l) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)) /\
     (!i. cS(i + n) = cS i) /\ (!i. cF(i + n) = cF i) /\
     moi_ftp_blocks t l h n S cS cF Q As AF bs b1
     ==> pl_solid_torus (UNIONS {derived_dual_cell t l (S i) | i | i < n}) /\
         spine (UNIONS {segment[S i,S(SUC i)] | i | i < n})
               (UNIONS {derived_dual_cell t l (S i) | i | i < n})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `n:num`; `S:num->real^N`;
                 `cS:num->real^N`; `cF:num->real^N`; `Q:num->real^N->bool`;
                 `As:num->real^N->bool`; `AF:num->real^N->bool`; `bs:num->real^N`;
                 `b1:num->real^N`] MOI_FTP_NECK_ASSEMBLY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^(2,2)finite_sum`
    (CONJUNCTS_THEN2 (LABEL_TAC "pl") (CONJUNCTS_THEN2 (LABEL_TAC "inj") (LABEL_TAC "im")))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `n:num`; `S:num->real^N`;
                 `cS:num->real^N`; `cF:num->real^N`; `Q:num->real^N->bool`;
                 `As:num->real^N->bool`; `AF:num->real^N->bool`; `bs:num->real^N`;
                 `b1:num->real^N`] MOI_FTP_DOM_UNION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "du")] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `n:num`; `S:num->real^N`;
                 `cS:num->real^N`; `cF:num->real^N`; `Q:num->real^N->bool`;
                 `As:num->real^N->bool`; `AF:num->real^N->bool`; `bs:num->real^N`;
                 `b1:num->real^N`] MOI_FTP_DOM_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "dc")] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `V:real^N->bool`;
                 `h:real^N->real^N`; `k:real^N->real^N`; `n:num`; `S:num->real^N`;
                 `cS:num->real^N`; `cF:num->real^N`; `Q:num->real^N->bool`;
                 `As:num->real^N->bool`; `AF:num->real^N->bool`; `bs:num->real^N`;
                 `b1:num->real^N`] MOI_FTP_DOM_CELLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "cells")] THEN
  MP_TAC(SPEC `n:num` MOI_FTP_MODEL_UNION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "mu") (LABEL_TAC "m6")) THEN
  ABBREV_TAC `U = UNIONS {derived_dual_cell t l ((S:num->real^N) i) | i | i < n}` THEN
  SUBGOAL_THEN `compact (U:real^N->bool)` ASSUME_TAC THENL
   [USE_THEN "du" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    REWRITE_TAC[MOI_FTC_FINITE_GSPEC2; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "cells" (MP_TAC o SPECL [`a:num`; `j:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o MATCH_MP MOI_CEL_CELL_COMPACT)] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^(2,2)finite_sum) U =
    moi_ftp_mc n PCROSS interval[--vec 1:real^2,vec 1]`
  ASSUME_TAC THENL
   [USE_THEN "du" (SUBST1_TAC o SYM) THEN
    USE_THEN "mu" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_FTC_IMAGE_UNIONS2 THEN REWRITE_TAC[] THEN USE_THEN "im" MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:real^N->bool`; `f:real^N->real^(2,2)finite_sum`] MOI_FCL_PLH_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [USE_THEN "pl" ACCEPT_TAC; USE_THEN "inj" ACCEPT_TAC];
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^(2,2)finite_sum->real^N`) THEN
  MP_TAC(ISPECL [`moi_ftp_mc n`; `U:real^N->bool`; `g:real^(2,2)finite_sum->real^N`;
                 `f:real^N->real^(2,2)finite_sum`] MOI_FTC_TORUS_SPINE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `n:num` MOI_FTP_MC) THEN ASM_SIMP_TAC[];
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (g:real^(2,2)finite_sum->real^N) (moi_ftp_mc n PCROSS {vec 0:real^2}) =
    UNIONS {segment[(S:num->real^N) i,S(SUC i)] | i | i < n}`
  (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "dc" (SUBST1_TAC o SYM) THEN USE_THEN "m6" (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `UNIONS {moi_ftp_mcb n a INTER moi_ftp_mzd n 6 | a | a < n + n} =
    IMAGE (f:real^N->real^(2,2)finite_sum)
      (UNIONS {moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i)) a INTER
               moi_ftp_za t l h k n S Q As AF 6 | a | a < n + n})`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FTC_IMAGE_UNIONS1 THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN USE_THEN "im" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {moi_ftp_cb n (\i. derived_dual_cell t l ((S:num->real^N) i)) a INTER
            moi_ftp_za t l h k n S Q As AF 6 | a | a < n + n} SUBSET U`
  MP_TAC THENL
   [USE_THEN "du" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`a:num`; `6`] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_comb(concl th) &&
    fst(strip_comb(concl th)) = `pl_homeomorphism:(real^N->bool)#(real^(2,2)finite_sum->bool)->
      (real^N->real^(2,2)finite_sum)#(real^(2,2)finite_sum->real^N)->bool`)) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; SUBSET] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* Cycles and kites.  A locally finite complex whose union is               *)
(* a PL 1-sphere is a cycle of n >= 3 vertices (pl1m's MOI_S4L_CM1_CYCLE    *)
(* through line charts and degree 2).  At an edge [v,w] of the graph the    *)
(* link of w in the link of v is such a complex, so it has an edge [y,x]    *)
(* with y different from any one given point; the tetrahedron conv{v,w,y,x} *)
(* then carries the kite of the edge (MOI_FTP_EDGE_KITE).                   *)
(* ========================================================================= *)

let MOI_FTP_SPHERE1_CYCLE = prove
 (`!K:(real^N->bool)->bool.
     lf_simplicial_complex K /\ pl_sphere 1 (UNIONS K)
     ==> FINITE K /\ (!s. s IN K ==> aff_dim s <= &1) /\
         (!v. {v} IN K ==> CARD {e | e IN K /\ aff_dim e = &1 /\ v IN e} = 2) /\
         ?n S. 3 <= n /\ (!i. S(i + n) = S i) /\
               (!i k. i < n /\ k < n /\ S i = S k ==> i = k) /\
               (!i. {S i} IN K /\ segment[S i,S(SUC i)] IN K) /\
               UNIONS K = UNIONS {segment[S i,S(SUC i)] | i | i < n} /\
               (!v. {v} IN K ==> ?i. i < n /\ v = S i)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S4O_CIRCLE_LOOP) THEN
  DISCH_THEN(X_CHOOSE_THEN `gam:real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact (UNIONS K:real^N->bool) /\ connected (UNIONS K) /\ ~(UNIONS K = {})`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `path_image(gam:real^1->real^N)`)) THEN
    REWRITE_TAC[PATH_IMAGE_NONEMPTY] THEN
    ASM_MESON_TAC[SIMPLE_PATH_IMP_PATH; COMPACT_PATH_IMAGE; CONNECTED_PATH_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN1_LF_COMPACT_FINITE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lf_simplicial_complex (K:(real^N->bool)->bool)` THEN
    SIMP_TAC[lf_simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4l_line_charts (UNIONS K:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TA_SPHERE1_LINE_CHARTS THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K ==> aff_dim s <= &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4L_LC_DIM_LE1 THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. {v} IN K ==> CARD {e | e IN K /\ aff_dim e = &1 /\ v IN e} = 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4L_LC_DEGREE_2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `UNIONS K:real^N->bool`] MOI_S4L_CM1_CYCLE) THEN
  ASM_REWRITE_TAC[IN_COMPONENTS_SELF] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `S:num->real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `S:num->real^N`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING]);;

(* Consecutive vertices of a cycle are distinct. *)

let MOI_FTP_CYC_NEXT = prove
 (`!(S:num->A) n i.
     3 <= n /\ (!i. S(i + n) = S i) /\ (!i k. i < n /\ k < n /\ S i = S k ==> i = k) /\
     i < n
     ==> ~(S i = S(SUC i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `SUC i < n` THENL
   [DISCH_TAC THEN SUBGOAL_THEN `i = SUC i` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC];
    SUBGOAL_THEN `(S:num->A)(SUC i) = S 0` SUBST1_TAC THENL
     [SUBGOAL_THEN `SUC i = 0 + n` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~(SUC i < n)`; `i:num < n`] THEN ARITH_TAC;
        FIRST_ASSUM MATCH_ACCEPT_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN SUBGOAL_THEN `i = 0` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `3 <= n` THEN ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`~(SUC i < n)`; `3 <= n`] THEN ARITH_TAC]]);;

(* An edge of the link of w in the link of v gives a tetrahedron of t. *)

let MOI_FTP_LINK2_BLK = prove
 (`!(t:(real^N->bool)->bool) v w y x.
     lf_simplicial_complex t /\ {v} IN t /\ {w} IN t /\ ~(y = x) /\
     segment[y,x] IN simplicial_link (simplicial_link t v) w
     ==> moi_ftc_blk t v w y x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r1:real^N->bool` MP_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r2:real^N->bool` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `segment[y:real^N,x] SUBSET r1 /\ r1 SUBSET r2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?W2. ~affine_dependent W2 /\ r2 = convex hull (W2:real^N->bool)`
  (X_CHOOSE_THEN `W2:real^N->bool` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `?n. n simplex (r2:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
     [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
    ASM_MESON_TAC[simplex];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `{y:real^N} IN t /\ {x:real^N} IN t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    EXISTS_TAC `segment[y:real^N,x]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N. p IN convex hull W2 /\ {p} IN t ==> p IN W2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `convex hull W2:real^N->bool`; `p:real^N`]
      MOI_FTC_VERTEX_OF) THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:real^N`; `x:real^N`] ENDS_IN_SEGMENT) THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N,w,y,x} SUBSET W2` ASSUME_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {v:real^N,w,y,x}` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `W2:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_ftc_blk] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    EXISTS_TAC `convex hull W2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTC_HULL_FACE THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* The kite tetrahedron of an edge of the graph, avoiding one given third  *)
(* vertex.                                                                  *)

let MOI_FTP_EDGE_KITE = prove
 (`!(t:(real^N->bool)->bool) l v w p.
     graph_in_complex t l /\ {v} IN l /\ ~(v = w) /\ segment[v,w] IN l
     ==> ?y x. moi_ftc_blk t v w y x /\ ~(y = p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN t /\ segment[v:real^N,w] IN t` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} IN t` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    EXISTS_TAC `segment[v:real^N,w]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} IN simplicial_link t v` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[IN_SING] THEN
    EXISTS_TAC `segment[v:real^N,w]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `w:real^N`] MOI_FTA_S2LINK) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `simplicial_link (simplicial_link t v) (w:real^N)` MOI_FTP_SPHERE1_CYCLE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FTA_LINK_LF]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC)
      (X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `C:num->real^N` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `?k. k < m /\ ~((C:num->real^N) k = p)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~((C:num->real^N) 0 = C (SUC 0))` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`C:num->real^N`; `m:num`; `0`] MOI_FTP_CYC_NEXT) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `3 <= m` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `(C:num->real^N) 0 = p` THENL
     [EXISTS_TAC `SUC 0` THEN CONJ_TAC THENL
       [UNDISCH_TAC `3 <= m` THEN ARITH_TAC; ASM_MESON_TAC[]];
      EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `3 <= m` THEN ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(C:num->real^N) k`; `(C:num->real^N) (SUC k)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FTP_LINK2_BLK THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FTP_CYC_NEXT THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The kite of an edge.  For the tetrahedron conv{v,w,y,x} of               *)
(* t the kite corners m = midpoint(v,w), A = bary conv{v,w,y} and           *)
(* B = bary conv{v,w,y,x} give a nonzero apex determinant at w             *)
(* (MOI_FTP_KITE_DET), so one order (cS,cF) of {A,B} has a positive one     *)
(* (MOI_FTP_KITE_LAB); at the other end v the sign flips (MOI_FTP_DET_MID). *)
(* Two kites at a vertex whose triangles differ meet at most in the         *)
(* barycentre of a common tetrahedron (MOI_FTP_KITE_PAIR).                  *)
(* ========================================================================= *)

let MOI_FTP_DET_MID = prove
 (`!v w a b:real^3.
     det(vector[a - v; b - v; midpoint(v,w) - v]) =
     --det(vector[a - w; b - w; midpoint(v,w) - w])`,
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT; midpoint; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN CONV_TAC REAL_RING);;

let MOI_FTP_KITE_DET = prove
 (`!(t:(real^3->bool)->bool) v w y x.
     moi_ftc_blk t v w y x
     ==> ~(det(vector[simplex_barycentre(convex hull {v,w,y}) - w;
                     simplex_barycentre(convex hull {v,w,y,x}) - w;
                     midpoint(v,w) - w]) = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_blk] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent {v:real^3,w,y}` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `{v:real^3,w,y,x}` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FTC_BARY3; MOI_FTC_BARY4] THEN
  MP_TAC(ISPECL [`w:real^3`; `v:real^3`; `y:real^3`; `x:real^3`] MOI_FM3_DET_NZ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    SUBGOAL_THEN `{w:real^3,v,y,x} = {v,w,y,x}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b * inv(&24) ==> ~(b = &0) ==> ~(a = &0)`) THEN
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT; midpoint; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN CONV_TAC REAL_RING);;

let MOI_FTP_KITE_LAB = prove
 (`!(t:(real^3->bool)->bool) v w y x.
     moi_ftc_blk t v w y x
     ==> ?cS cF. ((cS = simplex_barycentre(convex hull {v,w,y}) /\
                   cF = simplex_barycentre(convex hull {v,w,y,x})) \/
                  (cS = simplex_barycentre(convex hull {v,w,y,x}) /\
                   cF = simplex_barycentre(convex hull {v,w,y}))) /\
                 &0 < det(vector[cS - w; cF - w; midpoint(v,w) - w])`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_FTP_KITE_DET) THEN
  ABBREV_TAC `A = simplex_barycentre(convex hull {v:real^3,w,y})` THEN
  ABBREV_TAC `B = simplex_barycentre(convex hull {v:real^3,w,y,x})` THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `&0 < det(vector[A - w; B - w; midpoint(v,w) - w:real^3])` THENL
   [MAP_EVERY EXISTS_TAC [`A:real^3`; `B:real^3`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`B:real^3`; `A:real^3`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`w:real^3`; `A:real^3`; `B:real^3`; `midpoint(v:real^3,w)`]
      MOI_FTP_DET_SWAP12) THEN
    ASM_REAL_ARITH_TAC]);;

(* Two triangles of a complex sharing at most one given vertex do not meet *)
(* in an edge.                                                              *)

let MOI_FTP_KITES_NONADJ = prove
 (`!(c:(real^N->bool)->bool) a1 b1 d1 a2 b2 d2.
     lf_simplicial_complex c /\
     convex hull {a1,b1,d1} IN c /\ ~affine_dependent {a1,b1,d1} /\
     convex hull {a2,b2,d2} IN c /\ ~affine_dependent {a2,b2,d2} /\
     {a1,b1,d1} INTER {a2,b2,d2} SUBSET {d1}
     ==> ~(aff_dim(convex hull {a1,b1,d1} INTER convex hull {a2,b2,d2}) = &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K1 = convex hull {a1:real^N,b1,d1}` THEN
  ABBREV_TAC `K2 = convex hull {a2:real^N,b2,d2}` THEN
  SUBGOAL_THEN `(K1 INTER K2:real^N->bool) face_of K1 /\ (K1 INTER K2) face_of K2`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o el 2 o CONJUNCTS o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{a1:real^N,b1,d1}`; `K1 INTER K2:real^N->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  MP_TAC(ISPECL [`{a2:real^N,b2,d2}`; `K1 INTER K2:real^N->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~affine_dependent (c1:real^N->bool) /\ ~affine_dependent (c2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THENL
     [EXISTS_TAC `{a1:real^N,b1,d1}`; EXISTS_TAC `{a2:real^N,b2,d2}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (c1:real^N->bool) = convex hull c2` ASSUME_TAC THENL
   [UNDISCH_TAC `K1 INTER K2 = convex hull (c1:real^N->bool)` THEN
    UNDISCH_TAC `K1 INTER K2 = convex hull (c2:real^N->bool)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c1:real^N->bool) = c2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
    MP_TAC(ISPECL [`c1:real^N->bool`; `z:real^N`]
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    MP_TAC(ISPECL [`c2:real^N->bool`; `z:real^N`]
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(c1:real^N->bool) = c2`)) THEN
  SUBGOAL_THEN `(c2:real^N->bool) SUBSET {d1}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{a1:real^N,b1,d1} INTER {a2,b2,d2}` THEN ASM_REWRITE_TAC[SUBSET_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `K1 INTER K2:real^N->bool = {} \/ K1 INTER K2 = {d1}` MP_TAC THENL
   [UNDISCH_TAC `(c2:real^N->bool) SUBSET {d1}` THEN
    UNDISCH_TAC `K1 INTER K2 = convex hull (c2:real^N->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SET_RULE `(s:real^N->bool) SUBSET {a} <=> s = {} \/ s = {a}`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; CONVEX_HULL_SING];
    STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_SING] THEN
    CONV_TAC INT_REDUCE_CONV]);;

(* The simplices of a kite tetrahedron. *)

let MOI_FTP_BLK_SIMPS = prove
 (`!(t:(real^N->bool)->bool) v u y x.
     moi_ftc_blk t v u y x
     ==> lf_simplicial_complex t /\
         segment[v,u] IN t /\ convex hull {v,u,y} IN t /\ convex hull {v,u,y,x} IN t /\
         aff_dim(segment[v,u]) = &1 /\ aff_dim(convex hull {v,u,y}) = &2 /\
         aff_dim(convex hull {v,u,y,x}) = &3 /\
         {v} IN t /\ {u} IN t /\ {y} IN t /\ {x} IN t /\
         ~affine_dependent {v,u,y} /\ ~(segment[v,u] = {}) /\
         ~(convex hull {v,u,y} = {}) /\ ~(convex hull {v,u,y,x} = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ftc_blk] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!W. W SUBSET {v:real^N,u,y,x} ==> convex hull W IN t` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    EXISTS_TAC `convex hull {v:real^N,u,y,x}` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTC_HULL_FACE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N. p IN {v,u,y,x} ==> {p} IN t` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o el 1 o CONJUNCTS o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    EXISTS_TAC `convex hull {v:real^N,u,y,x}` THEN
    ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {v:real^N,u,y} /\ ~affine_dependent {v:real^N,u}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{v:real^N,u,y,x}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN FIRST_ASSUM MATCH_MP_TAC THEN SET_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN SET_TAC[];
    REWRITE_TAC[SEGMENT_CONVEX_HULL; AFF_DIM_CONVEX_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    FIRST_ASSUM MATCH_MP_TAC THEN SET_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN SET_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN SET_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN SET_TAC[];
    REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
    REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
    REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]]);;

let MOI_FTP_BARY_DIM_NE = prove
 (`!(c:(real^N->bool)->bool) s s'.
     moi_bar_complex c /\ s IN c /\ s' IN c /\ ~(s = {}) /\ ~(s' = {}) /\
     ~(aff_dim s = aff_dim s')
     ==> ~(simplex_barycentre s = simplex_barycentre s')`,
  MESON_TAC[MOI_FTA_BARY_INJ]);;

(* Two kites at a vertex v, on the edges [v,u] and [v,u'] (u <> u'), whose  *)
(* triangles differ (the third vertex y1 of the first is not u') do not     *)
(* meet in an edge.                                                          *)

let MOI_FTP_KITE_PAIR = prove
 (`!(t:(real^N->bool)->bool) v u u' y1 x1 y2 x2 cS1 cF1 cS2 cF2.
     moi_ftc_blk t v u y1 x1 /\ moi_ftc_blk t v u' y2 x2 /\ ~(u = u') /\ ~(y1 = u') /\
     ((cS1 = simplex_barycentre(convex hull {v,u,y1}) /\
       cF1 = simplex_barycentre(convex hull {v,u,y1,x1})) \/
      (cS1 = simplex_barycentre(convex hull {v,u,y1,x1}) /\
       cF1 = simplex_barycentre(convex hull {v,u,y1}))) /\
     ((cS2 = simplex_barycentre(convex hull {v,u',y2}) /\
       cF2 = simplex_barycentre(convex hull {v,u',y2,x2})) \/
      (cS2 = simplex_barycentre(convex hull {v,u',y2,x2}) /\
       cF2 = simplex_barycentre(convex hull {v,u',y2})))
     ==> ~(aff_dim(convex hull {midpoint(v,u),cS1,cF1} INTER
                   convex hull {midpoint(v,u'),cS2,cF2}) = &1)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "lab1") (LABEL_TAC "lab2")))))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`; `y1:real^N`; `x1:real^N`]
    MOI_FTP_BLK_SIMPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `u':real^N`; `y2:real^N`; `x2:real^N`]
    MOI_FTP_BLK_SIMPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `u:real^N`; `y1:real^N`; `x1:real^N`;
                 `midpoint(v:real^N,u)`; `midpoint(v:real^N,y1)`;
                 `simplex_barycentre(convex hull {v:real^N,u,y1})`;
                 `simplex_barycentre(convex hull {v:real^N,u,y1,x1})`] MOI_FTC_BLK_SD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `v:real^N`; `u':real^N`; `y2:real^N`; `x2:real^N`;
                 `midpoint(v:real^N,u')`; `midpoint(v:real^N,y2)`;
                 `simplex_barycentre(convex hull {v:real^N,u',y2})`;
                 `simplex_barycentre(convex hull {v:real^N,u',y2,x2})`] MOI_FTC_BLK_SD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `A1 = simplex_barycentre(convex hull {v:real^N,u,y1})` THEN
  ABBREV_TAC `B1 = simplex_barycentre(convex hull {v:real^N,u,y1,x1})` THEN
  ABBREV_TAC `A2 = simplex_barycentre(convex hull {v:real^N,u',y2})` THEN
  ABBREV_TAC `B2 = simplex_barycentre(convex hull {v:real^N,u',y2,x2})` THEN
  SUBGOAL_THEN `{midpoint(v,u),cS1,cF1} = {midpoint(v:real^N,u),A1,B1} /\
                {midpoint(v,u'),cS2,cF2} = {midpoint(v:real^N,u'),A2,B2}`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [USE_THEN "lab1" (DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN REWRITE_TAC[INSERT_AC];
      USE_THEN "lab2" (DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN REWRITE_TAC[INSERT_AC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_LF_BAR THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  (* the eight distinct pairs of kite corners *)
  SUBGOAL_THEN `~(midpoint(v:real^N,u) = midpoint(v,u'))` ASSUME_TAC THENL
   [REWRITE_TAC[midpoint; VECTOR_ARITH
      `inv(&2) % (v + u:real^N) = inv(&2) % (v + u') <=> u = u'`] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(midpoint(v:real^N,u) = A2) /\ ~(midpoint(v:real^N,u) = B2) /\
    ~(A1 = midpoint(v:real^N,u')) /\ ~(A1:real^N = B2) /\
    ~(B1 = midpoint(v:real^N,u')) /\ ~(B1:real^N = A2)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A1"; "B1"; "A2"; "B2"] THEN
    REWRITE_TAC[GSYM MOI_FTA_BARY_SEGMENT] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_FTP_BARY_DIM_NE THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(A1:real^N = A2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `convex hull {v:real^N,u,y1} = convex hull {v,u',y2}` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_BARY_INJ THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u':real^N) extreme_point_of convex hull {v,u,y1}` MP_TAC THENL
     [MATCH_MP_TAC MOI_FTC_VERTEX_OF THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `moi_ftc_blk t (v:real^N) u' y2 x2` THEN REWRITE_TAC[moi_ftc_blk] THEN
      MAP_EVERY UNDISCH_TAC [`~(u:real^N = u')`; `~(y1:real^N = u')`] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FTP_KITES_NONADJ THEN
  EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `t:(real^N->bool)->bool` MOI_FTA_BS_FACTS) THEN ASM_SIMP_TAC[];
    UNDISCH_TAC `convex hull {midpoint(v:real^N,u),A1,B1} IN
                 simplicial_link (barycentric_subdivision t) v` THEN
    SIMP_TAC[simplicial_link; IN_ELIM_THM];
    MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{v:real^N,midpoint(v,u),A1,B1}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `convex hull {midpoint(v:real^N,u'),A2,B2} IN
                 simplicial_link (barycentric_subdivision t) v` THEN
    SIMP_TAC[simplicial_link; IN_ELIM_THM];
    MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `{v:real^N,midpoint(v,u'),A2,B2}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* The polygon. The vertex cycle of l (MOI_FTP_SPHERE1_CYCLE) with its       *)
(* degree-2 description, a kite at every edge (avoiding the far end of the   *)
(* next edge) labelled by the rule at the end vertex, the blocks at every    *)
(* vertex (MOI_FTP_VBLK), and the main theorem POLYGON_NBHD_SOLID_TORUS.     *)
(* ========================================================================= *)

let MOI_FTP_POLY_DIST = prove
 (`!(S:num->A) n.
     3 <= n /\ (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j)
     ==> !i. ~(S(SUC i) = S i) /\ ~(S(i + n - 1) = S i) /\ ~(S(i + n - 1) = S(SUC i))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  SUBGOAL_THEN `0 < n` ASSUME_TAC THENL [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = i MOD n` THEN
  SUBGOAL_THEN `r:num < n` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `0 < n` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:num->A) i = S r /\ S(SUC i) = S(SUC r) /\ S(i + n - 1) = S(r + n - 1)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:num->A`; `n:num`] MOI_FTP_PER_MOD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[ADD1] THEN MATCH_MP_TAC MOI_FTP_PER_SHIFT THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "r" THEN REWRITE_TAC[MOD_MOD_REFL];
      MATCH_MP_TAC MOI_FTP_PER_SHIFT THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "r" THEN REWRITE_TAC[MOD_MOD_REFL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:num->A`; `n:num`; `r:num`] MOI_FTP_NXPV_PER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM))] THEN
  MP_TAC(SPECL [`n:num`; `r:num`] MOI_FTP_NXPV) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_MESON_TAC[]);;

(* The two edges of l at a polygon vertex. *)

let MOI_FTP_POLY_DEG = prove
 (`!(l:(real^N->bool)->bool) n S.
     FINITE l /\ 3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. {S i} IN l /\ segment[S i,S(SUC i)] IN l) /\
     (!v. {v} IN l ==> CARD {e | e IN l /\ aff_dim e = &1 /\ v IN e} = 2)
     ==> !i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:num->real^N`; `n:num`] MOI_FTP_POLY_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `w:real^N`] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `(S:num->real^N)(i + n - 1)`)) (concl th))) THEN
  SUBGOAL_THEN `segment[(S:num->real^N)(i + n - 1),S i] IN l /\ {(S:num->real^N) i} IN l /\
                segment[(S:num->real^N) i,S(SUC i)] IN l`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(S:num->real^N) i = S(SUC(i + n - 1))` SUBST1_TAC THENL
     [SUBGOAL_THEN `SUC(i + n - 1) = i + n` SUBST1_TAC THENL
       [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(S:num->real^N) i` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `CARD:((real^N->bool)->bool)->num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `E = {e | e IN l /\ aff_dim e = &1 /\ (S:num->real^N) i IN e}` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `FINITE (E:(real^N->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `~(segment[(S:num->real^N)(i + n - 1),S i] = segment[S i,S(SUC i)]) /\
      ~(segment[(S:num->real^N)(i + n - 1),S i] = segment[S i,w]) /\
      ~(segment[(S:num->real^N) i,S(SUC i)] = segment[S i,w])`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SEGMENT_EQ] THEN REPEAT CONJ_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
        `{a:real^N,b} = {c,d} ==> (a = c \/ a = d) /\ (b = c \/ b = d)`)) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{segment[(S:num->real^N)(i + n - 1),S i], segment[S i,S(SUC i)], segment[S i,w]}
      SUBSET E`
    ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`{segment[(S:num->real^N)(i + n - 1),S i], segment[S i,S(SUC i)], segment[S i,w]}`;
      `E:(real^N->bool)->bool`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]]);;

(* Periodic kite data along the polygon. *)

let MOI_FTP_POLY_KITES = prove
 (`!(t:(real^3->bool)->bool) l n S.
     graph_in_complex t l /\ 3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. {S i} IN l /\ segment[S i,S(SUC i)] IN l)
     ==> ?y x cS cF.
           (!i. cS(i + n) = cS i) /\ (!i. cF(i + n) = cF i) /\
           (!i. moi_ftc_blk t (S i) (S(SUC i)) (y i) (x i) /\ ~(y i = S(SUC(SUC i))) /\
                ((cS i = simplex_barycentre(convex hull {S i,S(SUC i),y i}) /\
                  cF i = simplex_barycentre(convex hull {S i,S(SUC i),y i,x i})) \/
                 (cS i = simplex_barycentre(convex hull {S i,S(SUC i),y i,x i}) /\
                  cF i = simplex_barycentre(convex hull {S i,S(SUC i),y i}))) /\
                &0 < det(vector[cS i - S(SUC i); cF i - S(SUC i);
                                midpoint(S i,S(SUC i)) - S(SUC i)]))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:num->real^3`; `n:num`] MOI_FTP_POLY_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!i. ?yy xx cc ff.
      moi_ftc_blk t ((S:num->real^3) i) (S(SUC i)) yy xx /\ ~(yy = S(SUC(SUC i))) /\
      ((cc = simplex_barycentre(convex hull {S i,S(SUC i),yy}) /\
        ff = simplex_barycentre(convex hull {S i,S(SUC i),yy,xx})) \/
       (cc = simplex_barycentre(convex hull {S i,S(SUC i),yy,xx}) /\
        ff = simplex_barycentre(convex hull {S i,S(SUC i),yy}))) /\
      &0 < det(vector[cc - S(SUC i); ff - S(SUC i); midpoint(S i,S(SUC i)) - S(SUC i)])`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `(S:num->real^3) i`;
                   `(S:num->real^3) (SUC i)`; `(S:num->real^3) (SUC(SUC i))`]
      MOI_FTP_EDGE_KITE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `(S:num->real^3)(i + n - 1)`)) (concl th))) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `yy:real^3` (X_CHOOSE_THEN `xx:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `(S:num->real^3) i`; `(S:num->real^3) (SUC i)`;
                   `yy:real^3`; `xx:real^3`] MOI_FTP_KITE_LAB) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `cc:real^3` (X_CHOOSE_THEN `ff:real^3` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`yy:real^3`; `xx:real^3`; `cc:real^3`; `ff:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `Y:num->real^3` (X_CHOOSE_THEN `X:num->real^3`
    (X_CHOOSE_THEN `CS:num->real^3` (X_CHOOSE_THEN `CF:num->real^3` (LABEL_TAC "K"))))) THEN
  MAP_EVERY EXISTS_TAC [`\i. (Y:num->real^3)(i MOD n)`; `\i. (X:num->real^3)(i MOD n)`;
                        `\i. (CS:num->real^3)(i MOD n)`; `\i. (CF:num->real^3)(i MOD n)`] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!i. (i + n) MOD n = i MOD n` (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(SPECL [`1`; `n:num`; `i:num`] (CONJUNCT1(CONJUNCT2(CONJUNCT2 MOD_MULT_ADD)))) THEN
    REWRITE_TAC[MULT_CLAUSES];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN
  SUBGOAL_THEN `0 < n` ASSUME_TAC THENL [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(S:num->real^3) (i MOD n) = S i /\ S(SUC(i MOD n)) = S(SUC i) /\
                S(SUC(SUC(i MOD n))) = S(SUC(SUC i))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:num->real^3`; `n:num`] MOI_FTP_PER_MOD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      REWRITE_TAC[ADD1] THEN MATCH_MP_TAC MOI_FTP_PER_SHIFT THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[MOD_MOD_REFL];
      REWRITE_TAC[ARITH_RULE `SUC(SUC x) = x + 2`] THEN MATCH_MP_TAC MOI_FTP_PER_SHIFT THEN
      EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[MOD_MOD_REFL]];
    ALL_TAC] THEN
  USE_THEN "K" (MP_TAC o SPEC `i MOD n`) THEN
  REWRITE_TAC[ASSUME `(S:num->real^3) (i MOD n) = S i`;
              ASSUME `(S:num->real^3) (SUC(i MOD n)) = S(SUC i)`;
              ASSUME `(S:num->real^3) (SUC(SUC(i MOD n))) = S(SUC(SUC i))`]);;

(* The blocks at all polygon vertices. *)

let MOI_FTP_POLY_BLOCKS = prove
 (`!(t:(real^3->bool)->bool) l V h k n S (cS:num->real^3) cF y x.
     graph_in_complex t l /\ moi_ftc_lev t l V h k /\ 3 <= n /\
     (!i. S(i + n) = S i) /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. S i IN V) /\
     (!i w. ~(w = S i) /\ segment[S i,w] IN l <=> w = S(i + n - 1) \/ w = S(SUC i)) /\
     (!i. moi_ftc_blk t (S i) (S(SUC i)) (y i) (x i) /\ ~(y i = S(SUC(SUC i))) /\
          ((cS i = simplex_barycentre(convex hull {S i,S(SUC i),y i}) /\
            cF i = simplex_barycentre(convex hull {S i,S(SUC i),y i,x i})) \/
           (cS i = simplex_barycentre(convex hull {S i,S(SUC i),y i,x i}) /\
            cF i = simplex_barycentre(convex hull {S i,S(SUC i),y i}))) /\
          &0 < det(vector[cS i - S(SUC i); cF i - S(SUC i);
                          midpoint(S i,S(SUC i)) - S(SUC i)]))
     ==> ?Q As AF bs b1. moi_ftp_blocks t l h n S cS cF Q As AF bs b1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> let c = CONJUNCTS th in
    MAP_EVERY ASSUME_TAC (butlast c) THEN LABEL_TAC "K" (last c)) THEN
  MP_TAC(ISPECL [`S:num->real^3`; `n:num`] MOI_FTP_POLY_DIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "dist")] THEN
  SUBGOAL_THEN
   `!i. ?Q As AF bs b1. i < n ==>
      moi_ftp_abl ((S:num->real^3) i) (UNIONS (simplicial_link (barycentric_subdivision t) (S i)))
          (IMAGE h (derived_dual_cell t l (S i) INTER derived_frontier t l) UNION
           (IMAGE h (derived_dual_cell t l (S i)) INTER
            UNIONS (simplicial_link (barycentric_subdivision t) (S i))))
          (IMAGE h (derived_dual_cell t l (S i)))
          (IMAGE h (derived_dual_cell t l (S i) INTER derived_frontier t l))
          (midpoint(S i,S(i + n - 1))) (midpoint(S i,S(SUC i)))
          (midpoint(midpoint(S i,S(i + n - 1)),cS(i + n - 1)))
          (midpoint(midpoint(S i,S(i + n - 1)),cF(i + n - 1)))
          (midpoint(midpoint(S i,S(SUC i)),cS i)) (midpoint(midpoint(S i,S(SUC i)),cF i))
          bs b1 Q As AF
          (IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(i + n - 1))))
          (IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(SUC i))))
          (IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(i + n - 1)) INTER
                    derived_frontier t l))
          (IMAGE h (derived_dual_cell t l (S i) INTER derived_dual_cell t l (S(SUC i)) INTER
                    derived_frontier t l))
          {}`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SKOLEM_THM; moi_ftp_blocks] THEN DISCH_THEN ACCEPT_TAC] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(S:num->real^3)(SUC(i + n - 1)) = S i /\ S(SUC(SUC(i + n - 1))) = S(SUC i)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `SUC(i + n - 1) = i + n /\ SUC(SUC(i + n - 1)) = SUC i + n`
    (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "K" (MP_TAC o SPEC `i + n - 1`) THEN
  USE_THEN "K" (MP_TAC o SPEC `i:num`) THEN
  REWRITE_TAC[ASSUME `(S:num->real^3)(SUC(i + n - 1)) = S i`;
              ASSUME `(S:num->real^3)(SUC(SUC(i + n - 1))) = S(SUC i)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  USE_THEN "dist" (STRIP_ASSUME_TAC o SPEC `i:num`) THEN
  SUBGOAL_THEN `segment[(S:num->real^3) i,S(i + n - 1)] IN l /\
                segment[(S:num->real^3) i,S(SUC i)] IN l`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> MP_TAC(SPECL [`i:num`; `(S:num->real^3)(i + n - 1)`] th) THEN
      MP_TAC(SPECL [`i:num`; `(S:num->real^3)(SUC i)`] th)) o check (fun th ->
      let _,b = strip_forall(concl th) in is_iff b)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_ftc_blk t ((S:num->real^3) i) (S(i + n - 1)) ((y:num->real^3)(i + n - 1))
                ((x:num->real^3)(i + n - 1))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FTC_BLK_PERM o check (fun th ->
      concl th = `moi_ftc_blk t ((S:num->real^3)(i + n - 1)) (S i)
                    ((y:num->real^3)(i + n - 1)) ((x:num->real^3)(i + n - 1))`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((cS:num->real^3)(i + n - 1) =
       simplex_barycentre(convex hull {(S:num->real^3) i,S(i + n - 1),(y:num->real^3)(i + n - 1)}) /\
     (cF:num->real^3)(i + n - 1) =
       simplex_barycentre(convex hull {S i,S(i + n - 1),y(i + n - 1),(x:num->real^3)(i + n - 1)})) \/
    (cS(i + n - 1) =
       simplex_barycentre(convex hull {S i,S(i + n - 1),y(i + n - 1),x(i + n - 1)}) /\
     cF(i + n - 1) = simplex_barycentre(convex hull {S i,S(i + n - 1),y(i + n - 1)}))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `(cS:num->real^3)(i + n - 1)`)) (concl th))) THEN
    REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < det(vector[(cS:num->real^3)(i + n - 1) - S i; (cF:num->real^3)(i + n - 1) - S i;
                    midpoint((S:num->real^3) i,S(i + n - 1)) - S i])`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[MIDPOINT_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `det(vector[(cS:num->real^3) i - S i; (cF:num->real^3) i - S i;
               midpoint((S:num->real^3) i,S(SUC i)) - S i]) < &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(S:num->real^3) i`; `(S:num->real^3)(SUC i)`; `(cS:num->real^3) i`;
                   `(cF:num->real^3) i`] MOI_FTP_DET_MID) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th =
      `&0 < det(vector[(cS:num->real^3) i - S(SUC i); (cF:num->real^3) i - S(SUC i);
                       midpoint((S:num->real^3) i,S(SUC i)) - S(SUC i)])`)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(aff_dim(convex hull {midpoint((S:num->real^3) i,S(i + n - 1)),(cS:num->real^3)(i + n - 1),
                           (cF:num->real^3)(i + n - 1)} INTER
              convex hull {midpoint(S i,S(SUC i)),cS i,cF i}) = &1)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `(S:num->real^3) i`;
                   `(S:num->real^3)(i + n - 1)`; `(S:num->real^3)(SUC i)`;
                   `(y:num->real^3)(i + n - 1)`; `(x:num->real^3)(i + n - 1)`;
                   `(y:num->real^3) i`; `(x:num->real^3) i`;
                   `(cS:num->real^3)(i + n - 1)`; `(cF:num->real^3)(i + n - 1)`;
                   `(cS:num->real^3) i`; `(cF:num->real^3) i`] MOI_FTP_KITE_PAIR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `V:real^3->bool`;
                 `h:real^3->real^3`; `k:real^3->real^3`; `(S:num->real^3) i`;
                 `(S:num->real^3)(i + n - 1)`; `(S:num->real^3)(SUC i)`;
                 `(y:num->real^3)(i + n - 1)`; `(x:num->real^3)(i + n - 1)`;
                 `(y:num->real^3) i`; `(x:num->real^3) i`;
                 `(cS:num->real^3)(i + n - 1)`; `(cF:num->real^3)(i + n - 1)`;
                 `(cS:num->real^3) i`; `(cF:num->real^3) i`] MOI_FTP_VBLK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem: Moise 24.11 in real^3 (orientable case).                *)
(* ------------------------------------------------------------------------- *)

let POLYGON_NBHD_SOLID_TORUS = prove
 (MOI_FND_POLYGON_SOLID_TORUS_3,
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
    ASM_MESON_TAC[MOI_FTA_SUB_FACTS];
    ALL_TAC] THEN
  MP_TAC(ISPEC `l:(real^3->bool)->bool` MOI_FTP_SPHERE1_CYCLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `S:num->real^3` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `n:num`; `S:num->real^3`] MOI_FTP_POLY_DEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `n:num`;
                 `S:num->real^3`] MOI_FTP_POLY_KITES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->real^3` (X_CHOOSE_THEN `x:num->real^3`
    (X_CHOOSE_THEN `cS:num->real^3` (X_CHOOSE_THEN `cF:num->real^3` STRIP_ASSUME_TAC)))) THEN
  ABBREV_TAC `V = {(S:num->real^3) j | j | j < n}` THEN
  SUBGOAL_THEN `!i. (S:num->real^3) i IN V` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `i MOD n` THEN
    SUBGOAL_THEN `0 < n` ASSUME_TAC THENL [UNDISCH_TAC `3 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MOD_LT_EQ] THEN UNDISCH_TAC `0 < n` THEN ARITH_TAC;
      MP_TAC(ISPECL [`S:num->real^3`; `n:num`] MOI_FTP_PER_MOD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num`) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `V:real^3->bool`]
    MOI_FTC_LEV_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "V" THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT];
      EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(S:num->real^3) 0` THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_TAC `k:real^3->real^3`))] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `V:real^3->bool`;
                 `h:real^3->real^3`; `k:real^3->real^3`; `n:num`; `S:num->real^3`;
                 `cS:num->real^3`; `cF:num->real^3`; `y:num->real^3`; `x:num->real^3`]
    MOI_FTP_POLY_BLOCKS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:num->real^3->bool` (X_CHOOSE_THEN `As:num->real^3->bool`
    (X_CHOOSE_THEN `AF:num->real^3->bool` (X_CHOOSE_THEN `bs:num->real^3`
      (X_CHOOSE_TAC `b1:num->real^3`))))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `V:real^3->bool`;
                 `h:real^3->real^3`; `k:real^3->real^3`; `n:num`; `S:num->real^3`;
                 `cS:num->real^3`; `cF:num->real^3`; `Q:num->real^3->bool`;
                 `As:num->real^3->bool`; `AF:num->real^3->bool`; `bs:num->real^3`;
                 `b1:num->real^3`] MOI_FTP_NECK_TORUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `derived_nbhd t l = UNIONS {derived_dual_cell t l ((S:num->real^3) i) | i | i < n}`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_NBHD_UNION_CELLS] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^3->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

