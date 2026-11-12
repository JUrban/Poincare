(* ========================================================================= *)
(* pc_moi_s35_stmt: the statements of Moise 35.1 in tube form                 *)
(* (MOISE_351_STATEMENT, producer MOI_PROD_351 of pc_moi_core_stmt.ml; Moise  *)
(* GTM 47, Sec 35, printed pp.247-251), split into units.  Definitions        *)
(* moi_s35_..., unit statements MOI_S35_... (OCaml term values), glue and     *)
(* sanity theorems MOI_S5D_...; the glue theorems take the unit statements    *)
(* as hypotheses.  pc_moi_s35_stmt_r1.ml, pc_moi_s35_stmt_r2.ml and           *)
(* pc_moi_s35_stmt_r3.ml give the strengthened forms of COMBINE, APPROX and   *)
(* FINAL with their glue, and pc_moi_s35_all.ml derives MOI_PROD_351 from     *)
(* the unit theorems.  Loads after pc_moi_fnd_stmt.ml (which loads            *)
(* pc_moi_core_stmt.ml).                                                      *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. The model near a splitting disk (all in real^3, coordinates p = (x1,  *)
(* x2) and height x3).  The double cube Q = [-1,1]^3 stands for the union    *)
(* of the two dual cells of an edge, the lower half for the A-side cell     *)
(* (unaltered), the upper half for the B-side cell, the middle square for   *)
(* the splitting disk (Fig. 35.1).  moi_s35_n is the sup norm of p, so its  *)
(* level sets are square circles around the vertical axis (the edge).       *)
(* moi_s35_bcell is the altered B-side cell C'_w of p.248: its boundary is  *)
(* the graph of (n - 1/4)/8, which pierces the middle square in the circle  *)
(* n = 1/4 (the book's J_e), dips below it near the axis (the finger) and   *)
(* is retracted from it near the rim.  stube, ttube are the regular         *)
(* neighbourhoods S_e, T_e of J_e (square annulus times interval); bann is  *)
(* the annulus B_e of Bd C'_w.  The A-side cell is cut at a level c close   *)
(* to 0 (chosen generic after the approximations, so that no general        *)
(* position lemma is needed); its trace on ttube is the flat annulus A_e.   *)
(* ------------------------------------------------------------------------- *)

let moi_s35_n = new_definition
 `moi_s35_n (x:real^3) = max (abs(x$1)) (abs(x$2))`;;

let moi_s35_cube = new_definition
 `moi_s35_cube = interval[--vec 1:real^3,vec 1]`;;

let moi_s35_lower = new_definition
 `moi_s35_lower = {x:real^3 | x IN moi_s35_cube /\ x$3 <= &0}`;;

let moi_s35_upper = new_definition
 `moi_s35_upper = {x:real^3 | x IN moi_s35_cube /\ &0 <= x$3}`;;

let moi_s35_mid = new_definition
 `moi_s35_mid = {x:real^3 | x IN moi_s35_cube /\ x$3 = &0}`;;

let moi_s35_slab = new_definition
 `moi_s35_slab = {x:real^3 | x IN moi_s35_cube /\ abs(x$3) <= &1 / &8}`;;

let moi_s35_dom = new_definition
 `moi_s35_dom = {x:real^3 | x IN moi_s35_cube /\ x$3 <= &1 / &8}`;;

let moi_s35_stube = new_definition
 `moi_s35_stube =
    {x:real^3 | &1 / &8 <= moi_s35_n x /\ moi_s35_n x <= &3 / &8 /\
                abs(x$3) <= &1 / &16}`;;

let moi_s35_ttube = new_definition
 `moi_s35_ttube =
    {x:real^3 | &3 / &16 <= moi_s35_n x /\ moi_s35_n x <= &5 / &16 /\
                abs(x$3) <= &1 / &32}`;;

let moi_s35_bcell = new_definition
 `moi_s35_bcell =
    {x:real^3 | x IN moi_s35_cube /\ (moi_s35_n x - &1 / &4) / &8 <= x$3}`;;

let moi_s35_bann = new_definition
 `moi_s35_bann =
    {x:real^3 | &5 / &32 <= moi_s35_n x /\ moi_s35_n x <= &11 / &32 /\
                x$3 = (moi_s35_n x - &1 / &4) / &8}`;;

(* Square circle of radius r at height c, the level square at height c,    *)
(* the flat annulus of ttube at height c, and the lift of the plane to      *)
(* height c (planar polygons and disks at a level are lifts).               *)

let moi_s35_sq = new_definition
 `moi_s35_sq r c = {x:real^3 | moi_s35_n x = r /\ x$3 = c}`;;

let moi_s35_level = new_definition
 `moi_s35_level c = {x:real^3 | x IN moi_s35_cube /\ x$3 = c}`;;

let moi_s35_aflat = new_definition
 `moi_s35_aflat c =
    {x:real^3 | &3 / &16 <= moi_s35_n x /\ moi_s35_n x <= &5 / &16 /\ x$3 = c}`;;

let moi_s35_lift = new_definition
 `moi_s35_lift c (y:real^2) = vector[y$1; y$2; c]:real^3`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_s35_n; moi_s35_cube; moi_s35_bcell; moi_s35_sq; moi_s35_lift];;
(* ------------------------------------------------------------------------- *)
(* 2. Local linear parts and orientation agreement of maps of real^3 (the   *)
(* orientation input missing from the book's final step, p.251).            *)
(* moi_s35_lin_at f x m: f is affine near x with                            *)
(* linear part m.  moi_s35_same_orient f s g t: wherever f (on s) and g (on *)
(* t) are locally affine, their determinants have the same sign.            *)
(* ------------------------------------------------------------------------- *)

let moi_s35_lin_at = new_definition
 `moi_s35_lin_at (f:real^3->real^3) (x:real^3) (m:real^3->real^3) <=>
    linear m /\ ?r. &0 < r /\ !z. z IN ball(x,r) ==> f z = f x + m(z - x)`;;

let moi_s35_same_orient = new_definition
 `moi_s35_same_orient (f:real^3->real^3) (s:real^3->bool)
                      (g:real^3->real^3) (t:real^3->bool) <=>
    !x y m m'. x IN s /\ y IN t /\ moi_s35_lin_at f x m /\ moi_s35_lin_at g y m'
               ==> &0 < det(matrix m) * det(matrix m')`;;

(* ------------------------------------------------------------------------- *)
(* 3. Edge charts (source side).  For every edge e of the graph l, a PL     *)
(* homeomorphism psi e from the model cube onto the union of the dual cells *)
(* of its ends, the lower half onto the A-side cell C(av e) (unaltered),    *)
(* the upper half onto the B-side cell C(bv e) (altered, Fig. 35.1); hence  *)
(* the middle square onto the splitting disk.  The slab |x3| <= 1/8 is thin: *)
(* inside the given relatively open g (av e) and g (bv e) (in the use,     *)
(* g v = preimage of w v under h), its lateral band lies in Bd N, the graph *)
(* meets it only near the axis, and slabs of distinct edges are disjoint.   *)
(* ------------------------------------------------------------------------- *)

let moi_s35_edge = new_definition
 `moi_s35_edge (l:(real^N->bool)->bool) e <=> e IN l /\ aff_dim e = &1`;;

let moi_s35_charts = new_definition
 `moi_s35_charts (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
                 (g:real^N->real^N->bool) (av:(real^N->bool)->real^N)
                 (bv:(real^N->bool)->real^N) (psi:(real^N->bool)->real^3->real^N) <=>
    (!e. moi_s35_edge l e
         ==> {av e} IN l /\ {bv e} IN l /\ ~(av e = bv e) /\
             e = segment[av e,bv e] /\
             (?q. pl_homeomorphism
                    (moi_s35_cube,
                     derived_dual_cell t l (av e) UNION derived_dual_cell t l (bv e))
                    (psi e,q)) /\
             IMAGE (psi e) moi_s35_lower = derived_dual_cell t l (av e) /\
             IMAGE (psi e) moi_s35_upper = derived_dual_cell t l (bv e) /\
             psi e (vec 0) = midpoint(av e,bv e) /\
             IMAGE (psi e) moi_s35_slab SUBSET g (av e) INTER g (bv e) /\
             IMAGE (psi e) {x | x IN moi_s35_slab /\ moi_s35_n x = &1}
               SUBSET derived_frontier t l /\
             (!x. x IN moi_s35_slab /\ psi e x IN UNIONS l
                  ==> moi_s35_n x < &1 / &16)) /\
    (!e e'. moi_s35_edge l e /\ moi_s35_edge l e' /\ ~(e = e')
            ==> DISJOINT (IMAGE (psi e) moi_s35_slab) (IMAGE (psi e') moi_s35_slab))`;;

(* ------------------------------------------------------------------------- *)
(* 4. Source cells.  moi_s35_csrc ... cc v is the cell C'_v of p.248 with   *)
(* the A-side edges cut at the levels cc e: inside the slab of a B-side     *)
(* edge it is the model bcell (finger and rim retraction), inside the slab  *)
(* of an A-side edge it is x3 <= cc e, elsewhere it is the dual cell.  With *)
(* cc = 0 it is the book's C'_v.  moi_s35_cplus v (the domain of the 34.1   *)
(* approximation f_v, the book's C''_v enlarged): the dual cell, the        *)
(* fingers of its B-side edges and the upper half slabs of its A-side edges *)
(* (which contain the tubes S_e).  moi_s35_cbig v adds the whole slabs of   *)
(* its B-side edges (domain of the container approximation E_v).            *)
(* ------------------------------------------------------------------------- *)

let moi_s35_csrc = new_definition
 `moi_s35_csrc (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
               (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
               (psi:(real^N->bool)->real^3->real^N) (cc:(real^N->bool)->real)
               (v:real^N) =
    ((derived_dual_cell t l v DIFF
      UNIONS {IMAGE (psi e) moi_s35_slab | e |
              moi_s35_edge l e /\ (av e = v \/ bv e = v)}) UNION
     UNIONS {IMAGE (psi e) (moi_s35_bcell INTER moi_s35_slab) | e |
             moi_s35_edge l e /\ bv e = v}) UNION
    UNIONS {IMAGE (psi e) {x | x IN moi_s35_slab /\ x$3 <= cc e} | e |
            moi_s35_edge l e /\ av e = v}`;;

let moi_s35_cplus = new_definition
 `moi_s35_cplus (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
                (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
                (psi:(real^N->bool)->real^3->real^N) (v:real^N) =
    (derived_dual_cell t l v UNION
     UNIONS {IMAGE (psi e) (moi_s35_bcell INTER moi_s35_lower) | e |
             moi_s35_edge l e /\ bv e = v}) UNION
    UNIONS {IMAGE (psi e) (moi_s35_slab INTER moi_s35_upper) | e |
            moi_s35_edge l e /\ av e = v}`;;

let moi_s35_cbig = new_definition
 `moi_s35_cbig (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
               (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
               (psi:(real^N->bool)->real^3->real^N) (v:real^N) =
    moi_s35_cplus t l av bv psi v UNION
    UNIONS {IMAGE (psi e) moi_s35_slab | e | moi_s35_edge l e /\ bv e = v}`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_s35_same_orient; moi_s35_charts; moi_s35_csrc; moi_s35_cplus; moi_s35_cbig];;
(* ------------------------------------------------------------------------- *)
(* 5. One edge after the 34.1 approximations (target side, conditions       *)
(* (2)-(8) of pp.248-250 in chart form).  phi = f_a o psi e is the A-side   *)
(* chart (a PL embedding of the model domain); xa = f_a(C'_a) is flat at    *)
(* the level c inside the slab, so A'_e = phi(aflat c) and the general     *)
(* position (8) is the genericity of c for the B-annulus b (no vertex of    *)
(* phi^-1(b) at height c).  xb = f_b(C'_w) (later modified), b = f_b(B_e)   *)
(* with ends b0, b1.  ww is the open target set: the fill condition says    *)
(* xb, the tube S'_e = phi(stube) and every bounded complementary piece of   *)
(* their union lie in ww (this replaces the book's container E_w of (1),   *)
(* (2): a 2-sphere in that union bounds a ball inside ww).  The remaining   *)
(* clauses are (3), (5), (4) and (7).                                       *)
(* ------------------------------------------------------------------------- *)

let moi_s35_edge_conf = new_definition
 `moi_s35_edge_conf (phi:real^3->real^3) (xa:real^3->bool) (xb:real^3->bool)
                    (ww:real^3->bool) (b:real^3->bool) (b0:real^3->bool)
                    (b1:real^3->bool) (c:real) <=>
    pl_map_on moi_s35_dom phi /\
    (!x y. x IN moi_s35_dom /\ y IN moi_s35_dom /\ phi x = phi y ==> x = y) /\
    abs c <= &1 / &512 /\ pl_ball 3 xa /\ pl_ball 3 xb /\ open ww /\
    xa INTER IMAGE phi moi_s35_slab = IMAGE phi {x | x IN moi_s35_slab /\ x$3 <= c} /\
    xb UNION IMAGE phi moi_s35_stube UNION
    inside (xb UNION IMAGE phi moi_s35_stube) SUBSET ww /\
    frontier xa INTER xb SUBSET
    IMAGE phi {x | x IN moi_s35_level c /\ moi_s35_n x < &5 / &16} /\
    frontier xa INTER frontier xb SUBSET IMAGE phi (moi_s35_aflat c) /\
    pl_annulus_with_ends b b0 b1 /\ b SUBSET frontier xb /\
    b SUBSET IMAGE phi (interior moi_s35_stube) /\
    DISJOINT (b0 UNION b1) (IMAGE phi moi_s35_ttube) /\
    frontier xb INTER IMAGE phi moi_s35_ttube SUBSET b /\
    IMAGE phi (moi_s35_sq (&3 / &16) c) SUBSET interior xb /\
    DISJOINT (IMAGE phi (moi_s35_sq (&5 / &16) c)) xb /\
    (?k0. k0 IN components {x | x IN moi_s35_dom /\ phi x IN b /\ x$3 <= c} /\
          !k. k IN components {x | x IN moi_s35_dom /\ phi x IN b /\ x$3 <= c} /\
              ~(k = k0) ==> k SUBSET moi_s35_ttube) /\
    (?k1. k1 IN components {x | x IN moi_s35_dom /\ phi x IN b /\ c <= x$3} /\
          !k. k IN components {x | x IN moi_s35_dom /\ phi x IN b /\ c <= x$3} /\
              ~(k = k1) ==> k SUBSET moi_s35_ttube) /\
    (?k:(real^3->bool)->bool.
        FINITE k /\ simplicial_complex k /\
        UNIONS k = {x | x IN moi_s35_dom /\ phi x IN b} /\
        !v. {v} IN k ==> ~(v$3 = c))`;;

(* The intersection circles A'_e INTER B'_e in the model (the set the       *)
(* Minimality condition of p.250 counts, here per edge), essential circles  *)
(* (planar polygons at the level c around the inner square), and the       *)
(* single-circle outcome of Lemmas 1-3 in the form used by the final step   *)
(* (Bd X_a meets Bd X_b in one essential polygon j and X_b in the planar    *)
(* disk bounded by j).                                                     *)

let moi_s35_circles = new_definition
 `moi_s35_circles (phi:real^3->real^3) (b:real^3->bool) c =
    {x | x IN moi_s35_dom /\ phi x IN b /\ x$3 = c}`;;

let moi_s35_ess = new_definition
 `moi_s35_ess c (k:real^3->bool) <=>
    ?j:real^2->bool. pl_sphere 1 j /\ k = IMAGE (moi_s35_lift c) j /\
                     !y. moi_s35_n (moi_s35_lift c y) <= &3 / &16 ==> y IN inside j`;;

let moi_s35_single = new_definition
 `moi_s35_single (phi:real^3->real^3) (xa:real^3->bool) (xb:real^3->bool) c <=>
    ?j:real^2->bool.
      pl_sphere 1 j /\
      IMAGE (moi_s35_lift c) j SUBSET
      moi_s35_aflat c DIFF (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c) /\
      (!y. moi_s35_n (moi_s35_lift c y) <= &3 / &16 ==> y IN inside j) /\
      frontier xa INTER frontier xb = IMAGE phi (IMAGE (moi_s35_lift c) j) /\
      frontier xa INTER xb = IMAGE phi (IMAGE (moi_s35_lift c) (j UNION inside j))`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_s35_edge_conf; moi_s35_circles; moi_s35_ess; moi_s35_single];;
(* ------------------------------------------------------------------------- *)
(* 6. Packages passed between the units.  ach e = f_(av e) o psi e is the   *)
(* A-side chart of the edge e, bch e = f_(bv e) o psi e the B-side one;     *)
(* bant e = f_b(B_e) with its ends.  moi_s35_source_ok: source facts (the   *)
(* altered cells are PL 3-cells for all admissible levels, the domains of  *)
(* the approximations and the bigger cells are PL 3-cells, and compact      *)
(* cores away from the tubes cover the graph).  moi_s35_frame: the target  *)
(* conditions common to the states before and after the circle removal    *)
(* (a fill condition for each cell with all tubes of its B-side edges),     *)
(* orientation agreement of the two charts of an edge (from the degree     *)
(* lemma), overlaps inside the slab images, the B-side interface level     *)
(* 1/8 clear of the tube and of the A-cell, separation of cells from slabs  *)
(* of edges they are not on, slabs of distinct edges disjoint, the graph in *)
(* the interiors of the cells and off the tubes.  No local finiteness in   *)
(* the target is asked (h need not be closed; PL-ness is local in N).      *)
(* ------------------------------------------------------------------------- *)

let moi_s35_ach = new_definition
 `moi_s35_ach (ff:real^N->real^N->real^3) (av:(real^N->bool)->real^N)
              (psi:(real^N->bool)->real^3->real^N) e = ff (av e) o psi e`;;

let moi_s35_bch = new_definition
 `moi_s35_bch (ff:real^N->real^N->real^3) (bv:(real^N->bool)->real^N)
              (psi:(real^N->bool)->real^3->real^N) e = ff (bv e) o psi e`;;

let moi_s35_source_ok = new_definition
 `moi_s35_source_ok (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
                    (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
                    (psi:(real^N->bool)->real^3->real^N) <=>
    (!cc v. (!e. abs(cc e) <= &1 / &512) /\ {v} IN l
            ==> (?bs. pl_cell_with_boundary 3 (moi_s35_csrc t l av bv psi cc v) bs) /\
                moi_s35_csrc t l av bv psi cc v SUBSET moi_s35_cplus t l av bv psi v) /\
    (!v. {v} IN l
         ==> (?bs. pl_cell_with_boundary 3 (moi_s35_cplus t l av bv psi v) bs) /\
             (?bs. pl_cell_with_boundary 3 (moi_s35_cbig t l av bv psi v) bs)) /\
    (?kk:real^N->real^N->bool.
        (!v. {v} IN l
             ==> compact (kk v) /\
                 (!cc. (!e. abs(cc e) <= &1 / &512)
                       ==> kk v SUBSET (subtopology euclidean (UNIONS t)) interior_of
                                       (moi_s35_csrc t l av bv psi cc v)) /\
                 (!e. moi_s35_edge l e ==> DISJOINT (kk v) (IMAGE (psi e) moi_s35_stube))) /\
        UNIONS l SUBSET UNIONS {kk v | v | {v} IN l})`;;

let moi_s35_frame = new_definition
 `moi_s35_frame (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
                (h:real^N->real^3) (w:real^N->real^3->bool)
                (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
                (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3)
                (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) <=>
    (!v. {v} IN l
         ==> pl_map_on (moi_s35_cplus t l av bv psi v) (ff v) /\
             (!x y. x IN moi_s35_cplus t l av bv psi v /\
                    y IN moi_s35_cplus t l av bv psi v /\ ff v x = ff v y ==> x = y) /\
             pl_ball 3 (xx v) /\ xx v SUBSET w v /\
             xx v UNION
             UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e |
                     moi_s35_edge l e /\ bv e = v} UNION
             inside (xx v UNION
                     UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e |
                             moi_s35_edge l e /\ bv e = v}) SUBSET w v) /\
    (!e. moi_s35_edge l e
         ==> abs(cc e) <= &1 / &512 /\
             moi_s35_same_orient (moi_s35_ach ff av psi e) (interior moi_s35_dom)
                                 (moi_s35_bch ff bv psi e) (interior moi_s35_bcell) /\
             xx (av e) INTER xx (bv e) SUBSET IMAGE (moi_s35_ach ff av psi e) moi_s35_slab /\
             DISJOINT (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)))
                      (IMAGE (moi_s35_ach ff av psi e) moi_s35_stube) /\
             DISJOINT (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)))
                      (xx (av e))) /\
    (!e v. moi_s35_edge l e /\ {v} IN l /\ ~(v = av e) /\ ~(v = bv e)
           ==> DISJOINT (xx v) (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab)) /\
    (!e e'. moi_s35_edge l e /\ moi_s35_edge l e' /\ ~(e = e')
            ==> DISJOINT (IMAGE (moi_s35_ach ff av psi e) moi_s35_slab)
                         (IMAGE (moi_s35_ach ff av psi e') moi_s35_slab) /\
                DISJOINT (IMAGE (moi_s35_bch ff bv psi e) (moi_s35_level (&1 / &8)))
                         (IMAGE (moi_s35_ach ff av psi e') moi_s35_slab)) /\
    (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
           ==> DISJOINT (xx u) (xx v)) /\
    (!y. y IN IMAGE h (UNIONS l)
         ==> ?v. {v} IN l /\ y IN interior (xx v) /\
                 !e. moi_s35_edge l e
                     ==> ~(y IN IMAGE (moi_s35_ach ff av psi e) moi_s35_stube))`;;

(* Before the circle removal: the cells are the images of the altered      *)
(* source cells and every edge is in the configuration of p.250.           *)

let moi_s35_pre = new_definition
 `moi_s35_pre (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
              (h:real^N->real^3) (w:real^N->real^3->bool)
              (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
              (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3)
              (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) <=>
    moi_s35_frame t l h w av bv psi ff xx cc /\
    (!v. {v} IN l ==> xx v = IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v)) /\
    (!e. moi_s35_edge l e
         ==> moi_s35_edge_conf (moi_s35_ach ff av psi e) (xx (av e)) (xx (bv e)) (w (bv e))
               (IMAGE (moi_s35_bch ff bv psi e) moi_s35_bann)
               (IMAGE (moi_s35_bch ff bv psi e)
                      (moi_s35_sq (&5 / &32) (--(&3) / &256)))
               (IMAGE (moi_s35_bch ff bv psi e)
                      (moi_s35_sq (&11 / &32) (&3 / &256)))
               (cc e))`;;

(* After the circle removal: the cells agree with the images of the source *)
(* cells outside the tubes of their B-side edges, and at every edge the     *)
(* boundaries meet in one essential polygon (Lemmas 2-3, p.250).            *)

let moi_s35_post = new_definition
 `moi_s35_post (t:(real^N->bool)->bool) (l:(real^N->bool)->bool)
               (h:real^N->real^3) (w:real^N->real^3->bool)
               (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
               (psi:(real^N->bool)->real^3->real^N) (ff:real^N->real^N->real^3)
               (xx:real^N->real^3->bool) (cc:(real^N->bool)->real) <=>
    moi_s35_frame t l h w av bv psi ff xx cc /\
    (!v. {v} IN l
         ==> xx v DIFF UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e |
                               moi_s35_edge l e /\ bv e = v} =
             IMAGE (ff v) (moi_s35_csrc t l av bv psi cc v) DIFF
             UNIONS {IMAGE (moi_s35_ach ff av psi e) moi_s35_stube | e |
                     moi_s35_edge l e /\ bv e = v}) /\
    (!e. moi_s35_edge l e
         ==> (?b. moi_s35_edge_conf (moi_s35_ach ff av psi e) (xx (av e)) (xx (bv e))
                    (w (bv e)) b
                    (IMAGE (moi_s35_bch ff bv psi e)
                           (moi_s35_sq (&5 / &32) (--(&3) / &256)))
                    (IMAGE (moi_s35_bch ff bv psi e)
                           (moi_s35_sq (&11 / &32) (&3 / &256)))
                    (cc e)) /\
             moi_s35_single (moi_s35_ach ff av psi e) (xx (av e)) (xx (bv e)) (cc e))`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_s35_ach; moi_s35_source_ok; moi_s35_frame; moi_s35_pre; moi_s35_post];;
(* ========================================================================= *)
(* 7. Unit statements (OCaml values MOI_S35_...; closed boolean terms).     *)
(* Stage statements that need lemma statements or foundation terms take     *)
(* them as antecedents (built with mk_imp), so that each unit can be        *)
(* proved on its own.                                                       *)
(* ========================================================================= *)

(* 7.1 Tube fact missing from MOI_FND_GRAPH_TUBE (unit s35_chart): three    *)
(* dual cells never meet (their stars in the first derived subdivision meet *)
(* only in barycentres of simplices of dimension at least 2, which N does   *)
(* not reach); hence distinct splitting disks are disjoint.                 *)

let MOI_S35_TUBE_TRIPLE =
 `!(t:(real^N->bool)->bool) l u v w.
     graph_in_complex t l /\ {u} IN l /\ {v} IN l /\ {w} IN l /\
     ~(u = v) /\ ~(u = w) /\ ~(v = w)
     ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
         derived_dual_cell t l w = {}`;;

(* 7.2 Lemma statements of unit s35_mark.  MARKER (p.249 (4), (6); DG       *)
(* section34Marker_of_dist_lt): an embedding of a PL 3-cell close to h on   *)
(* the cell boundary covers h of the interior part at distance at least e   *)
(* from h(bs) (Jordan-Brouwer and Borsuk maps, BORSUK_MAP_ESSENTIAL_BOUNDED_ *)
(* COMPONENT).  CELL_341: 34.1 for PL 3-cells in real^N.  FILL: sets close  *)
(* to a compact set with connected complement have their bounded           *)
(* complementary pieces close to it.                                        *)

let MOI_S35_MARKER =
 `!(s:real^N->bool) bs k (f:real^N->real^3) (h:real^N->real^3) e.
     pl_cell_with_boundary 3 s bs /\ compact k /\ k SUBSET s DIFF bs /\
     f continuous_on s /\ (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     h continuous_on s /\ (!x y. x IN s /\ y IN s /\ h x = h y ==> x = y) /\
     (!x. x IN bs ==> dist(f x,h x) < e) /\
     (!x y. x IN k /\ y IN bs ==> e <= dist(h x,h y))
     ==> IMAGE h k SUBSET interior (IMAGE f s)`;;

let MOI_S35_CELL_341 =
 `MOISE_341_STATEMENT
  ==> !(s:real^N->bool) bs (h:real^N->real^3) e.
        pl_cell_with_boundary 3 s bs /\ h continuous_on s /\
        (!x y. x IN s /\ y IN s /\ h x = h y ==> x = y) /\ &0 < e
        ==> ?f. pl_map_on s f /\
                (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
                !x. x IN s ==> dist(f x,h x) < e`;;

let MOI_S35_FILL =
 `!(k:real^3->bool) w.
     compact k /\ ~(k = {}) /\ connected ((:real^3) DIFF k) /\ open w /\ k SUBSET w
     ==> ?e. &0 < e /\
             !k'. compact k' /\ (!x. x IN k' ==> setdist({x},k) < e)
                  ==> k' UNION inside k' SUBSET w`;;

(* 7.3 Orientation (unit s35_deg).  LOCAL_SIGN: a continuous injective map  *)
(* of a connected open set in real^3 has the same determinant sign at all   *)
(* points where it is locally affine (local degree via homotopies of small  *)
(* sphere maps and HOMOTOPIC_LINEAR_MAPS_ALT, degree.ml).  CLOSE_SIGN: two  *)
(* such maps within r of each other, the first covering a ball of radius 3r, *)
(* have the same sign (the second composed with the inverse of the first is *)
(* close to the identity on that ball).                                      *)

let MOI_S35_LOCAL_SIGN =
 `!(f:real^3->real^3) s x y m m'.
     open s /\ connected s /\ f continuous_on s /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     x IN s /\ y IN s /\ moi_s35_lin_at f x m /\ moi_s35_lin_at f y m'
     ==> &0 < det(matrix m) * det(matrix m')`;;

let MOI_S35_CLOSE_SIGN =
 `!(f:real^3->real^3) g s y0 r.
     open s /\ connected s /\ f continuous_on s /\ g continuous_on s /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
     (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y) /\
     (!x. x IN s ==> dist(f x,g x) < r) /\ cball(y0,&3 * r) SUBSET IMAGE f s
     ==> moi_s35_same_orient f s g s`;;

(* 7.4 Extension lemmas (unit s35_ext).  ONE_DISK_EXT: a PL homeomorphism of *)
(* one boundary disk extends over PL 3-balls taking a second disk onto a    *)
(* second disk (no orientation condition).  TWO_DISK_EXT: prescribed maps   *)
(* on two disjoint boundary disks extend when local PL extensions near      *)
(* interior points of the disks, taking the u-side into w, have the same    *)
(* orientation (the edge-matching step of p.251 the book leaves implicit).  *)

let MOI_S35_ONE_DISK_EXT =
 `!(u:real^3->bool) w d0 j0 d1 j1 e0 i0 e1 i1 (g0:real^3->real^3) g0'.
     pl_ball 3 u /\ pl_ball 3 w /\
     pl_cell_with_boundary 2 d0 j0 /\ pl_cell_with_boundary 2 d1 j1 /\
     d0 SUBSET frontier u /\ d1 SUBSET frontier u /\ DISJOINT d0 d1 /\
     pl_cell_with_boundary 2 e0 i0 /\ pl_cell_with_boundary 2 e1 i1 /\
     e0 SUBSET frontier w /\ e1 SUBSET frontier w /\ DISJOINT e0 e1 /\
     pl_homeomorphism (d0,e0) (g0,g0')
     ==> ?f f'. pl_homeomorphism (u,w) (f,f') /\
                (!x. x IN d0 ==> f x = g0 x) /\ IMAGE f d1 = e1`;;

let MOI_S35_TWO_DISK_EXT =
 `!(u:real^3->bool) w d0 j0 d1 j1 e0 i0 e1 i1 (g0:real^3->real^3) g0' g1 g1'
   o0 o1 (gg0:real^3->real^3) gg1.
     pl_ball 3 u /\ pl_ball 3 w /\
     pl_cell_with_boundary 2 d0 j0 /\ pl_cell_with_boundary 2 d1 j1 /\
     d0 SUBSET frontier u /\ d1 SUBSET frontier u /\ DISJOINT d0 d1 /\
     pl_cell_with_boundary 2 e0 i0 /\ pl_cell_with_boundary 2 e1 i1 /\
     e0 SUBSET frontier w /\ e1 SUBSET frontier w /\ DISJOINT e0 e1 /\
     pl_homeomorphism (d0,e0) (g0,g0') /\ pl_homeomorphism (d1,e1) (g1,g1') /\
     open o0 /\ open o1 /\ ~(o0 INTER (d0 DIFF j0) = {}) /\
     ~(o1 INTER (d1 DIFF j1) = {}) /\
     pl_map_on o0 gg0 /\ (!x y. x IN o0 /\ y IN o0 /\ gg0 x = gg0 y ==> x = y) /\
     pl_map_on o1 gg1 /\ (!x y. x IN o1 /\ y IN o1 /\ gg1 x = gg1 y ==> x = y) /\
     (!x. x IN o0 INTER d0 ==> gg0 x = g0 x) /\
     (!x. x IN o1 INTER d1 ==> gg1 x = g1 x) /\
     IMAGE gg0 (o0 INTER u) SUBSET w /\ IMAGE gg1 (o1 INTER u) SUBSET w /\
     moi_s35_same_orient gg0 o0 gg1 o1
     ==> ?f f'. pl_homeomorphism (u,w) (f,f') /\
                (!x. x IN d0 ==> f x = g0 x) /\ (!x. x IN d1 ==> f x = g1 x)`;;

(* 7.5 The slab lemma (unit s35_slab): the part of a triangulated surface   *)
(* in real^3 between two levels containing no vertex is the product of its  *)
(* lower level set with an interval, height-preservingly (the push-offs of  *)
(* Lemmas 2-3 to the levels c +- eta, p.250).                               *)

let MOI_S35_SLAB_PRODUCT =
 `!(k:(real^3->bool)->bool) c d.
     FINITE k /\ simplicial_complex k /\ (!s. s IN k ==> aff_dim s <= &2) /\
     c < d /\ (!v. {v} IN k ==> v$3 < c \/ d < v$3)
     ==> ?(f:real^(3,1)finite_sum->real^3) g.
           homeomorphism
             ({x | x IN UNIONS k /\ x$3 = c} PCROSS interval[vec 0:real^1,vec 1],
              {x | x IN UNIONS k /\ c <= x$3 /\ x$3 <= d}) (f,g) /\
           pl_map_on ({x | x IN UNIONS k /\ x$3 = c} PCROSS
                      interval[vec 0:real^1,vec 1]) f /\
           (!x s. x IN UNIONS k /\ x$3 = c /\ s IN interval[vec 0:real^1,vec 1]
                  ==> (f(pastecart x s))$3 = c + drop s * (d - c)) /\
           (!x. x IN UNIONS k /\ x$3 = c ==> f(pastecart x (vec 0)) = x)`;;

map type_of [MOI_S35_TUBE_TRIPLE; MOI_S35_MARKER; MOI_S35_CELL_341; MOI_S35_FILL;
             MOI_S35_LOCAL_SIGN; MOI_S35_CLOSE_SIGN; MOI_S35_ONE_DISK_EXT;
             MOI_S35_TWO_DISK_EXT; MOI_S35_SLAB_PRODUCT];;
(* 7.6 Stage statements.  CHARTS (unit s35_chart) and SOURCE (unit          *)
(* s35_cells): the source side of p.248 (Fig. 35.1, C'_v, S_e, T_e, A_e,    *)
(* B_e, C''_v) from the tube foundation and the triple-intersection fact.   *)

let MOI_S35_CHARTS = mk_imp(mk_conj(MOI_FND_GRAPH_TUBE,MOI_S35_TUBE_TRIPLE),
 `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool).
     graph_in_complex t l /\
     (!v. {v} IN l ==> open_in (subtopology euclidean (UNIONS t)) (g v) /\
                       derived_dual_cell t l v SUBSET g v)
     ==> ?av bv psi. moi_s35_charts t l g av bv psi`);;

let MOI_S35_SOURCE = mk_imp(mk_conj(MOI_FND_GRAPH_TUBE,MOI_S35_TUBE_TRIPLE),
 `!(t:(real^N->bool)->bool) l (g:real^N->real^N->bool) av bv psi.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi
     ==> moi_s35_source_ok t l av bv psi`);;

(* APPROX (unit s35_approx): 34.1 on every C''_v with lf small errors, then *)
(* conditions (2)-(8) of pp.249-250, the generic levels, the fill clauses   *)
(* and the orientation agreement (CLOSE_SIGN on the fingers).               *)

let MOI_S35_APPROX = mk_imp(list_mk_conj
  [`MOISE_341_STATEMENT`; MOI_S35_MARKER; MOI_S35_CELL_341; MOI_S35_FILL;
   MOI_S35_LOCAL_SIGN; MOI_S35_CLOSE_SIGN; MOI_FND_GRAPH_TUBE; MOI_S35_TUBE_TRIPLE],
 `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w av bv psi.
     graph_in_complex t l /\ h continuous_on UNIONS t /\
     (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
     (!v. {v} IN l ==> open (w v) /\ IMAGE h (derived_dual_cell t l v) SUBSET w v) /\
     moi_s35_charts t l (\v. {x | x IN UNIONS t /\ h x IN w v}) av bv psi /\
     moi_s35_source_ok t l av bv psi
     ==> ?ff xx cc. moi_s35_pre t l h w av bv psi ff xx cc`);;

(* LEMMA1 and SINGLE_FROM_ONE (unit s35_min_a): Lemma 1 of p.250 in chart  *)
(* form (the circles are polygons at the level; a circle is essential in   *)
(* A'_e iff it bounds no disk in B'_e; some circle is essential), and the  *)
(* passage from one essential circle to the single-circle predicate.       *)

let MOI_S35_LEMMA1 = mk_imp(`MOISE_273_STATEMENT (:3)`,
 `!phi xa xb ww b b0 b1 c.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c
     ==> FINITE (components (moi_s35_circles phi b c)) /\
         (!k. k IN components (moi_s35_circles phi b c)
              ==> ?j:real^2->bool. pl_sphere 1 j /\ k = IMAGE (moi_s35_lift c) j) /\
         (!k. k IN components (moi_s35_circles phi b c)
              ==> (moi_s35_ess c k <=>
                   ~(?d. pl_cell_with_boundary 2 d (IMAGE phi k) /\ d SUBSET b))) /\
         (?k. k IN components (moi_s35_circles phi b c) /\ moi_s35_ess c k)`);;

let MOI_S35_SINGLE_FROM_ONE =
 `!phi xa xb ww b b0 b1 c k.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
     components (moi_s35_circles phi b c) = {k} /\ moi_s35_ess c k
     ==> moi_s35_single phi xa xb c`;;

(* DISK_SWAP (unit s35_min_b, Lemma 2 of p.250 as a step: an inessential    *)
(* circle is removed by swapping the disk it bounds in B'_e for a planar    *)
(* disk pushed to a level c +- eta) and ANNULUS_SWAP (unit s35_min_c, Lemma *)
(* 3 of p.251 as a step).  Both lower the number of circles of this edge   *)
(* (the per-edge Minimality condition) and change xb only inside the image  *)
(* of a compact part of the open tube missing the two ends of A'_e.          *)

let MOI_S35_DISK_SWAP = mk_imp(list_mk_conj
  [`PL_SCHOENFLIES_3_STATEMENT`; MOI_S35_LEMMA1; MOI_S35_SLAB_PRODUCT],
 `!phi xa xb ww b b0 b1 c k.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
     k IN components (moi_s35_circles phi b c) /\ ~moi_s35_ess c k
     ==> ?xb' b'. moi_s35_edge_conf phi xa xb' ww b' b0 b1 c /\
                  CARD (components (moi_s35_circles phi b' c)) <
                  CARD (components (moi_s35_circles phi b c)) /\
                  ?kk. compact kk /\ kk SUBSET interior moi_s35_stube /\
                       DISJOINT kk (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c) /\
                       xb' DIFF IMAGE phi kk = xb DIFF IMAGE phi kk`);;

let MOI_S35_ANNULUS_SWAP = mk_imp(list_mk_conj
  [`PL_SCHOENFLIES_3_STATEMENT`; MOI_S35_LEMMA1; MOI_S35_SLAB_PRODUCT],
 `!phi xa xb ww b b0 b1 c.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
     (!k. k IN components (moi_s35_circles phi b c) ==> moi_s35_ess c k) /\
     2 <= CARD (components (moi_s35_circles phi b c))
     ==> ?xb' b'. moi_s35_edge_conf phi xa xb' ww b' b0 b1 c /\
                  CARD (components (moi_s35_circles phi b' c)) <
                  CARD (components (moi_s35_circles phi b c)) /\
                  ?kk. compact kk /\ kk SUBSET interior moi_s35_stube /\
                       DISJOINT kk (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c) /\
                       xb' DIFF IMAGE phi kk = xb DIFF IMAGE phi kk`);;

(* The circle removal for one edge (proved by glue MOI_S5D_REMOVAL below    *)
(* from the step statements, by induction on the number of circles).       *)

let MOI_S35_REMOVAL =
 `!phi xa xb ww b b0 b1 c.
     moi_s35_edge_conf phi xa xb ww b b0 b1 c
     ==> ?xb' b'. moi_s35_edge_conf phi xa xb' ww b' b0 b1 c /\
                  moi_s35_single phi xa xb' c /\
                  ?kk. compact kk /\ kk SUBSET interior moi_s35_stube /\
                       DISJOINT kk (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c) /\
                       xb' DIFF IMAGE phi kk = xb DIFF IMAGE phi kk`;;

(* COMBINE (unit s35_comb): the removal at all edges at once (finitely many *)
(* B-side edges per vertex, supports in disjoint tubes).                     *)

let MOI_S35_COMBINE = mk_imp(MOI_S35_REMOVAL,
 `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w av bv psi ff xx cc.
     moi_s35_pre t l h w av bv psi ff xx cc
     ==> ?xx'. moi_s35_post t l h w av bv psi ff xx' cc`);;

(* Final cells D_v of p.251 (delete from X_w the interiors of the A-cells   *)
(* of its B-side edges) and the disks D_v INTER D_w.                        *)

let moi_s35_dcell = new_definition
 `moi_s35_dcell (l:(real^N->bool)->bool) (av:(real^N->bool)->real^N)
                (bv:(real^N->bool)->real^N) (xx:real^N->real^3->bool) v =
    xx v DIFF UNIONS {interior (xx (av e)) | e | moi_s35_edge l e /\ bv e = v}`;;

let moi_s35_ddisk = new_definition
 `moi_s35_ddisk (av:(real^N->bool)->real^N) (bv:(real^N->bool)->real^N)
                (xx:real^N->real^3->bool) e =
    frontier (xx (av e)) INTER xx (bv e)`;;

(* FINAL_CELLS (unit s35_fin_a): the final cells are PL 3-balls meeting in  *)
(* the disks along edges only.  FINAL (unit s35_fin_b): the PL embedding of *)
(* N (cores by f_v, A-side squeezes by ONE_DISK_EXT, B-side edge pieces by  *)
(* TWO_DISK_EXT with the orientation agreement of the frame, lf pasting).   *)

let MOI_S35_FINAL_CELLS = mk_imp(`PL_SCHOENFLIES_3_STATEMENT`,
 `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_source_ok t l av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc
     ==> (!v. {v} IN l ==> pl_ball 3 (moi_s35_dcell l av bv xx v)) /\
         (!e. moi_s35_edge l e
              ==> moi_s35_dcell l av bv xx (av e) INTER moi_s35_dcell l av bv xx (bv e) =
                  moi_s35_ddisk av bv xx e /\
                  (?j. pl_cell_with_boundary 2 (moi_s35_ddisk av bv xx e) j) /\
                  moi_s35_ddisk av bv xx e SUBSET frontier (moi_s35_dcell l av bv xx (av e)) /\
                  moi_s35_ddisk av bv xx e SUBSET frontier (moi_s35_dcell l av bv xx (bv e))) /\
         (!e e'. moi_s35_edge l e /\ moi_s35_edge l e' /\ ~(e = e')
                 ==> DISJOINT (moi_s35_ddisk av bv xx e) (moi_s35_ddisk av bv xx e')) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
                ==> DISJOINT (moi_s35_dcell l av bv xx u) (moi_s35_dcell l av bv xx v)) /\
         UNIONS {moi_s35_dcell l av bv xx v | v | {v} IN l} = UNIONS {xx v | v | {v} IN l}`);;

let MOI_S35_FINAL = mk_imp(list_mk_conj
  [MOI_FND_GRAPH_TUBE; MOI_S35_TUBE_TRIPLE; MOI_S35_FINAL_CELLS; MOI_S35_ONE_DISK_EXT;
   MOI_S35_TWO_DISK_EXT; MOI_S35_LOCAL_SIGN; `PL_SCHOENFLIES_3_STATEMENT`],
 `!(t:(real^N->bool)->bool) l (h:real^N->real^3) w g av bv psi ff xx cc.
     graph_in_complex t l /\ moi_s35_charts t l g av bv psi /\
     moi_s35_source_ok t l av bv psi /\ moi_s35_post t l h w av bv psi ff xx cc
     ==> ?f. pl_map_on (derived_nbhd t l) f /\
             (!x y. x IN derived_nbhd t l /\ y IN derived_nbhd t l /\ f x = f y
                    ==> x = y) /\
             IMAGE h (UNIONS l) SUBSET interior (IMAGE f (derived_nbhd t l)) /\
             (!v. {v} IN l ==> IMAGE f (derived_dual_cell t l v) SUBSET w v)`);;

map type_of [MOI_S35_CHARTS; MOI_S35_SOURCE; MOI_S35_APPROX; MOI_S35_LEMMA1;
             MOI_S35_SINGLE_FROM_ONE; MOI_S35_DISK_SWAP; MOI_S35_ANNULUS_SWAP;
             MOI_S35_REMOVAL; MOI_S35_COMBINE; MOI_S35_FINAL_CELLS; MOI_S35_FINAL];;
map (fun tm -> frees tm) [MOI_S35_CHARTS; MOI_S35_APPROX; MOI_S35_FINAL; MOI_S35_COMBINE];;
(* ========================================================================= *)
(* 8. Glue.  MOI_S5D_REMOVAL_CORE: the per-edge Minimality argument of      *)
(* pp.250-251 as an induction on the number of circles of the edge (the     *)
(* book minimizes a total over all edges, which is infinite for infinite K): *)
(* while some circle is inessential, Lemma 2 (disk swap); while all are     *)
(* essential and at least two, Lemma 3 (annulus swap); Lemma 1 leaves one   *)
(* essential circle.  Supports accumulate in a compact part of the tube.    *)
(* ========================================================================= *)

let moi_s5d_vars = [`phi:real^3->real^3`; `xa:real^3->bool`; `xb:real^3->bool`;
              `ww:real^3->bool`; `b:real^3->bool`; `b0:real^3->bool`;
              `b1:real^3->bool`; `c:real`];;
let moi_s5d_concl_at xb_tm =
    subst [xb_tm,`xb:real^3->bool`]
     `?xb' b'. moi_s35_edge_conf phi xa xb' ww b' b0 b1 c /\
               moi_s35_single phi xa xb' c /\
               ?kk. compact kk /\ kk SUBSET interior moi_s35_stube /\
                    DISJOINT kk (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c) /\
                    xb' DIFF IMAGE phi kk = (xb:real^3->bool) DIFF IMAGE phi kk`;;

let moi_s5d_auxg =
 `!n phi xa xb ww b b0 b1 c.
       moi_s35_edge_conf phi xa xb ww b b0 b1 c /\
       CARD (components (moi_s35_circles phi b c)) = n
       ==> ?xb' b'. moi_s35_edge_conf phi xa xb' ww b' b0 b1 c /\
                    moi_s35_single phi xa xb' c /\
                    ?kk. compact kk /\ kk SUBSET interior moi_s35_stube /\
                         DISJOINT kk (moi_s35_sq (&3 / &16) c UNION
                                      moi_s35_sq (&5 / &16) c) /\
                         xb' DIFF IMAGE phi kk = xb DIFF IMAGE phi kk`;;

let moi_s5d_aux_tac l1 one dsk ann =
    MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
    DISCH_THEN(fun ih ->
      MAP_EVERY X_GEN_TAC moi_s5d_vars THEN STRIP_TAC THEN
      SUBGOAL_THEN
       (mk_forall(`xb1:real^3->bool`, mk_forall(`bn:real^3->bool`,
         mk_forall(`kk1:real^3->bool`,
          mk_imp(`moi_s35_edge_conf phi xa xb1 ww bn b0 b1 c /\
                  CARD (components (moi_s35_circles phi bn c)) <
                  CARD (components (moi_s35_circles phi b c)) /\
                  compact kk1 /\ kk1 SUBSET interior moi_s35_stube /\
                  DISJOINT kk1 (moi_s35_sq (&3 / &16) c UNION moi_s35_sq (&5 / &16) c) /\
                  xb1 DIFF IMAGE phi kk1 = xb DIFF IMAGE phi kk1`,
                 moi_s5d_concl_at `xb:real^3->bool`)))))
      (fun stp ->
        ASM_CASES_TAC
         `?k:real^3->bool. k IN components (moi_s35_circles phi b c) /\ ~moi_s35_ess c k`
        THENL
         [FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
          MP_TAC(SPECL (moi_s5d_vars @ [`k:real^3->bool`]) dsk) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `xb1:real^3->bool` (X_CHOOSE_THEN `bn:real^3->bool`
            (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
              (X_CHOOSE_THEN `kk1:real^3->bool` STRIP_ASSUME_TAC))))) THEN
          MATCH_MP_TAC stp THEN
          MAP_EVERY EXISTS_TAC
           [`xb1:real^3->bool`; `bn:real^3->bool`; `kk1:real^3->bool`] THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN
         `!k:real^3->bool. k IN components (moi_s35_circles phi b c) ==> moi_s35_ess c k`
        ASSUME_TAC THENL
         [UNDISCH_TAC
           `~(?k:real^3->bool. k IN components (moi_s35_circles phi b c) /\
                               ~moi_s35_ess c k)` THEN MESON_TAC[];
          ALL_TAC] THEN
        ASM_CASES_TAC `2 <= CARD (components (moi_s35_circles phi b c))` THENL
         [MP_TAC(SPECL moi_s5d_vars ann) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `xb1:real^3->bool` (X_CHOOSE_THEN `bn:real^3->bool`
            (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
              (X_CHOOSE_THEN `kk1:real^3->bool` STRIP_ASSUME_TAC))))) THEN
          MATCH_MP_TAC stp THEN
          MAP_EVERY EXISTS_TAC
           [`xb1:real^3->bool`; `bn:real^3->bool`; `kk1:real^3->bool`] THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MP_TAC(SPECL moi_s5d_vars l1) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
          (CONJUNCTS_THEN2 (K ALL_TAC)
            (X_CHOOSE_THEN `k0:real^3->bool` STRIP_ASSUME_TAC)))) THEN
        SUBGOAL_THEN `components (moi_s35_circles phi b c) = {k0:real^3->bool}`
        ASSUME_TAC THENL
         [MP_TAC(MATCH_MP (TAUT `(p /\ q <=> r) ==> p ==> q ==> r`)
                   (ISPEC `components (moi_s35_circles phi b c)` CARD_LE_1)) THEN
          ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
          ANTS_TAC THENL
           [UNDISCH_TAC `~(2 <= CARD (components (moi_s35_circles phi b c)))` THEN
            ARITH_TAC;
            ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_TAC `a:real^3->bool`) THEN
          UNDISCH_TAC `components (moi_s35_circles phi b c) SUBSET {a:real^3->bool}` THEN
          UNDISCH_TAC `(k0:real^3->bool) IN components (moi_s35_circles phi b c)` THEN
          SET_TAC[];
          ALL_TAC] THEN
        MP_TAC(SPECL (moi_s5d_vars @ [`k0:real^3->bool`]) one) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
        MAP_EVERY EXISTS_TAC [`xb:real^3->bool`; `b:real^3->bool`] THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `{}:real^3->bool` THEN
        REWRITE_TAC[COMPACT_EMPTY; EMPTY_SUBSET; DISJOINT_EMPTY])
      THEN
      MAP_EVERY X_GEN_TAC
       [`xb1:real^3->bool`; `bn:real^3->bool`; `kk1:real^3->bool`] THEN
      STRIP_TAC THEN
      MP_TAC(SPEC `CARD (components (moi_s35_circles phi bn c))` ih) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `CARD (components (moi_s35_circles phi b c)) = n` THEN
        UNDISCH_TAC `CARD (components (moi_s35_circles phi bn c)) <
                     CARD (components (moi_s35_circles phi b c))` THEN
        ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL
       [`phi:real^3->real^3`; `xa:real^3->bool`; `xb1:real^3->bool`; `ww:real^3->bool`;
        `bn:real^3->bool`; `b0:real^3->bool`; `b1:real^3->bool`; `c:real`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `xb2:real^3->bool` (X_CHOOSE_THEN `b2:real^3->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `kk2:real^3->bool` STRIP_ASSUME_TAC))))) THEN
      MAP_EVERY EXISTS_TAC [`xb2:real^3->bool`; `b2:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `kk1 UNION kk2:real^3->bool` THEN
      ASM_SIMP_TAC[COMPACT_UNION; UNION_SUBSET; DISJOINT_UNION; IMAGE_UNION] THEN
      UNDISCH_TAC `xb1 DIFF IMAGE (phi:real^3->real^3) kk1 = xb DIFF IMAGE phi kk1` THEN
      UNDISCH_TAC `xb2 DIFF IMAGE (phi:real^3->real^3) kk2 = xb1 DIFF IMAGE phi kk2` THEN
      SET_TAC[]);;

let MOI_S5D_REMOVAL_CORE = prove
 (mk_imp(list_mk_conj [rand MOI_S35_LEMMA1; MOI_S35_SINGLE_FROM_ONE;
                       rand MOI_S35_DISK_SWAP; rand MOI_S35_ANNULUS_SWAP],
         MOI_S35_REMOVAL),
  DISCH_THEN(fun hs ->
    let l1,r1 = CONJ_PAIR hs in
    let one,r2 = CONJ_PAIR r1 in
    let dsk,ann = CONJ_PAIR r2 in
    SUBGOAL_THEN moi_s5d_auxg
     (fun aux ->
        MAP_EVERY X_GEN_TAC moi_s5d_vars THEN DISCH_TAC THEN
        MP_TAC(SPECL (`CARD (components (moi_s35_circles phi b c))` :: moi_s5d_vars) aux) THEN
        ASM_REWRITE_TAC[]) THEN
    moi_s5d_aux_tac l1 one dsk ann));;

let MOI_S5D_REMOVAL =
  let hs = [`PL_SCHOENFLIES_3_STATEMENT`; `MOISE_273_STATEMENT (:3)`;
            MOI_S35_SLAB_PRODUCT; MOI_S35_LEMMA1; MOI_S35_SINGLE_FROM_ONE;
            MOI_S35_DISK_SWAP; MOI_S35_ANNULUS_SWAP] in
  let ths = map ASSUME hs in
  match ths with
    [hsch; h273; hslab; hl1; hone; hdisk; hann] ->
      let pre = CONJ hsch (CONJ hl1 hslab) in
      let th = MP MOI_S5D_REMOVAL_CORE
                 (CONJ (MP hl1 h273) (CONJ hone (CONJ (MP hdisk pre) (MP hann pre)))) in
      prove(mk_imp(list_mk_conj hs, MOI_S35_REMOVAL), STRIP_TAC THEN ACCEPT_TAC th)
  | _ -> failwith "MOI_S5D_REMOVAL";;

(hyp MOI_S5D_REMOVAL_CORE, hyp MOI_S5D_REMOVAL);;
(* MOI_S5D_351_FROM_CORES: the stage cores (charts, source, approximation,  *)
(* combination, final map) and the derived-neighbourhood term               *)
(* give 35.1 in tube form.  The open sets w v are pulled back by h to the   *)
(* relatively open g v containing the dual cells, so the charts are thin.   *)

let MOI_S5D_351_FROM_CORES = prove
 (mk_imp(list_mk_conj [MOI_FND_DERIVED_NBHD_BASIC; rand MOI_S35_CHARTS;
                       rand MOI_S35_SOURCE; rand MOI_S35_APPROX;
                       rand MOI_S35_COMBINE; rand MOI_S35_FINAL],
         `!u:N->bool. MOISE_351_STATEMENT u`),
  DISCH_THEN(fun hs ->
    let dnb,r1 = CONJ_PAIR hs in
    let ch,r2 = CONJ_PAIR r1 in
    let so,r3 = CONJ_PAIR r2 in
    let ap,r4 = CONJ_PAIR r3 in
    let cb,fi = CONJ_PAIR r4 in
    GEN_TAC THEN REWRITE_TAC[MOISE_351_STATEMENT; graph_approximable] THEN
    MAP_EVERY X_GEN_TAC
     [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h:real^N->real^3`] THEN
    STRIP_TAC THEN X_GEN_TAC `w:real^N->real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                  `\v:real^N. {x | x IN UNIONS t /\ (h:real^N->real^3) x IN w v}`] ch) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] dnb) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[graph_in_complex]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      SUBGOAL_THEN `IMAGE (h:real^N->real^3) (derived_dual_cell t l v) SUBSET w v`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[derived_dual_cell] THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `av:(real^N->bool)->real^N`
      (X_CHOOSE_THEN `bv:(real^N->bool)->real^N`
        (X_CHOOSE_TAC `psi:(real^N->bool)->real^3->real^N`))) THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                  `\v:real^N. {x | x IN UNIONS t /\ (h:real^N->real^3) x IN w v}`;
                  `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                  `psi:(real^N->bool)->real^3->real^N`] so) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                  `h:real^N->real^3`; `w:real^N->real^3->bool`;
                  `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                  `psi:(real^N->bool)->real^3->real^N`] ap) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `ff:real^N->real^N->real^3`
      (X_CHOOSE_THEN `xx:real^N->real^3->bool`
        (X_CHOOSE_TAC `cc:(real^N->bool)->real`))) THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                  `h:real^N->real^3`; `w:real^N->real^3->bool`;
                  `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                  `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                  `xx:real^N->real^3->bool`; `cc:(real^N->bool)->real`] cb) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `xx':real^N->real^3->bool`) THEN
    MP_TAC(SPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                  `h:real^N->real^3`; `w:real^N->real^3->bool`;
                  `\v:real^N. {x | x IN UNIONS t /\ (h:real^N->real^3) x IN w v}`;
                  `av:(real^N->bool)->real^N`; `bv:(real^N->bool)->real^N`;
                  `psi:(real^N->bool)->real^3->real^N`; `ff:real^N->real^N->real^3`;
                  `xx':real^N->real^3->bool`; `cc:(real^N->bool)->real`] fi) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN ACCEPT_TAC));;

(* MOI_S5D_PROD_351: the producer MOI_PROD_351 (pc_moi_core_stmt.ml) from   *)
(* the unit statements of this file and two foundation terms                *)
(* (MOI_FND_DERIVED_NBHD_BASIC, proved in pc_moi_fnd_dn;                    *)
(* MOI_FND_GRAPH_TUBE, unit fnd_tubea).  MOISE_305_STATEMENT and the cell   *)
(* assembly are not needed on this route.                                   *)

let MOI_S35_UNIT_TARGETS =
  [MOI_S35_TUBE_TRIPLE; MOI_S35_MARKER; MOI_S35_CELL_341; MOI_S35_FILL;
   MOI_S35_LOCAL_SIGN; MOI_S35_CLOSE_SIGN; MOI_S35_ONE_DISK_EXT;
   MOI_S35_TWO_DISK_EXT; MOI_S35_SLAB_PRODUCT; MOI_S35_CHARTS; MOI_S35_SOURCE;
   MOI_S35_APPROX; MOI_S35_LEMMA1; MOI_S35_SINGLE_FROM_ONE; MOI_S35_DISK_SWAP;
   MOI_S35_ANNULUS_SWAP; MOI_S35_COMBINE; MOI_S35_FINAL_CELLS; MOI_S35_FINAL];;

let MOI_S5D_PROD_351 = prove
 (mk_imp(list_mk_conj (MOI_FND_DERIVED_NBHD_BASIC :: MOI_FND_GRAPH_TUBE ::
                       MOI_S35_UNIT_TARGETS),
         MOI_PROD_351),
  DISCH_THEN(fun hs ->
    match CONJUNCTS hs with
      [dnb; gt; tri; mrk; c341; fil; lsg; csg; one_e; two_e; slb; chs; src; apx;
       l1; one1; dsk; ann; cmb; fcl; fin] ->
        GEN_TAC THEN DISCH_THEN(fun ins ->
          match CONJUNCTS ins with
            [h341; _; h273; hsch; _] ->
              let gtt = CONJ gt tri in
              let pre = CONJ hsch (CONJ l1 slb) in
              let rem = MP MOI_S5D_REMOVAL
                         (end_itlist CONJ [hsch; h273; slb; l1; one1; dsk; ann]) in
              let cores =
                end_itlist CONJ
                 [dnb; MP chs gtt; MP src gtt;
                  MP apx (end_itlist CONJ [h341; mrk; c341; fil; lsg; csg; gt; tri]);
                  MP cmb rem;
                  MP fin (end_itlist CONJ [gt; tri; fcl; one_e; two_e; lsg; hsch])] in
              ignore pre;
              ACCEPT_TAC (SPEC `u:N->bool` (MP MOI_S5D_351_FROM_CORES cores))
          | _ -> failwith "MOI_S5D_PROD_351: producer antecedent")
    | _ -> failwith "MOI_S5D_PROD_351: hypotheses"));;

(hyp MOI_S5D_351_FROM_CORES, hyp MOI_S5D_PROD_351, length MOI_S35_UNIT_TARGETS);;
(* ========================================================================= *)
(* 9. Sanity theorems: the model has the book's properties (pp.248-249),   *)
(* degenerate cases, and teeth tests.                                       *)
(* ========================================================================= *)

let MOI_S5D_N_LIFT = prove
 (`!c y. moi_s35_n (moi_s35_lift c y) = max (abs(y$1)) (abs(y$2))`,
  REWRITE_TAC[moi_s35_n; moi_s35_lift; VECTOR_3]);;

(* B_e lies in the open tube S_e, its ends miss T_e, T_e INTER Bd C'_w lies *)
(* in B_e, and the ends of B_e are its two boundary squares (p.249).        *)

let MOI_S5D_BANN_STUBE = prove
 (`moi_s35_bann SUBSET moi_s35_stube`,
  REWRITE_TAC[moi_s35_bann; moi_s35_stube; SUBSET; IN_ELIM_THM] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

let MOI_S5D_BANN_ENDS_OFF_TTUBE = prove
 (`DISJOINT (moi_s35_sq (&5 / &32) (--(&3) / &256) UNION
             moi_s35_sq (&11 / &32) (&3 / &256)) moi_s35_ttube`,
  REWRITE_TAC[moi_s35_sq; moi_s35_ttube; DISJOINT; EXTENSION; IN_INTER; IN_UNION;
              IN_ELIM_THM; NOT_IN_EMPTY] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S5D_TTUBE_TRACE_BANN = prove
 (`{x | x IN moi_s35_ttube /\ x$3 = (moi_s35_n x - &1 / &4) / &8} SUBSET moi_s35_bann`,
  REWRITE_TAC[moi_s35_bann; moi_s35_ttube; SUBSET; IN_ELIM_THM] THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

let MOI_S5D_BANN_ENDS = prove
 (`moi_s35_sq (&5 / &32) (--(&3) / &256) SUBSET moi_s35_bann /\
   moi_s35_sq (&11 / &32) (&3 / &256) SUBSET moi_s35_bann`,
  REWRITE_TAC[moi_s35_bann; moi_s35_sq; SUBSET; IN_ELIM_THM] THEN
  CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* In the source model the boundary of C'_w pierces the flat annulus in the *)
(* circle n = 1/4 (the book's J_e), the inner end of A_e lies above it      *)
(* (inside C'_w) and the outer end below (condition (4)), and the finger    *)
(* contains the axis near the midpoint (condition (6)).                     *)

let MOI_S5D_SOURCE_CROSSING = prove
 (`{x | x IN moi_s35_aflat (&0) /\ x$3 = (moi_s35_n x - &1 / &4) / &8} =
   moi_s35_sq (&1 / &4) (&0)`,
  REWRITE_TAC[moi_s35_aflat; moi_s35_sq; EXTENSION; IN_ELIM_THM] THEN
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

let MOI_S5D_SOURCE_ENDS_SIDES = prove
 (`(!x. x IN moi_s35_sq (&3 / &16) (&0) ==> (moi_s35_n x - &1 / &4) / &8 < x$3) /\
   (!x. x IN moi_s35_sq (&5 / &16) (&0) ==> x$3 < (moi_s35_n x - &1 / &4) / &8)`,
  REWRITE_TAC[moi_s35_sq; IN_ELIM_THM] THEN CONJ_TAC THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_S5D_FINGER_AXIS = prove
 (`!x. x IN moi_s35_cube /\ moi_s35_n x < &1 / &16 /\ --(&1 / &64) <= x$3
       ==> x IN moi_s35_bcell`,
  REWRITE_TAC[moi_s35_bcell; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

(* The interface level 1/8 of the B-side chart is clear of the tube S_e.     *)

let MOI_S5D_INTERFACE_OFF_STUBE = prove
 (`DISJOINT (moi_s35_level (&1 / &8)) moi_s35_stube`,
  REWRITE_TAC[moi_s35_level; moi_s35_stube; DISJOINT; EXTENSION; IN_INTER;
              IN_ELIM_THM; NOT_IN_EMPTY] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

(* Degenerate graphs: no edges, no charts needed, source cells are dual cells. *)

let MOI_S5D_CHARTS_NO_EDGES = prove
 (`!(t:(real^N->bool)->bool) g av bv psi. moi_s35_charts t {} g av bv psi`,
  REWRITE_TAC[moi_s35_charts; moi_s35_edge; NOT_IN_EMPTY]);;

let MOI_S5D_CSRC_NO_EDGES = prove
 (`!(t:(real^N->bool)->bool) av bv psi cc v.
     moi_s35_csrc t {} av bv psi cc v = derived_dual_cell t {} v`,
  REWRITE_TAC[moi_s35_csrc; moi_s35_edge; NOT_IN_EMPTY] THEN SET_TAC[]);;

(* Teeth: the nonemptiness hypothesis of MOI_S35_FILL is needed.           *)

let MOI_S5D_FILL_NEEDS_NONEMPTY = prove
 (`~(!(k:real^3->bool) w.
       compact k /\ connected ((:real^3) DIFF k) /\ open w /\ k SUBSET w
       ==> ?e. &0 < e /\
               !k'. compact k' /\ (!x. x IN k' ==> setdist({x},k) < e)
                    ==> k' UNION inside k' SUBSET w)`,
  DISCH_THEN(MP_TAC o SPECL [`{}:real^3->bool`; `{}:real^3->bool`]) THEN
  REWRITE_TAC[COMPACT_EMPTY; DIFF_EMPTY; CONNECTED_UNIV; OPEN_EMPTY; EMPTY_SUBSET;
              SETDIST_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{vec 0:real^3}`) THEN
  ASM_REWRITE_TAC[COMPACT_SING; IN_SING] THEN SET_TAC[]);;

(* Teeth: same orientation holds for the identity and fails against the    *)
(* point reflection (det = -1 in real^3).                                    *)

let MOI_S5D_LIN_AT_LINEAR = prove
 (`!(f:real^3->real^3) x. linear f ==> moi_s35_lin_at f x f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s35_lin_at] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LINEAR_SUB] THEN VECTOR_ARITH_TAC);;

let MOI_S5D_SAME_ORIENT_TEETH = prove
 (`~moi_s35_same_orient (\x:real^3. x) (:real^3) (\x. --x) (:real^3)`,
  REWRITE_TAC[moi_s35_same_orient; IN_UNIV; NOT_FORALL_THM; NOT_IMP] THEN
  MAP_EVERY EXISTS_TAC [`vec 0:real^3`; `vec 0:real^3`;
                        `\x:real^3. x`; `\x:real^3. --x`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5D_LIN_AT_LINEAR THEN REWRITE_TAC[LINEAR_ID];
    MATCH_MP_TAC MOI_S5D_LIN_AT_LINEAR THEN REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `matrix (\x:real^3. --x) = --(mat 1:real^3^3)` SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; matrix; LAMBDA_BETA; MATRIX_NEG_COMPONENT; MAT_COMPONENT;
             VECTOR_NEG_COMPONENT; BASIS_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MATRIX_ID; DET_NEG; DET_I; DIMINDEX_3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_S5D_THEOREMS =
  [MOI_S5D_REMOVAL_CORE; MOI_S5D_REMOVAL; MOI_S5D_351_FROM_CORES; MOI_S5D_PROD_351;
   MOI_S5D_N_LIFT; MOI_S5D_BANN_STUBE; MOI_S5D_BANN_ENDS_OFF_TTUBE;
   MOI_S5D_TTUBE_TRACE_BANN; MOI_S5D_BANN_ENDS; MOI_S5D_SOURCE_CROSSING;
   MOI_S5D_SOURCE_ENDS_SIDES; MOI_S5D_FINGER_AXIS; MOI_S5D_INTERFACE_OFF_STUBE;
   MOI_S5D_CHARTS_NO_EDGES; MOI_S5D_CSRC_NO_EDGES; MOI_S5D_FILL_NEEDS_NONEMPTY;
   MOI_S5D_LIN_AT_LINEAR; MOI_S5D_SAME_ORIENT_TEETH];;

map (fun th -> length (hyp th)) MOI_S5D_THEOREMS;;
length (axioms());;

