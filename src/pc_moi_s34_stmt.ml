(* ========================================================================= *)
(* pc_moi_s34_stmt: the statements of the Sec 34 extension MOI_PROD_34_EXT    *)
(* (Moise GTM 47, Sec 34, printed pp.239-246), split into units:              *)
(* definitions moi_s34_..., unit statements MOI_S34_..., glue theorems        *)
(* MOI_S4D_... and sanity theorems MOI_S4D_SAN_....  The closure              *)
(* MOI_S4D_PROD_34_EXT: the unit statements imply MOI_PROD_34_EXT of          *)
(* pc_moi_core_stmt.ml.  The unit files prove the unit statements and         *)
(* pc_moi_s34_status.ml assembles MOI_PROD_34_EXT.  The tube hypothesis of    *)
(* MOI_S34_EXT_BODY is needed (teeth theorem MOI_S4D_SAN_EXT_TEETH).          *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1 (MOISE_34_EXT): vocabulary.  Moise GTM 47, Sec 34,                 *)
(* printed pp.239-246.  Notation: tt, kk the subdivided complexes t', k' of  *)
(* MOISE_34_EXT_STATEMENT; l = skeleton 1 kk the graph; N = moi_s34_nb, the  *)
(* second derived neighbourhood; C_v = moi_s34_vb (vertex balls); D_g =     *)
(* moi_s34_sd (splitting disks of edges g); Bd N = moi_s34_bd; N_s =        *)
(* moi_s34_ft (face torus of a 2-simplex s).  Target objects carry ''.      *)
(* ========================================================================= *)

(* Embeddings (continuous and injective on s). *)

let moi_s34_emb = new_definition
 `moi_s34_emb (h:real^N->real^M) (s:real^N->bool) <=>
    h continuous_on s /\ (!x y. x IN s /\ y IN s /\ h x = h y ==> x = y)`;;

(* The simplices of dimension n of a complex. *)

let moi_s34_simp = new_definition
 `moi_s34_simp (kk:(real^N->bool)->bool) (n:int) =
    {s | s IN kk /\ aff_dim s = n}`;;

(* The tube N of the 1-skeleton of kk in tt and its pieces (p.239, p.223). *)

let moi_s34_nb = new_definition
 `moi_s34_nb (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) =
    derived_nbhd tt (skeleton 1 kk)`;;

let moi_s34_bd = new_definition
 `moi_s34_bd (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) =
    derived_frontier tt (skeleton 1 kk)`;;

let moi_s34_vb = new_definition
 `moi_s34_vb (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (v:real^N) =
    derived_dual_cell tt (skeleton 1 kk) v`;;

let moi_s34_sd = new_definition
 `moi_s34_sd (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (g:real^N->bool) =
    INTERS {moi_s34_vb tt kk v | v | v IN g /\ {v} IN kk}`;;

let moi_s34_ft = new_definition
 `moi_s34_ft (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (s:real^N->bool) =
    UNIONS {moi_s34_vb tt kk v | v | v IN s /\ {v} IN kk}`;;

(* The union of the closed stars in tt of the vertices of s. *)

let moi_s34_cstar = new_definition
 `moi_s34_cstar (tt:(real^N->bool)->bool) (s:real^N->bool) =
    UNIONS {q | q IN tt /\ ?v. v IN s /\ {v} IN tt /\ v IN q}`;;

(* ------------------------------------------------------------------------- *)
(* Stage SRC (p.239, first paragraphs): the structure of the subdivision    *)
(* and its fineness for h and ep.                                            *)
(* ------------------------------------------------------------------------- *)

let moi_s34_tube = new_definition
 `moi_s34_tube (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) <=>
    lf_simplicial_complex tt /\ simplicial_subcomplex kk tt /\
    combinatorial_manifold_with_boundary 3 kk /\
    graph_in_complex tt (skeleton 1 kk)`;;

let moi_s34_fine = new_definition
 `moi_s34_fine (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
               (h:real^N->real^3) (ep:real^N->real) <=>
    !s x y z. s IN kk /\ x IN s /\
              y IN moi_s34_cstar tt s /\ z IN moi_s34_cstar tt s
              ==> dist(h y,h z) < ep x / &4`;;

let moi_s34_src = new_definition
 `moi_s34_src (t:(real^N->bool)->bool) (k:(real^N->bool)->bool)
              (h:real^N->real^3) (ep:real^N->real) tt kk <=>
    moi_s34_tube tt kk /\ subdivides tt t /\ subdivides kk k /\
    moi_s34_fine tt kk h ep`;;

map (fun th -> type_of (lhs (snd (strip_forall (concl th)))))
  [moi_s34_emb; moi_s34_simp; moi_s34_nb; moi_s34_bd; moi_s34_vb; moi_s34_sd;
   moi_s34_ft; moi_s34_cstar; moi_s34_fine; moi_s34_src];;

(* ========================================================================= *)
(* Part 2: the stage predicates.                                             *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Stage FRAME (Lemmas 1-2, p.240; DG Section34GraphFrame and              *)
(* Section34CarrierControl).  f1 is the tube embedding obtained from        *)
(* graph_approximable for open sets chosen inside the carriers car q (one   *)
(* open set in real^3 for each nonempty simplex q of kk): car q contains    *)
(* h(q), the carriers are nested, small for ep, locally finite at their   *)
(* own points (not on all of h(tt): the image of a non-closed tt may      *)
(* accumulate at h(x) for some x in tt), the                             *)
(* vertex carriers avoid the images of simplices not containing the vertex *)
(* (Lemma 1 (2)-(3)), and the vertices outside a 3-simplex r lie in the     *)
(* unbounded component of the complement of the carriers of the proper      *)
(* faces of r (the obstacle of Lemma 5 (7), p.241, made a frame property).  *)
(* The triangle clauses are Lemma 1 (4) and Lemma 2 (30.8).                 *)
(* ------------------------------------------------------------------------- *)

let moi_s34_frame = new_definition
 `moi_s34_frame (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                (h:real^N->real^3) (ep:real^N->real) (f1:real^N->real^3)
                (car:(real^N->bool)->real^3->bool) <=>
   pl_map_on (moi_s34_nb tt kk) f1 /\
   (!x y. x IN moi_s34_nb tt kk /\ y IN moi_s34_nb tt kk /\ f1 x = f1 y ==> x = y) /\
   IMAGE h (UNIONS (skeleton 1 kk)) SUBSET interior (IMAGE f1 (moi_s34_nb tt kk)) /\
   IMAGE f1 (moi_s34_nb tt kk) DIFF interior (IMAGE f1 (moi_s34_nb tt kk)) =
   IMAGE f1 (moi_s34_bd tt kk) /\
   (!q. q IN kk /\ ~(q = {})
        ==> open (car q) /\ car q SUBSET IMAGE h (UNIONS tt) /\ IMAGE h q SUBSET car q) /\
   (!q q'. q IN kk /\ q' IN kk /\ ~(q = {}) /\ q SUBSET q' ==> car q SUBSET car q') /\
   (!v. {v} IN kk
        ==> IMAGE h (moi_s34_vb tt kk v) SUBSET car {v} /\
            IMAGE f1 (moi_s34_vb tt kk v) SUBSET car {v} /\
            pl_ball 3 (IMAGE f1 (moi_s34_vb tt kk v)) /\
            frontier (IMAGE f1 (moi_s34_vb tt kk v)) =
            IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
            UNIONS {IMAGE f1 (moi_s34_sd tt kk g) | g |
                    g IN moi_s34_simp kk (&1) /\ v IN g}) /\
   (!g. g IN moi_s34_simp kk (&1)
        ==> pl_cell_with_boundary 2 (IMAGE f1 (moi_s34_sd tt kk g))
              (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk))) /\
   (!v q. {v} IN kk /\ q IN kk /\ ~(v IN q) ==> DISJOINT (car {v}) (IMAGE h q)) /\
   (!s. s IN moi_s34_simp kk (&2)
        ==> pl_solid_torus (IMAGE f1 (moi_s34_ft tt kk s)) /\
            IMAGE h (relative_frontier s) SUBSET
            interior (IMAGE f1 (moi_s34_ft tt kk s)) /\
            loops_carried (IMAGE h (relative_frontier s))
                          (IMAGE f1 (moi_s34_ft tt kk s))) /\
   (!r w. r IN moi_s34_simp kk (&3) /\ {w} IN kk /\ ~(w IN r)
          ==> h w IN outside (UNIONS {car q | q | q IN kk /\ ~(q = {}) /\
                                                 q SUBSET r /\ ~(q = r)})) /\
   (!y. y IN UNIONS {car q | q | q IN kk /\ ~(q = {})}
        ==> ?u. open u /\ y IN u /\
                FINITE {q | q IN kk /\ ~(q = {}) /\ ~(car q INTER u = {})}) /\
   (!q x y z. q IN kk /\ x IN q /\ y IN car q /\ z IN car q
              ==> dist(y,z) < ep x / &2)`;;

(* ------------------------------------------------------------------------- *)
(* Face balls (Lemmas 3-5, pp.240-241; DG Section34FaceBallInvariants).     *)
(* The trace of a ball c on Bd N'' and the union of the rims of the         *)
(* splitting disks Bd D_g''.                                                 *)
(* ------------------------------------------------------------------------- *)

let moi_s34_trace = new_definition
 `moi_s34_trace (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                (f1:real^N->real^3) (c:real^3->bool) =
    frontier c INTER IMAGE f1 (moi_s34_bd tt kk)`;;

let moi_s34_rims = new_definition
 `moi_s34_rims (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
               (f1:real^N->real^3) =
    UNIONS {IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) | g |
            g IN moi_s34_simp kk (&1)}`;;

(* One-face conditions: Lemma 5 (1) (a neighbourhood of Bd s'), (8) (the    *)
(* boundary sphere in the carrier of s), (2), (3), (4), finiteness of the   *)
(* trace and of its crossings with the rims, and (6) (H_1 carried).         *)

let moi_s34_fb1 = new_definition
 `moi_s34_fb1 (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
              (h:real^N->real^3) (f1:real^N->real^3)
              (car:(real^N->bool)->real^3->bool) (s:real^N->bool) (c:real^3->bool) <=>
   pl_ball 3 c /\
   IMAGE h (relative_frontier s) SUBSET interior c /\
   frontier c SUBSET car s /\
   (!w. {w} IN kk /\ ~(w IN s) ==> DISJOINT c (IMAGE f1 (moi_s34_vb tt kk w))) /\
   (!x. x IN moi_s34_trace tt kk f1 c
        ==> pl_crossing_at (frontier c) (IMAGE f1 (moi_s34_bd tt kk)) x) /\
   (!g x. g IN moi_s34_simp kk (&1) /\
          x IN frontier c INTER IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
          ==> pl_curve_crossing_at (IMAGE f1 (moi_s34_bd tt kk))
                (moi_s34_trace tt kk f1 c)
                (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) x) /\
   FINITE (components (moi_s34_trace tt kk f1 c)) /\
   FINITE (frontier c INTER moi_s34_rims tt kk f1) /\
   carries_h1 (moi_s34_trace tt kk f1 c INTER IMAGE f1 (moi_s34_ft tt kk s))
              (IMAGE f1 (moi_s34_ft tt kk s))`;;

(* Two-face condition: Lemma 5 (5), different balls meet only in Int N''.  *)

let moi_s34_fb2 = new_definition
 `moi_s34_fb2 (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
              (f1:real^N->real^3) (s:real^N->bool) (s':real^N->bool)
              (c:real^3->bool) (c':real^3->bool) <=>
   ~(s = s') ==> c INTER c' SUBSET interior (IMAGE f1 (moi_s34_nb tt kk))`;;

let moi_s34_fbinv = new_definition
 `moi_s34_fbinv (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                (h:real^N->real^3) (f1:real^N->real^3)
                (car:(real^N->bool)->real^3->bool)
                (cb:(real^N->bool)->real^3->bool) <=>
   (!s. s IN moi_s34_simp kk (&2) ==> moi_s34_fb1 tt kk h f1 car s (cb s)) /\
   (!s s'. s IN moi_s34_simp kk (&2) /\ s' IN moi_s34_simp kk (&2)
           ==> moi_s34_fb2 tt kk f1 s s' (cb s) (cb s'))`;;

(* The per-face rank (DG section34FaceBallRank): trace components plus      *)
(* crossings with the rims; Operation 1 lowers the first without raising   *)
(* the second, Operation 2 lowers the second by 2 (p.242).                  *)

let moi_s34_rank = new_definition
 `moi_s34_rank (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
               (f1:real^N->real^3) (c:real^3->bool) =
    CARD (components (moi_s34_trace tt kk f1 c)) +
    CARD (frontier c INTER moi_s34_rims tt kk f1)`;;

(* Operation 1 (p.241), witness form: a PL disk d in A_v'' = Bd C_v''       *)
(* minus the splitting disks, meeting Bd C_s exactly in its rim j, with     *)
(* interior disjoint from the other face balls (DG Section34Compression).   *)

let moi_s34_op1w = new_definition
 `moi_s34_op1w (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
               (f1:real^N->real^3) (cb:(real^N->bool)->real^3->bool)
               (s:real^N->bool) (v:real^N) (d:real^3->bool) (j:real^3->bool) <=>
   {v} IN kk /\ pl_cell_with_boundary 2 d j /\
   d SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
   d INTER frontier (cb s) = j /\
   (!g. g IN moi_s34_simp kk (&1) ==> DISJOINT d (IMAGE f1 (moi_s34_sd tt kk g))) /\
   (!s'. s' IN moi_s34_simp kk (&2) /\ ~(s' = s) ==> DISJOINT (d DIFF j) (cb s'))`;;

let moi_s34_op1 = new_definition
 `moi_s34_op1 (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
              (f1:real^N->real^3) (cb:(real^N->bool)->real^3->bool) (s:real^N->bool) <=>
   ?v d j. moi_s34_op1w tt kk f1 cb s v d j`;;

(* Operation 2 (p.242, Figure 34.1): an arc a of Bd C_s in A_v'' with both  *)
(* ends on the rim of D_g'' and no other point on splitting disks, an arc   *)
(* a' of that rim with the same ends, bounding with a a disk d in A_v''     *)
(* whose interior misses every face-ball boundary (DG Section34BigonSlide). *)

let moi_s34_op2 = new_definition
 `moi_s34_op2 (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
              (f1:real^N->real^3) (cb:(real^N->bool)->real^3->bool) (s:real^N->bool) <=>
   ?v g a a' aa d j.
     {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
     pl_cell_with_boundary 1 a aa /\ a SUBSET frontier (cb s) /\
     a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
     aa SUBSET IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) /\
     a INTER moi_s34_rims tt kk f1 = aa /\
     pl_cell_with_boundary 1 a' aa /\
     a' SUBSET IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) /\
     a INTER a' = aa /\
     pl_cell_with_boundary 2 d j /\
     d SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
     j = a UNION a' /\
     (!s'. s' IN moi_s34_simp kk (&2) ==> DISJOINT (d DIFF j) (frontier (cb s')))`;;

(* Lemmas 9 and 10 (p.243): no trace component lies in one Bd C_v'' INTER  *)
(* Bd N'', and no arc of a trace in it returns to the rim it starts on.     *)

let moi_s34_l910 = new_definition
 `moi_s34_l910 (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
               (f1:real^N->real^3) (cb:(real^N->bool)->real^3->bool) <=>
   (!s v j. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
            j IN components (moi_s34_trace tt kk f1 (cb s))
            ==> ~(j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))) /\
   (!s v g a aa. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
                 pl_cell_with_boundary 1 a aa /\
                 a SUBSET moi_s34_trace tt kk f1 (cb s) /\
                 a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                 aa SUBSET IMAGE f1 (moi_s34_sd tt kk g) /\
                 a INTER moi_s34_rims tt kk f1 = aa
                 ==> F)`;;

(* Lemma 11 (p.244): every trace component is a PL circle crossing the rim  *)
(* of each edge of s exactly once (DG Section34Trace).                       *)

let moi_s34_traced = new_definition
 `moi_s34_traced (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                 (f1:real^N->real^3) (cb:(real^N->bool)->real^3->bool) <=>
   !s. s IN moi_s34_simp kk (&2)
       ==> ~(moi_s34_trace tt kk f1 (cb s) = {}) /\
           moi_s34_trace tt kk f1 (cb s) SUBSET IMAGE f1 (moi_s34_ft tt kk s) /\
           !j. j IN components (moi_s34_trace tt kk f1 (cb s))
               ==> pl_sphere 1 j /\
                   !g. g IN moi_s34_simp kk (&1) /\ g SUBSET s
                       ==> ?p. j INTER IMAGE f1 (moi_s34_sd tt kk g) = {p}`;;

(* ------------------------------------------------------------------------- *)
(* Target cells (pp.244-246).  Face disks dd s = D_s'' (irreducible disks in *)
(* Bd C_s with rim in Bd N''); tetra balls rr r = C''(r) bounded by the     *)
(* face disks of r and the patches X''(r,v) = rr r INTER C_v''.              *)
(* ------------------------------------------------------------------------- *)

let moi_s34_fdisk = new_definition
 `moi_s34_fdisk (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool)
                (dd:(real^N->bool)->real^3->bool) <=>
   (!s. s IN moi_s34_simp kk (&2)
        ==> pl_cell_with_boundary 2 (dd s) (dd s INTER IMAGE f1 (moi_s34_bd tt kk)) /\
            dd s INTER IMAGE f1 (moi_s34_nb tt kk) =
            dd s INTER IMAGE f1 (moi_s34_bd tt kk) /\
            dd s SUBSET car s /\
            (!w. {w} IN kk /\ ~(w IN s)
                 ==> DISJOINT (dd s) (IMAGE f1 (moi_s34_vb tt kk w))) /\
            (!v. {v} IN kk /\ v IN s
                 ==> pl_cell_with_boundary 1 (dd s INTER IMAGE f1 (moi_s34_vb tt kk v))
                       (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                                g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})) /\
            (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET s
                 ==> ?p. dd s INTER IMAGE f1 (moi_s34_sd tt kk g) = {p} /\
                         pl_curve_crossing_at (IMAGE f1 (moi_s34_bd tt kk))
                           (dd s INTER IMAGE f1 (moi_s34_bd tt kk))
                           (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) p)) /\
   (!s s'. s IN moi_s34_simp kk (&2) /\ s' IN moi_s34_simp kk (&2) /\ ~(s = s')
           ==> DISJOINT (dd s) (dd s'))`;;

let moi_s34_resid = new_definition
 `moi_s34_resid (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool)
                (dd:(real^N->bool)->real^3->bool) (rr:(real^N->bool)->real^3->bool) <=>
   (!r. r IN moi_s34_simp kk (&3)
        ==> pl_ball 3 (rr r) /\
            rr r SUBSET convex hull (car r) /\
            frontier (rr r) =
            UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r} UNION
            (rr r INTER IMAGE f1 (moi_s34_bd tt kk)) /\
            rr r INTER IMAGE f1 (moi_s34_nb tt kk) =
            rr r INTER IMAGE f1 (moi_s34_bd tt kk) /\
            (!v. {v} IN kk /\ v IN r
                 ==> pl_cell_with_boundary 2 (rr r INTER IMAGE f1 (moi_s34_vb tt kk v))
                       (UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                                s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
                        UNIONS {rr r INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                                g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r})) /\
            (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET r
                 ==> pl_cell_with_boundary 1 (rr r INTER IMAGE f1 (moi_s34_sd tt kk g))
                       (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                                s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})) /\
            (!w. {w} IN kk /\ ~(w IN r)
                 ==> DISJOINT (rr r) (IMAGE f1 (moi_s34_vb tt kk w))) /\
            (!s. s IN moi_s34_simp kk (&2) /\ ~(s SUBSET r) ==> DISJOINT (rr r) (dd s))) /\
   (!r r'. r IN moi_s34_simp kk (&3) /\ r' IN moi_s34_simp kk (&3) /\ ~(r = r')
           ==> rr r INTER rr r' =
               UNIONS {dd s | s | s IN moi_s34_simp kk (&2) /\ s SUBSET r /\ s SUBSET r'}) /\
   (!v. {v} IN kk /\ ~(v IN complex_boundary kk)
        ==> IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
            UNIONS {rr r | r | r IN moi_s34_simp kk (&3) /\ v IN r}) /\
   (!g. g IN moi_s34_simp kk (&1) /\ ~(g SUBSET complex_boundary kk)
        ==> IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) SUBSET
            UNIONS {rr r | r | r IN moi_s34_simp kk (&3) /\ g SUBSET r})`;;

(* Outer cells at boundary vertices and edges of kk (the 34.1 case; DG's    *)
(* compact-only outer labels, Section34CompactOuter files): the parts of A_v''   *)
(* and of the rims not covered by the tetra balls.                          *)

let moi_s34_opatch = new_definition
 `moi_s34_opatch (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                 (f1:real^N->real^3) (rr:(real^N->bool)->real^3->bool) (v:real^N) =
    closure (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF
             UNIONS {rr r | r | r IN moi_s34_simp kk (&3) /\ v IN r})`;;

let moi_s34_oarc = new_definition
 `moi_s34_oarc (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
               (f1:real^N->real^3) (rr:(real^N->bool)->real^3->bool) (g:real^N->bool) =
    closure (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
             UNIONS {rr r | r | r IN moi_s34_simp kk (&3) /\ g SUBSET r})`;;

let moi_s34_outer = new_definition
 `moi_s34_outer (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                (f1:real^N->real^3) (dd:(real^N->bool)->real^3->bool)
                (rr:(real^N->bool)->real^3->bool) <=>
   (!v. {v} IN kk /\ v IN complex_boundary kk
        ==> pl_cell_with_boundary 2 (moi_s34_opatch tt kk f1 rr v)
              (UNIONS {dd s INTER IMAGE f1 (moi_s34_vb tt kk v) | s |
                       s IN moi_s34_simp kk (&2) /\ v IN s /\
                       s SUBSET complex_boundary kk} UNION
               UNIONS {moi_s34_oarc tt kk f1 rr g | g |
                       g IN moi_s34_simp kk (&1) /\ v IN g /\
                       g SUBSET complex_boundary kk})) /\
   (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk
        ==> pl_cell_with_boundary 1 (moi_s34_oarc tt kk f1 rr g)
              (UNIONS {dd s INTER IMAGE f1 (moi_s34_sd tt kk g) | s |
                       s IN moi_s34_simp kk (&2) /\ g SUBSET s /\
                       s SUBSET complex_boundary kk}))`;;

(* ------------------------------------------------------------------------- *)
(* The source cells on kk UNION N  (stages (1)-(7), p.245; DG              *)
(* Section34CutFrame and Section34Label): vertex balls, splitting disks,    *)
(* face disks Cl(s - N), tetra balls Cl(r - N), patches X(r,v), face arcs,  *)
(* edge arcs, marked points, and the outer patches and outer arcs at the    *)
(* boundary of kk.  The cells are their own labels; faces are inclusions.  *)
(* ------------------------------------------------------------------------- *)

let moi_s34_scells = new_definition
 `moi_s34_scells (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) =
   {moi_s34_vb tt kk v | v | {v} IN kk} UNION
   {moi_s34_sd tt kk g | g | g IN moi_s34_simp kk (&1)} UNION
   {closure (s DIFF moi_s34_nb tt kk) | s | s IN moi_s34_simp kk (&2)} UNION
   {closure (r DIFF moi_s34_nb tt kk) | r | r IN moi_s34_simp kk (&3)} UNION
   {r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | r,v |
    r IN moi_s34_simp kk (&3) /\ v IN r /\ {v} IN kk} UNION
   {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s,v |
    s IN moi_s34_simp kk (&2) /\ v IN s /\ {v} IN kk} UNION
   {r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | r,g |
    r IN moi_s34_simp kk (&3) /\ g IN moi_s34_simp kk (&1) /\ g SUBSET r} UNION
   {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | s,g |
    s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\ g SUBSET s} UNION
   {closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk) | v |
    {v} IN kk /\ v IN complex_boundary kk} UNION
   {closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF UNIONS kk) | g |
    g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk}`;;

(* The dimension of a PL cell (unique by invariance of dimension). *)

let moi_s34_dim = new_definition
 `moi_s34_dim (l:real^N->bool) = @n. n <= 3 /\ ?b. pl_cell_with_boundary n l b`;;

(* The PL cell structure of the new source cells (the vertex balls and the  *)
(* splitting disks are MOI_FND_GRAPH_TUBE).                                  *)

let moi_s34_scell_facts = new_definition
 `moi_s34_scell_facts (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) <=>
   (!r. r IN moi_s34_simp kk (&3)
        ==> pl_cell_with_boundary 3 (closure (r DIFF moi_s34_nb tt kk))
              (UNIONS {closure (s DIFF moi_s34_nb tt kk) | s |
                       s IN moi_s34_simp kk (&2) /\ s SUBSET r} UNION
               (r INTER moi_s34_bd tt kk))) /\
   (!s. s IN moi_s34_simp kk (&2)
        ==> pl_cell_with_boundary 2 (closure (s DIFF moi_s34_nb tt kk))
                                    (s INTER moi_s34_bd tt kk)) /\
   (!r v. r IN moi_s34_simp kk (&3) /\ v IN r /\ {v} IN kk
          ==> pl_cell_with_boundary 2 (r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                (UNIONS {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
                         s IN moi_s34_simp kk (&2) /\ v IN s /\ s SUBSET r} UNION
                 UNIONS {r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | g |
                         g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET r})) /\
   (!s v. s IN moi_s34_simp kk (&2) /\ v IN s /\ {v} IN kk
          ==> pl_cell_with_boundary 1 (s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
                (UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | g |
                         g IN moi_s34_simp kk (&1) /\ v IN g /\ g SUBSET s})) /\
   (!r g. r IN moi_s34_simp kk (&3) /\ g IN moi_s34_simp kk (&1) /\ g SUBSET r
          ==> pl_cell_with_boundary 1 (r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
                (UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | s |
                         s IN moi_s34_simp kk (&2) /\ g SUBSET s /\ s SUBSET r})) /\
   (!s g. s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\ g SUBSET s
          ==> ?p. s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk = {p}) /\
   (!v. {v} IN kk /\ v IN complex_boundary kk
        ==> pl_cell_with_boundary 2
              (closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk))
              (UNIONS {s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk | s |
                       s IN moi_s34_simp kk (&2) /\ v IN s /\
                       s SUBSET complex_boundary kk} UNION
               UNIONS {closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF
                                UNIONS kk) | g |
                       g IN moi_s34_simp kk (&1) /\ v IN g /\
                       g SUBSET complex_boundary kk})) /\
   (!g. g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk
        ==> pl_cell_with_boundary 1
              (closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF UNIONS kk))
              (UNIONS {s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk | s |
                       s IN moi_s34_simp kk (&2) /\ g SUBSET s /\
                       s SUBSET complex_boundary kk}))`;;

(* The source cell diagram (input of MOISE_CELL_ASSEMBLY_ON, source side).  *)

let moi_s34_src_ok = new_definition
 `moi_s34_src_ok (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) <=>
   (!l. l IN moi_s34_scells tt kk
        ==> moi_s34_dim l <= 3 /\
            pl_cell_with_boundary (moi_s34_dim l) l
              (UNIONS {m | m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)})) /\
   (!l m. l IN moi_s34_scells tt kk /\ m IN moi_s34_scells tt kk /\
          m SUBSET l /\ ~(m = l)
          ==> moi_s34_dim m < moi_s34_dim l) /\
   (!l m. l IN moi_s34_scells tt kk /\ m IN moi_s34_scells tt kk
          ==> l INTER m =
              UNIONS {n | n IN moi_s34_scells tt kk /\ n SUBSET l /\ n SUBSET m}) /\
   (!x. x IN UNIONS (moi_s34_scells tt kk)
        ==> ?u. open u /\ x IN u /\
                FINITE {l | l IN moi_s34_scells tt kk /\ ~(l INTER u = {})}) /\
   UNIONS (moi_s34_scells tt kk) = UNIONS kk UNION moi_s34_nb tt kk`;;

(* The target of each source cell, by kind (DG section34Cell). *)

let moi_s34_tgt_rel = new_definition
 `moi_s34_tgt_rel (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                  (f1:real^N->real^3) (dd:(real^N->bool)->real^3->bool)
                  (rr:(real^N->bool)->real^3->bool) (l:real^N->bool) (y:real^3->bool) <=>
   (?v. {v} IN kk /\ l = moi_s34_vb tt kk v /\ y = IMAGE f1 (moi_s34_vb tt kk v)) \/
   (?g. g IN moi_s34_simp kk (&1) /\ l = moi_s34_sd tt kk g /\
        y = IMAGE f1 (moi_s34_sd tt kk g)) \/
   (?s. s IN moi_s34_simp kk (&2) /\ l = closure (s DIFF moi_s34_nb tt kk) /\
        y = dd s) \/
   (?r. r IN moi_s34_simp kk (&3) /\ l = closure (r DIFF moi_s34_nb tt kk) /\
        y = rr r) \/
   (?r v. r IN moi_s34_simp kk (&3) /\ v IN r /\ {v} IN kk /\
          l = r INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk /\
          y = rr r INTER IMAGE f1 (moi_s34_vb tt kk v)) \/
   (?s v. s IN moi_s34_simp kk (&2) /\ v IN s /\ {v} IN kk /\
          l = s INTER moi_s34_vb tt kk v INTER moi_s34_bd tt kk /\
          y = dd s INTER IMAGE f1 (moi_s34_vb tt kk v)) \/
   (?r g. r IN moi_s34_simp kk (&3) /\ g IN moi_s34_simp kk (&1) /\ g SUBSET r /\
          l = r INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk /\
          y = rr r INTER IMAGE f1 (moi_s34_sd tt kk g)) \/
   (?s g. s IN moi_s34_simp kk (&2) /\ g IN moi_s34_simp kk (&1) /\ g SUBSET s /\
          l = s INTER moi_s34_sd tt kk g INTER moi_s34_bd tt kk /\
          y = dd s INTER IMAGE f1 (moi_s34_sd tt kk g)) \/
   (?v. {v} IN kk /\ v IN complex_boundary kk /\
        l = closure ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) DIFF UNIONS kk) /\
        y = moi_s34_opatch tt kk f1 rr v) \/
   (?g. g IN moi_s34_simp kk (&1) /\ g SUBSET complex_boundary kk /\
        l = closure ((moi_s34_sd tt kk g INTER moi_s34_bd tt kk) DIFF UNIONS kk) /\
        y = moi_s34_oarc tt kk f1 rr g)`;;

let moi_s34_tgt = new_definition
 `moi_s34_tgt (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
              (f1:real^N->real^3) (dd:(real^N->bool)->real^3->bool)
              (rr:(real^N->bool)->real^3->bool) (l:real^N->bool) =
    @y. moi_s34_tgt_rel tt kk f1 dd rr l y`;;

(* The target cell diagram (input of MOISE_CELL_ASSEMBLY_ON, target side),  *)
(* with the face relation of the source (inclusion), and the carrier        *)
(* estimate that gives dist(f x,h x) < ep x (p.246).                          *)

let moi_s34_tgt_cells = new_definition
 `moi_s34_tgt_cells (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                    (b:(real^N->bool)->real^3->bool) <=>
   !l. l IN moi_s34_scells tt kk
       ==> pl_cell_with_boundary (moi_s34_dim l) (b l)
             (UNIONS {b m | m | m IN moi_s34_scells tt kk /\ m SUBSET l /\ ~(m = l)})`;;

let moi_s34_tgt_meets = new_definition
 `moi_s34_tgt_meets (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                    (h:real^N->real^3) (ep:real^N->real)
                    (b:(real^N->bool)->real^3->bool) <=>
   (!l m. l IN moi_s34_scells tt kk /\ m IN moi_s34_scells tt kk
          ==> b l INTER b m =
              UNIONS {b n | n | n IN moi_s34_scells tt kk /\ n SUBSET l /\ n SUBSET m}) /\
   (!y. y IN UNIONS {b l | l IN moi_s34_scells tt kk}
        ==> ?u. open u /\ y IN u /\
                FINITE {l | l IN moi_s34_scells tt kk /\ ~(b l INTER u = {})}) /\
   (!l x y z. l IN moi_s34_scells tt kk /\ x IN l /\ x IN UNIONS kk /\
              y IN IMAGE h l UNION b l /\ z IN IMAGE h l UNION b l
              ==> dist(y,z) < ep x)`;;

let moi_s34_tgt_ok = new_definition
 `moi_s34_tgt_ok (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                 (h:real^N->real^3) (ep:real^N->real)
                 (b:(real^N->bool)->real^3->bool) <=>
   moi_s34_tgt_cells tt kk b /\ moi_s34_tgt_meets tt kk h ep b`;;

(* ========================================================================= *)
(* Part 3: the unit statements MOI_S34_... (closed boolean terms; each      *)
(* unit proves one or two of them).  Where a unit uses another unit's       *)
(* statement or an input statement constant, its statement is an            *)
(* implication, so that every unit can be checked on its own.               *)
(* ========================================================================= *)

(* s34_fine (foundation, shared with 35.1): locally finite complexes have    *)
(* subdivisions finer than any relatively open cover, in the strong form    *)
(* that the union of the simplices meeting a closed vertex star lies in a  *)
(* member of the cover; the induced subdivision of a subcomplex.            *)

let MOI_S34_LF_FINE =
 `!(t:(real^N->bool)->bool) (k:(real^N->bool)->bool) (cv:(real^N->bool)->bool).
     lf_simplicial_complex t /\ simplicial_subcomplex k t /\
     (!w. w IN cv ==> open_in (subtopology euclidean (UNIONS t)) w) /\
     UNIONS t SUBSET UNIONS cv
     ==> ?t' k'. lf_simplicial_complex t' /\ subdivides t' t /\
                 simplicial_subcomplex k' t' /\ subdivides k' k /\
                 !v. {v} IN t'
                     ==> ?w. w IN cv /\
                             UNIONS {q | q IN t' /\
                                         ~(q INTER moi_s34_cstar t' {v} = {})}
                             SUBSET w`;;

(* s34_src (p.239): the subdivision of MOISE_34_EXT, fine for h and ep, with *)
(* k' a combinatorial 3-manifold with boundary whose vertices have PL       *)
(* 2-sphere links in t'.                                                     *)

let MOI_S34_SRC_BODY =
 `!(t:(real^N->bool)->bool) (k:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real).
     lf_simplicial_complex t /\ simplicial_subcomplex k t /\
     combinatorial_manifold_with_boundary 3 k /\
     (!v. {v} IN k ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     h continuous_on UNIONS t /\
     (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y) /\
     (lift o ep) continuous_on UNIONS k /\ (!x. x IN UNIONS k ==> &0 < ep x)
     ==> ?tt kk. moi_s34_src t k h ep tt kk`;;

let MOI_S34_SRC = mk_imp(MOI_S34_LF_FINE,MOI_S34_SRC_BODY);;

(* s34_scell_a, s34_scell_b (stages (1)-(7), p.245, source side): the new   *)
(* source cells are PL cells with the stated boundaries; with the vertex    *)
(* balls and splitting disks of MOI_FND_GRAPH_TUBE they form a cell diagram *)
(* on |kk| UNION N (DG Section34CutFrame, Section34SourceFaceOrder).         *)

let MOI_S34_SCELL_A =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool).
     moi_s34_tube tt kk ==> moi_s34_scell_facts tt kk`;;

let MOI_S34_SCELL_B =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool).
     moi_s34_tube tt kk /\ moi_s34_scell_facts tt kk ==> moi_s34_src_ok tt kk`;;

(* s34_shell (Lemma 2, p.240, domain part and the use of 30.8): a           *)
(* neighbourhood w0 of the face torus N_s, with h(w0) open, such that every *)
(* embedding f1 of N_s into h(w0) whose image has h(Bd s) in its interior   *)
(* makes h(Bd s) carry the loops of f1(N_s).  (Solid tori S_1 inside N_s     *)
(* with spine Bd s, S_2 = N_s plus an outer collar, toroidal shell between.) *)

let MOI_S34_SHELL_BODY =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3) s.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\ s IN moi_s34_simp kk (&2)
     ==> ?w0. w0 SUBSET UNIONS tt /\ moi_s34_ft tt kk s SUBSET w0 /\
              open (IMAGE h w0) /\
              !f1:real^N->real^3.
                moi_s34_emb f1 (moi_s34_ft tt kk s) /\
                IMAGE f1 (moi_s34_ft tt kk s) SUBSET IMAGE h w0 /\
                IMAGE h (relative_frontier s) SUBSET
                interior (IMAGE f1 (moi_s34_ft tt kk s))
                ==> loops_carried (IMAGE h (relative_frontier s))
                                  (IMAGE f1 (moi_s34_ft tt kk s))`;;

let MOI_S34_SHELL = mk_imp(`MOISE_308_STATEMENT`,MOI_S34_SHELL_BODY);;

(* s34_margin (Lemma 5 (7), p.241): the vertices outside a 3-simplex r lie  *)
(* in the unbounded component of the complement of a closed d-neighbourhood *)
(* of h(r UNION the vertex balls of r) (Borsuk separation: the union of the *)
(* closed vertex stars of r in the first derived subdivision is an AR).     *)

let MOI_S34_MARGIN =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3) r.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\ r IN moi_s34_simp kk (&3)
     ==> ?d. &0 < d /\
             !w. {w} IN kk /\ ~(w IN r)
                 ==> h w IN outside {y | ?x. x IN r UNION moi_s34_ft tt kk r /\
                                             dist(y,h x) <= d}`;;

(* s34_frame (Lemmas 1-2, p.240): carriers, the tube embedding f1 from      *)
(* graph_approximable, and the frame properties.                             *)

let MOI_S34_FRAME_BODY =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real).
     moi_s34_tube tt kk /\ moi_s34_fine tt kk h ep /\ moi_s34_emb h (UNIONS tt) /\
     (lift o ep) continuous_on UNIONS kk /\ (!x. x IN UNIONS kk ==> &0 < ep x) /\
     graph_approximable tt (skeleton 1 kk) h
     ==> ?f1 car. moi_s34_frame tt kk h ep f1 car`;;

let MOI_S34_FRAME =
  mk_imp(MOI_S34_SHELL_BODY,mk_imp(MOI_S34_MARGIN,MOI_S34_FRAME_BODY));;

(* s34_cellnb (Lemma 3, p.240): h(s) has arbitrarily small polyhedral 3-cell *)
(* neighbourhoods in general position with Bd N'' and the rims (30.5, then  *)
(* minor adjustments).                                                        *)

let MOI_S34_CELLNB_BODY =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool) s w0.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\
     s IN moi_s34_simp kk (&2) /\ open w0 /\ IMAGE h s SUBSET w0
     ==> ?c. pl_ball 3 c /\ IMAGE h s SUBSET interior c /\ c SUBSET w0 /\
             (!x. x IN moi_s34_trace tt kk f1 c
                  ==> pl_crossing_at (frontier c) (IMAGE f1 (moi_s34_bd tt kk)) x) /\
             (!g x. g IN moi_s34_simp kk (&1) /\
                    x IN frontier c INTER
                         IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)
                    ==> pl_curve_crossing_at (IMAGE f1 (moi_s34_bd tt kk))
                          (moi_s34_trace tt kk f1 c)
                          (IMAGE f1 (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)) x) /\
             FINITE (components (moi_s34_trace tt kk f1 c)) /\
             FINITE (frontier c INTER moi_s34_rims tt kk f1)`;;

let MOI_S34_CELLNB = mk_imp(`MOISE_305_STATEMENT`,MOI_S34_CELLNB_BODY);;

(* s34_h1 (Lemma 4, p.241): a small enough polyhedral 3-cell neighbourhood  *)
(* of h(s) in general position has trace on the face torus carrying H_1    *)
(* (the book's cycles Z^1, Z_1, Z_2; DG CellTraceFirstHomology by           *)
(* Mayer-Vietoris, here pc_top_mv).                                          *)

let MOI_S34_LEMMA4 =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool) s.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ s IN moi_s34_simp kk (&2)
     ==> ?w0. open w0 /\ IMAGE h s SUBSET w0 /\
              !c. pl_ball 3 c /\ IMAGE h s SUBSET interior c /\ c SUBSET w0 /\
                  (!x. x IN moi_s34_trace tt kk f1 c
                       ==> pl_crossing_at (frontier c)
                                          (IMAGE f1 (moi_s34_bd tt kk)) x) /\
                  FINITE (components (moi_s34_trace tt kk f1 c))
                  ==> carries_h1 (moi_s34_trace tt kk f1 c INTER
                                  IMAGE f1 (moi_s34_ft tt kk s))
                                 (IMAGE f1 (moi_s34_ft tt kk s))`;;

(* s34_fball (Lemma 5, p.241): an initial face-ball family. *)

let MOI_S34_FBALL_BODY =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool).
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car
     ==> ?cb. moi_s34_fbinv tt kk h f1 car cb`;;

let MOI_S34_FBALL =
  mk_imp(MOI_S34_CELLNB_BODY,mk_imp(MOI_S34_LEMMA4,MOI_S34_FBALL_BODY));;

(* s34_op1a, s34_op1b, s34_op2 (Operations 1-2 and Lemmas 6-7, pp.241-242;  *)
(* DG exists_section34Compression, of_subset and of_disjoint with clean and *)
(* unclean pockets, exists_section34BigonSlide): an available operation at  *)
(* face s gives a family with the invariants, changed only at s, of smaller *)
(* rank at s.  Op 1 is split by the side of the compressing disk.           *)

let MOI_S34_OP_HYP =
 `moi_s34_tube (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) /\
  moi_s34_emb (h:real^N->real^3) (UNIONS tt) /\
  moi_s34_frame tt kk h (ep:real^N->real) (f1:real^N->real^3)
                (car:(real^N->bool)->real^3->bool) /\
  moi_s34_fbinv tt kk h f1 car (cb:(real^N->bool)->real^3->bool) /\
  (s:real^N->bool) IN moi_s34_simp kk (&2)`;;

let MOI_S34_OP_CONCL =
 `?cb'. moi_s34_fbinv (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                      (h:real^N->real^3) (f1:real^N->real^3)
                      (car:(real^N->bool)->real^3->bool) cb' /\
        (!s'. ~(s' = s) ==> cb' s' = (cb:(real^N->bool)->real^3->bool) s') /\
        moi_s34_rank tt kk f1 (cb' s) < moi_s34_rank tt kk f1 (cb s)`;;

let MOI_S34_OP_VARS =
  [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
   `cb:(real^N->bool)->real^3->bool`; `s:real^N->bool`];;

let MOI_S34_OP1_IN =
  let hyp = list_mk_conj
    [MOI_S34_OP_HYP;
     `moi_s34_op1w (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                   (f1:real^N->real^3) (cb:(real^N->bool)->real^3->bool)
                   (s:real^N->bool) (v:real^N) (d:real^3->bool) (j:real^3->bool)`;
     `(d:real^3->bool) DIFF (j:real^3->bool) SUBSET
      interior ((cb:(real^N->bool)->real^3->bool) (s:real^N->bool))`] in
  mk_imp(`PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT`,
         list_mk_forall(MOI_S34_OP_VARS @
                        [`v:real^N`; `d:real^3->bool`; `j:real^3->bool`],
                        mk_imp(hyp,MOI_S34_OP_CONCL)));;

let MOI_S34_OP1_OUT =
  let hyp = list_mk_conj
    [MOI_S34_OP_HYP;
     `moi_s34_op1w (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                   (f1:real^N->real^3) (cb:(real^N->bool)->real^3->bool)
                   (s:real^N->bool) (v:real^N) (d:real^3->bool) (j:real^3->bool)`;
     `DISJOINT ((d:real^3->bool) DIFF (j:real^3->bool))
               ((cb:(real^N->bool)->real^3->bool) (s:real^N->bool))`] in
  mk_imp(`PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT`,
         list_mk_forall(MOI_S34_OP_VARS @
                        [`v:real^N`; `d:real^3->bool`; `j:real^3->bool`],
                        mk_imp(hyp,MOI_S34_OP_CONCL)));;

let MOI_S34_OP2 =
  let hyp = list_mk_conj
    [MOI_S34_OP_HYP;
     `moi_s34_op2 (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
                  (f1:real^N->real^3) (cb:(real^N->bool)->real^3->bool)
                  (s:real^N->bool)`] in
  mk_imp(`PL_SCHOENFLIES_3_STATEMENT /\ PL_SCHOENFLIES_3_AMBIENT_STATEMENT`,
         list_mk_forall(MOI_S34_OP_VARS,mk_imp(hyp,MOI_S34_OP_CONCL)));;

(* s34_l910 (Lemmas 9-10, p.243): with no operation available, no trace     *)
(* component lies in one A_v'' and no trace arc returns to its rim.  Uses   *)
(* the link condition of p.239, automatic for combinatorial 3-manifolds     *)
(* with boundary (every edge of a link lies in a triangle of the link).     *)

let MOI_S34_L910 =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool) cb.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     (!s. s IN moi_s34_simp kk (&2)
          ==> ~moi_s34_op1 tt kk f1 cb s /\ ~moi_s34_op2 tt kk f1 cb s)
     ==> moi_s34_l910 tt kk f1 cb`;;

(* s34_trace (Lemma 11, p.244, with 28.8 in the used form). *)

let MOI_S34_TRACE_BODY =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool) cb.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     moi_s34_l910 tt kk f1 cb
     ==> moi_s34_traced tt kk f1 cb`;;

let MOI_S34_TRACE = mk_imp(`MOISE_288_STATEMENT`,MOI_S34_TRACE_BODY);;

(* s34_fdisk (p.244): the target face disks D_s''. *)

let MOI_S34_FDISK =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool) cb.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb /\
     moi_s34_traced tt kk f1 cb
     ==> ?dd. moi_s34_fdisk tt kk f1 car dd`;;

(* s34_resid (pp.244-245): the target tetra balls C''(r) (W_i, X_i, Y_i,    *)
(* the unbounded component, PL Schoenflies; Lemma 5 (7) from the frame).    *)

let MOI_S34_RESID_BODY =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool) dd.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd
     ==> ?rr. moi_s34_resid tt kk f1 car dd rr`;;

let MOI_S34_RESID = mk_imp(`PL_SCHOENFLIES_3_STATEMENT`,MOI_S34_RESID_BODY);;

(* s34_outer (34.1 case): outer patches and outer arcs at the boundary. *)

let MOI_S34_OUTER =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool) dd rr.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fdisk tt kk f1 car dd /\
     moi_s34_resid tt kk f1 car dd rr
     ==> moi_s34_outer tt kk f1 dd rr`;;

(* s34_recog_a, s34_recog_b (stages (1)-(7) target side; DG                *)
(* section34TargetRecognition_of_tiling): the target family by kinds is a  *)
(* cell diagram with the face relation of the source, locally finite, and   *)
(* each target with the h-image of its source cell has diameter below ep.  *)

let MOI_S34_RECOG_HYP =
 `moi_s34_tube (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) /\
  moi_s34_emb (h:real^N->real^3) (UNIONS tt) /\
  moi_s34_frame tt kk h (ep:real^N->real) (f1:real^N->real^3)
                (car:(real^N->bool)->real^3->bool) /\
  moi_s34_fdisk tt kk f1 car (dd:(real^N->bool)->real^3->bool) /\
  moi_s34_resid tt kk f1 car dd (rr:(real^N->bool)->real^3->bool) /\
  moi_s34_outer tt kk f1 dd rr`;;

let MOI_S34_RECOG_VARS =
  [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
   `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
   `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`];;

let MOI_S34_RECOG_A =
  let c = `moi_s34_tgt_cells (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
             (moi_s34_tgt tt kk (f1:real^N->real^3)
                (dd:(real^N->bool)->real^3->bool) (rr:(real^N->bool)->real^3->bool))` in
  list_mk_forall(MOI_S34_RECOG_VARS,mk_imp(MOI_S34_RECOG_HYP,c));;

let MOI_S34_RECOG_B =
  let c = `moi_s34_tgt_meets (tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool)
             (h:real^N->real^3) (ep:real^N->real)
             (moi_s34_tgt tt kk (f1:real^N->real^3)
                (dd:(real^N->bool)->real^3->bool) (rr:(real^N->bool)->real^3->bool))` in
  list_mk_forall(MOI_S34_RECOG_VARS,mk_imp(MOI_S34_RECOG_HYP,c));;

(* s34_ext (p.246): the cell assembly gives the PL embedding of |kk| within *)
(* ep of h.  Labels are the source cells themselves (label type real^N->bool, *)
(* as in MOI_PROD_34_EXT), faces are inclusions.  The hypothesis              *)
(* moi_s34_tube tt kk is needed: without it kk may contain a junk set and     *)
(* UNIONS kk need not be locally polyhedral (MOI_S4D_SAN_EXT_TEETH below).    *)

let MOI_S34_EXT_BODY =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (b:(real^N->bool)->real^3->bool).
     moi_s34_tube tt kk /\ moi_s34_src_ok tt kk /\ moi_s34_tgt_ok tt kk h ep b
     ==> ?f. pl_map_on (UNIONS kk) f /\
             (!x y. x IN UNIONS kk /\ y IN UNIONS kk /\ f x = f y ==> x = y) /\
             !x. x IN UNIONS kk ==> dist(f x,h x) < ep x`;;

let MOI_S34_EXT =
  mk_forall(`u:N->bool`,
    mk_imp(`MOISE_CELL_ASSEMBLY_ON_STATEMENT (:real^N->bool) (u:N->bool)`,
           MOI_S34_EXT_BODY));;

(* All unit statements, in unit order. *)

let MOI_S34_UNIT_TARGETS =
  [MOI_S34_LF_FINE; MOI_S34_SRC; MOI_S34_SCELL_A; MOI_S34_SCELL_B;
   MOI_S34_SHELL; MOI_S34_MARGIN; MOI_S34_FRAME; MOI_S34_CELLNB;
   MOI_S34_LEMMA4; MOI_S34_FBALL; MOI_S34_OP1_IN; MOI_S34_OP1_OUT;
   MOI_S34_OP2; MOI_S34_L910; MOI_S34_TRACE; MOI_S34_FDISK; MOI_S34_RESID;
   MOI_S34_OUTER; MOI_S34_RECOG_A; MOI_S34_RECOG_B; MOI_S34_EXT];;

map (fun t -> type_of t = bool_ty && frees t = []) MOI_S34_UNIT_TARGETS;;

(* ========================================================================= *)
(* Part 4a: the termination argument (Lemma 8, p.242) in the                 *)
(* locally finite form of DG (TerminalFaceBalls.lean:30): configurations     *)
(* g with one-point and two-point invariants, a rank per index depending   *)
(* only on the value at that index, and operations that lower the rank at   *)
(* one index changing nothing else; Zorn's lemma (ZL, Library/wo.ml) gives  *)
(* a configuration admitting no operation.                                   *)
(* ========================================================================= *)

let moi_s34_zinv = new_definition
 `moi_s34_zinv (ix:A->bool) (p1:A->B->bool) (p2:A->A->B->B->bool) (g:A->B) <=>
    (!i. i IN ix ==> p1 i (g i)) /\
    (!i j. i IN ix /\ j IN ix ==> p2 i j (g i) (g j))`;;

let moi_s34_zle = new_definition
 `moi_s34_zle (ix:A->bool) (p1:A->B->bool) (p2:A->A->B->B->bool)
              (rk:A->B->num) (g:A->B) (g':A->B) <=>
    moi_s34_zinv ix p1 p2 g /\ moi_s34_zinv ix p1 p2 g' /\
    (!i. ~(i IN ix) ==> g' i = g i) /\
    (!i. i IN ix ==> g' i = g i \/ rk i (g' i) < rk i (g i))`;;

let MOI_S4D_ZLE_POSET = prove
 (`!(ix:A->bool) (p1:A->B->bool) (p2:A->A->B->B->bool) (rk:A->B->num).
     poset (moi_s34_zle ix p1 p2 rk)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[poset; IN_FLD] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s34_zle] THEN MESON_TAC[];
    REWRITE_TAC[moi_s34_zle] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `i:A` THEN DISCH_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!i:A. i IN ix ==> (z:A->B) i = y i \/
                                   (rk:A->B->num) i (z i) < rk i (y i)` THEN
    DISCH_THEN(MP_TAC o SPEC `i:A`) THEN
    UNDISCH_TAC `!i:A. i IN ix ==> (y:A->B) i = x i \/
                                   (rk:A->B->num) i (y i) < rk i (x i)` THEN
    DISCH_THEN(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[LT_TRANS];
    REWRITE_TAC[moi_s34_zle] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:A` THEN
    ASM_CASES_TAC `(i:A) IN ix` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    UNDISCH_TAC `!i:A. i IN ix ==> (x:A->B) i = y i \/
                                   (rk:A->B->num) i (x i) < rk i (y i)` THEN
    DISCH_THEN(MP_TAC o SPEC `i:A`) THEN
    UNDISCH_TAC `!i:A. i IN ix ==> (y:A->B) i = x i \/
                                   (rk:A->B->num) i (y i) < rk i (x i)` THEN
    DISCH_THEN(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[LT_ANTISYM]]);;

(* Minimizers of the rank at each index along a nonempty chain. *)

let MOI_S4D_ZLE_MIN = prove
 (`!(P:(A->B)->bool) (rk:A->B->num) (a:A->B).
     P a ==> ?gm:A->A->B. !i. P (gm i) /\ !x. P x ==> rk i (gm i i) <= rk i (x i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:A` THEN
  MP_TAC(fst(EQ_IMP_RULE(BETA_RULE(ISPEC
    `\n. ?x:A->B. P x /\ (rk:A->B->num) i (x i) = n` num_WOP)))) THEN
  ANTS_TAC THENL [MAP_EVERY EXISTS_TAC [`(rk:A->B->num) i ((a:A->B) i)`; `a:A->B`] THEN
                  ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `m:A->B` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `m:A->B` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:A->B` THEN DISCH_TAC THEN REWRITE_TAC[GSYM NOT_LT] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(rk:A->B->num) i ((x:A->B) i)`) THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:A->B` THEN ASM_REWRITE_TAC[]);;

(* Chains have upper bounds: take at each index the value of a minimizer. *)

let MOI_S4D_ZLE_CHAIN = prove
 (`!(ix:A->bool) (p1:A->B->bool) (p2:A->A->B->B->bool) (rk:A->B->num) (g0:A->B).
     moi_s34_zinv ix p1 p2 g0
     ==> !P. chain (moi_s34_zle ix p1 p2 rk) P
             ==> ?y. fld (moi_s34_zle ix p1 p2 rk) y /\
                     !x. P x ==> moi_s34_zle ix p1 p2 rk x y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `P:(A->B)->bool` THEN
  REWRITE_TAC[chain; IN] THEN DISCH_THEN(LABEL_TAC "ch") THEN
  REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN
  ASM_CASES_TAC `?a:A->B. P a` THENL
   [ALL_TAC;
    EXISTS_TAC `g0:A->B` THEN CONJ_TAC THENL
     [EXISTS_TAC `g0:A->B` THEN ASM_REWRITE_TAC[moi_s34_zle];
      ASM_MESON_TAC[]]] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:A->B`) THEN
  SUBGOAL_THEN `!x:A->B. P x ==> moi_s34_zinv (ix:A->bool) (p1:A->B->bool)
                                   (p2:A->A->B->B->bool) x`
  (LABEL_TAC "pinv") THENL
   [X_GEN_TAC `x:A->B` THEN DISCH_TAC THEN
    USE_THEN "ch" (MP_TAC o SPECL [`x:A->B`; `x:A->B`]) THEN
    REWRITE_TAC[ASSUME `(P:(A->B)->bool) x`; moi_s34_zle] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`P:(A->B)->bool`; `rk:A->B->num`; `a:A->B`] MOI_S4D_ZLE_MIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `gm:A->A->B` (LABEL_TAC "gm")) THEN
  SUBGOAL_THEN
   `!x:A->B i. P x /\ i IN ix
               ==> x i = (gm:A->A->B) i i \/ (rk:A->B->num) i (gm i i) < rk i (x i)`
  (LABEL_TAC "cmp") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "gm" (MP_TAC o SPEC `i:A`) THEN STRIP_TAC THEN
    USE_THEN "ch" (MP_TAC o SPECL [`x:A->B`; `(gm:A->A->B) i`]) THEN
    REWRITE_TAC[ASSUME `(P:(A->B)->bool) x`;
                ASSUME `(P:(A->B)->bool) ((gm:A->A->B) i)`; moi_s34_zle] THEN
    DISCH_THEN(DISJ_CASES_THEN (MP_TAC o SPEC `i:A` o el 3 o CONJUNCTS)) THEN
    ASM_REWRITE_TAC[] THENL
     [DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(P:(A->B)->bool) x`)) THEN
      POP_ASSUM MP_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A->B y i. P x /\ P y /\ ~(i IN ix) ==> y i = x i`
  (LABEL_TAC "off") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "ch" (MP_TAC o SPECL [`x:A->B`; `y:A->B`]) THEN
    REWRITE_TAC[ASSUME `(P:(A->B)->bool) x`; ASSUME `(P:(A->B)->bool) y`;
                moi_s34_zle] THEN
    DISCH_THEN(DISJ_CASES_THEN (MP_TAC o SPEC `i:A` o el 2 o CONJUNCTS)) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `y = \i:A. if i IN ix then (gm:A->A->B) i i else (a:A->B) i` THEN
  SUBGOAL_THEN `moi_s34_zinv (ix:A->bool) (p1:A->B->bool) (p2:A->A->B->B->bool)
                             (y:A->B)`
  ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[moi_s34_zinv] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "gm" (MP_TAC o SPEC `i:A`) THEN STRIP_TAC THEN
      USE_THEN "pinv" (MP_TAC o C MATCH_MP
        (ASSUME `(P:(A->B)->bool) ((gm:A->A->B) i)`)) THEN
      REWRITE_TAC[moi_s34_zinv] THEN DISCH_THEN(MP_TAC o SPEC `i:A` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "gm" (MP_TAC o SPEC `i:A`) THEN STRIP_TAC THEN
      USE_THEN "gm" (MP_TAC o SPEC `j:A`) THEN STRIP_TAC THEN
      MP_TAC(MATCH_MP (ASSUME `!x:A->B. P x ==> (rk:A->B->num) i ((gm:A->A->B) i i) <=
                                                 rk i (x i)`)
                      (ASSUME `(P:(A->B)->bool) ((gm:A->A->B) j)`)) THEN
      MP_TAC(MATCH_MP (ASSUME `!x:A->B. P x ==> (rk:A->B->num) j ((gm:A->A->B) j j) <=
                                                 rk j (x j)`)
                      (ASSUME `(P:(A->B)->bool) ((gm:A->A->B) i)`)) THEN
      REPEAT DISCH_TAC THEN
      USE_THEN "ch" (MP_TAC o SPECL [`(gm:A->A->B) i`; `(gm:A->A->B) j`]) THEN
      REWRITE_TAC[ASSUME `(P:(A->B)->bool) ((gm:A->A->B) i)`;
                  ASSUME `(P:(A->B)->bool) ((gm:A->A->B) j)`; moi_s34_zle] THEN
      DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [SUBGOAL_THEN `(gm:A->A->B) j i = gm i i` (SUBST1_TAC o SYM) THENL
         [UNDISCH_TAC `!i':A. i' IN ix ==> (gm:A->A->B) j i' = gm i i' \/
                                           (rk:A->B->num) i' (gm j i') < rk i' (gm i i')` THEN
          DISCH_THEN(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[GSYM NOT_LE] THEN
          ASM_REWRITE_TAC[];
          UNDISCH_TAC `moi_s34_zinv (ix:A->bool) (p1:A->B->bool)
                         (p2:A->A->B->B->bool) ((gm:A->A->B) j)` THEN
          REWRITE_TAC[moi_s34_zinv] THEN
          DISCH_THEN(MP_TAC o SPECL [`i:A`; `j:A`] o CONJUNCT2) THEN
          ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(gm:A->A->B) i j = gm j j` (SUBST1_TAC o SYM) THENL
         [UNDISCH_TAC `!i':A. i' IN ix ==> (gm:A->A->B) i i' = gm j i' \/
                                           (rk:A->B->num) i' (gm i i') < rk i' (gm j i')` THEN
          DISCH_THEN(MP_TAC o SPEC `j:A`) THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN REWRITE_TAC[GSYM NOT_LE] THEN
          ASM_REWRITE_TAC[];
          UNDISCH_TAC `moi_s34_zinv (ix:A->bool) (p1:A->B->bool)
                         (p2:A->A->B->B->bool) ((gm:A->A->B) i)` THEN
          REWRITE_TAC[moi_s34_zinv] THEN
          DISCH_THEN(MP_TAC o SPECL [`i:A`; `j:A`] o CONJUNCT2) THEN
          ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  EXISTS_TAC `y:A->B` THEN
  SUBGOAL_THEN `!x:A->B. P x ==> moi_s34_zle (ix:A->bool) (p1:A->B->bool)
                                   (p2:A->A->B->B->bool) (rk:A->B->num) x y`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A->B` THEN DISCH_TAC THEN REWRITE_TAC[moi_s34_zle] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [USE_THEN "pinv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN X_GEN_TAC `i:A` THEN DISCH_TAC THENL
     [EXPAND_TAC "y" THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "off" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "y" THEN REWRITE_TAC[ASSUME `(i:A) IN ix`] THEN
      USE_THEN "cmp" (MP_TAC o SPECL [`x:A->B`; `i:A`]) THEN
      REWRITE_TAC[ASSUME `(i:A) IN ix`; ASSUME `(P:(A->B)->bool) x`] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:A->B` THEN DISJ2_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The abstract minimization: no operation is available at a maximal       *)
(* configuration.                                                             *)

let MOI_S4D_ZORN = prove
 (`!(ix:A->bool) (p1:A->B->bool) (p2:A->A->B->B->bool) (rk:A->B->num)
    (opr:(A->B)->A->bool) (g0:A->B).
     moi_s34_zinv ix p1 p2 g0 /\
     (!g i. moi_s34_zinv ix p1 p2 g /\ i IN ix /\ opr g i
            ==> ?g'. moi_s34_zinv ix p1 p2 g' /\
                     (!j. ~(j = i) ==> g' j = g j) /\
                     rk i (g' i) < rk i (g i))
     ==> ?g. moi_s34_zinv ix p1 p2 g /\ (!i. i IN ix ==> ~opr g i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `moi_s34_zle (ix:A->bool) (p1:A->B->bool) (p2:A->A->B->B->bool)
                            (rk:A->B->num)` ZL) THEN
  REWRITE_TAC[MOI_S4D_ZLE_POSET] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_S4D_ZLE_CHAIN THEN EXISTS_TAC `g0:A->B` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A->B` (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "max"))) THEN
  REWRITE_TAC[REWRITE_RULE[IN] IN_FLD] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:A->B`) THEN
  SUBGOAL_THEN `moi_s34_zinv (ix:A->bool) (p1:A->B->bool) (p2:A->A->B->B->bool)
                             (y:A->B)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THEN SIMP_TAC[moi_s34_zle];
    ALL_TAC] THEN
  EXISTS_TAC `y:A->B` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:A` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`y:A->B`; `i:A`] o
    check (fun th -> can (find_term (fun t -> t = `opr:(A->B)->A->bool`))
                    (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':A->B` STRIP_ASSUME_TAC) THEN
  USE_THEN "max" (MP_TAC o SPEC `g':A->B`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[moi_s34_zle] THEN CONJ_TAC THEN
    X_GEN_TAC `j:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j:A = i` THEN ASM_MESON_TAC[];
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[SYM th])) THEN
    ASM_MESON_TAC[LT_REFL]]);;

(* ========================================================================= *)
(* Part 4b: glue.  MOI_S4D_OP1_SIDE (the compressing disk of                *)
(* Operation 1 lies inside or outside the face ball), MOI_S4D_TERMINAL      *)
(* (Lemma 8: a face-ball family admitting no operation, by MOI_S4D_ZORN),   *)
(* and MOI_S4D_PROD_34_EXT (the unit statements imply the producer          *)
(* MOI_PROD_34_EXT of pc_moi_core_stmt.ml).                                  *)
(* ========================================================================= *)

let MOI_S4D_PL_BALL_COMPACT = prove
 (`!n (c:real^N->bool). pl_ball n c ==> compact c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check
    (fun th -> is_eq (concl th) && rand(concl th) = `c:real^N->bool`)) THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[POLYTOPE_IMP_COMPACT; SIMPLEX_IMP_POLYTOPE]);;

let MOI_S4D_PL_CELL_OPEN_CONNECTED = prove
 (`!n (d:real^N->bool) j. pl_cell_with_boundary n d j ==> connected (d DIFF j)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `relative_frontier (k:real^N->bool) = k DIFF relative_interior k`
  ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CLOSURE_CLOSED THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^N->bool) DIFF j = IMAGE (f:real^N->real^N) (relative_interior k)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^N`; `k:real^N->bool`;
                   `k DIFF relative_interior (k:real^N->bool)`] IMAGE_DIFF_INJ_ALT) THEN
    REWRITE_TAC[SUBSET_DIFF] THEN ANTS_TAC THENL
     [REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE] THEN EXISTS_TAC `g:real^N->real^N` THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `k DIFF (k DIFF relative_interior k) = relative_interior (k:real^N->bool)`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SUBSET];
    MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]]);;

(* The compressing disk of Operation 1 is inside or outside the face ball   *)
(* (the case split of DG's exists_section34Compression).                     *)

let MOI_S4D_OP1_SIDE = prove
 (`!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (f1:real^N->real^3)
    (cb:(real^N->bool)->real^3->bool) (s:real^N->bool) (v:real^N) d j.
     moi_s34_op1w tt kk f1 cb s v d j /\ pl_ball 3 (cb s)
     ==> d DIFF j SUBSET interior (cb s) \/ DISJOINT (d DIFF j) (cb s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s34_op1w] THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected ((d:real^3->bool) DIFF j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4D_PL_CELL_OPEN_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN `closed ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4D_PL_BALL_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier ((cb:(real^N->bool)->real^3->bool) s) =
                cb s DIFF interior (cb s)` ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `((d:real^3->bool) DIFF j) INTER
                frontier ((cb:(real^N->bool)->real^3->bool) s) = {}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `((d:real^3->bool) DIFF j) INTER
                 (cb:(real^N->bool)->real^3->bool) s = {}` THENL
   [DISJ2_TAC THEN ASM_REWRITE_TAC[DISJOINT]; DISJ1_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(d:real^3->bool) DIFF j`;
                 `interior((cb:(real^N->bool)->real^3->bool) s)`]
                CONNECTED_INTER_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `(cb:(real^N->bool)->real^3->bool) s` FRONTIER_INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;

let MOI_S4D_FBINV_ZINV = prove
 (`!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
    (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool)
    (cb:(real^N->bool)->real^3->bool).
     moi_s34_fbinv tt kk h f1 car cb <=>
     moi_s34_zinv (moi_s34_simp kk (&2)) (moi_s34_fb1 tt kk h f1 car)
                  (moi_s34_fb2 tt kk f1) cb`,
  REWRITE_TAC[moi_s34_fbinv; moi_s34_zinv]);;

(* Lemma 8 (p.242): a face-ball family admitting neither operation. *)

let MOI_S4D_TERMINAL_CONCL =
 `!(tt:(real^N->bool)->bool) (kk:(real^N->bool)->bool) (h:real^N->real^3)
   (ep:real^N->real) (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool) cb0.
     moi_s34_tube tt kk /\ moi_s34_emb h (UNIONS tt) /\
     moi_s34_frame tt kk h ep f1 car /\ moi_s34_fbinv tt kk h f1 car cb0
     ==> ?cb. moi_s34_fbinv tt kk h f1 car cb /\
              !s. s IN moi_s34_simp kk (&2)
                  ==> ~moi_s34_op1 tt kk f1 cb s /\ ~moi_s34_op2 tt kk f1 cb s`;;

let moi_s4d_has_const c tm =
  can (find_term (fun t -> try fst(dest_const t) = c with Failure _ -> false)) tm;;

let MOI_S4D_TERMINAL = prove
 (mk_imp(list_mk_conj [`PL_SCHOENFLIES_3_STATEMENT`;
                       `PL_SCHOENFLIES_3_AMBIENT_STATEMENT`;
                       MOI_S34_OP1_IN; MOI_S34_OP1_OUT; MOI_S34_OP2],
         MOI_S4D_TERMINAL_CONCL),
  DISCH_THEN(fun th ->
    match CONJUNCTS th with
      [s3;s3a;o1i;o1o;o2] ->
        let sch = CONJ s3 s3a in
        ASSUME_TAC(MP o1i sch) THEN ASSUME_TAC(MP o1o sch) THEN
        ASSUME_TAC(MP o2 sch)
    | _ -> failwith "MOI_S4D_TERMINAL: conjunct count") THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`moi_s34_simp (kk:(real^N->bool)->bool) (&2)`;
    `moi_s34_fb1 (tt:(real^N->bool)->bool) kk (h:real^N->real^3) (f1:real^N->real^3)
                 (car:(real^N->bool)->real^3->bool)`;
    `moi_s34_fb2 (tt:(real^N->bool)->bool) kk (f1:real^N->real^3)`;
    `\(s:real^N->bool) (c:real^3->bool).
       moi_s34_rank (tt:(real^N->bool)->bool) kk (f1:real^N->real^3) c`;
    `\(cb:(real^N->bool)->real^3->bool) (s:real^N->bool).
       moi_s34_op1 (tt:(real^N->bool)->bool) kk (f1:real^N->real^3) cb s \/
       moi_s34_op2 tt kk f1 cb s`;
    `cb0:(real^N->bool)->real^3->bool`] MOI_S4D_ZORN) THEN
  REWRITE_TAC[GSYM MOI_S4D_FBINV_ZINV; DE_MORGAN_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`g:(real^N->bool)->real^3->bool`; `i:real^N->bool`] THEN
  STRIP_TAC THENL
   [POP_ASSUM(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `d:real^3->bool`
      (X_CHOOSE_TAC `j:real^3->bool`)) o REWRITE_RULE[moi_s34_op1]) THEN
    SUBGOAL_THEN `pl_ball 3 ((g:(real^N->bool)->real^3->bool) i)` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s34_fbinv (tt:(real^N->bool)->bool) kk (h:real^N->real^3)
                     (f1:real^N->real^3) (car:(real^N->bool)->real^3->bool)
                     (g:(real^N->bool)->real^3->bool)` THEN
      REWRITE_TAC[moi_s34_fbinv; moi_s34_fb1] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `f1:real^N->real^3`; `g:(real^N->bool)->real^3->bool`;
                   `i:real^N->bool`; `v:real^N`; `d:real^3->bool`; `j:real^3->bool`]
                  MOI_S4D_OP1_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL
        [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
         `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
         `g:(real^N->bool)->real^3->bool`; `i:real^N->bool`;
         `v:real^N`; `d:real^3->bool`; `j:real^3->bool`] o
        check (fun th -> moi_s4d_has_const "interior" (concl th) &&
                         moi_s4d_has_const "moi_s34_op1w" (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPECL
        [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
         `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
         `g:(real^N->bool)->real^3->bool`; `i:real^N->bool`;
         `v:real^N`; `d:real^3->bool`; `j:real^3->bool`] o
        check (fun th -> moi_s4d_has_const "DISJOINT" (concl th) &&
                         moi_s4d_has_const "moi_s34_op1w" (concl th))) THEN
      ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `h:real^N->real^3`;
       `ep:real^N->real`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
       `g:(real^N->bool)->real^3->bool`; `i:real^N->bool`] o
      check (fun th -> moi_s4d_has_const "moi_s34_op2" (concl th) &&
                       is_forall (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The closure: the unit statements imply MOI_PROD_34_EXT.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4D_SUBDIVIDES_UNIONS = prove
 (`!(c:(real^N->bool)->bool) c'. subdivides c' c ==> UNIONS c' = UNIONS c`,
  SIMP_TAC[subdivides]);;

let MOI_S4D_PROD_34_EXT = prove
 (mk_imp(list_mk_conj MOI_S34_UNIT_TARGETS, MOI_PROD_34_EXT),
  DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    let get t = find (fun th -> concl th = t) ths in
    let lff = get MOI_S34_LF_FINE in
    let srcb = MP (get MOI_S34_SRC) lff in
    let mar = get MOI_S34_MARGIN in
    let l4 = get MOI_S34_LEMMA4 in
    MAP_EVERY ASSUME_TAC
      [srcb; mar; l4; get MOI_S34_SHELL; get MOI_S34_FRAME; get MOI_S34_CELLNB;
       get MOI_S34_FBALL; get MOI_S34_OP1_IN; get MOI_S34_OP1_OUT; get MOI_S34_OP2;
       get MOI_S34_L910; get MOI_S34_TRACE; get MOI_S34_FDISK; get MOI_S34_RESID;
       get MOI_S34_OUTER; get MOI_S34_RECOG_A; get MOI_S34_RECOG_B;
       get MOI_S34_SCELL_A; get MOI_S34_SCELL_B; get MOI_S34_EXT]) THEN
  X_GEN_TAC `u:N->bool` THEN STRIP_TAC THEN
  (* discharge the antecedents of the unit statements *)
  SUBGOAL_THEN MOI_S34_SHELL_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S34_SHELL)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S34_FRAME_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = MOI_S34_FRAME)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S34_CELLNB_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S34_CELLNB)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S34_FBALL_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = MOI_S34_FBALL)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN ACCEPT_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S34_TRACE_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S34_TRACE)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S34_RESID_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S34_RESID)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S34_EXT_BODY ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:N->bool` o
      check (fun th -> concl th = MOI_S34_EXT)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN MOI_S4D_TERMINAL_CONCL ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4D_TERMINAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the main chain *)
  REWRITE_TAC[MOISE_34_EXT_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`t:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `e:real^N->real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                                `h:real^N->real^3`; `e:real^N->real`] o
    check (fun th -> concl th = MOI_S34_SRC_BODY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tt:(real^N->bool)->bool`
    (X_CHOOSE_THEN `kk:(real^N->bool)->bool` MP_TAC)) THEN
  REWRITE_TAC[moi_s34_src] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s34_tube] o
    check (fun th -> concl th = `moi_s34_tube (tt:(real^N->bool)->bool) kk`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `UNIONS (tt:(real^N->bool)->bool) = UNIONS t /\
                UNIONS (kk:(real^N->bool)->bool) = UNIONS k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4D_SUBDIVIDES_UNIONS THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_emb (h:real^N->real^3) (UNIONS (tt:(real^N->bool)->bool))`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[moi_s34_emb]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                                `h:real^N->real^3`; `e:real^N->real`] o
    check (fun th -> concl th = MOI_S34_FRAME_BODY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^N->real^3`
    (X_CHOOSE_TAC `car:(real^N->bool)->real^3->bool`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                                `h:real^N->real^3`; `e:real^N->real`;
                                `f1:real^N->real^3`;
                                `car:(real^N->bool)->real^3->bool`] o
    check (fun th -> concl th = MOI_S34_FBALL_BODY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `cb0:(real^N->bool)->real^3->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                                `h:real^N->real^3`; `e:real^N->real`;
                                `f1:real^N->real^3`;
                                `car:(real^N->bool)->real^3->bool`;
                                `cb0:(real^N->bool)->real^3->bool`] o
    check (fun th -> concl th = MOI_S4D_TERMINAL_CONCL)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cb:(real^N->bool)->real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s34_l910 (tt:(real^N->bool)->bool) kk (f1:real^N->real^3)
                             (cb:(real^N->bool)->real^3->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S34_L910)) THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `e:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_traced (tt:(real^N->bool)->bool) kk (f1:real^N->real^3)
                               (cb:(real^N->bool)->real^3->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S34_TRACE_BODY)) THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `e:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                                `h:real^N->real^3`; `e:real^N->real`;
                                `f1:real^N->real^3`;
                                `car:(real^N->bool)->real^3->bool`;
                                `cb:(real^N->bool)->real^3->bool`] o
    check (fun th -> concl th = MOI_S34_FDISK)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `dd:(real^N->bool)->real^3->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                                `h:real^N->real^3`; `e:real^N->real`;
                                `f1:real^N->real^3`;
                                `car:(real^N->bool)->real^3->bool`;
                                `dd:(real^N->bool)->real^3->bool`] o
    check (fun th -> concl th = MOI_S34_RESID_BODY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `rr:(real^N->bool)->real^3->bool`) THEN
  SUBGOAL_THEN `moi_s34_outer (tt:(real^N->bool)->bool) kk (f1:real^N->real^3)
                  (dd:(real^N->bool)->real^3->bool) (rr:(real^N->bool)->real^3->bool)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S34_OUTER)) THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `e:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_tgt_ok (tt:(real^N->bool)->bool) kk (h:real^N->real^3)
                  (e:real^N->real)
                  (moi_s34_tgt tt kk (f1:real^N->real^3)
                     (dd:(real^N->bool)->real^3->bool) (rr:(real^N->bool)->real^3->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_tgt_ok] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`tt:(real^N->bool)->bool`;
        `kk:(real^N->bool)->bool`; `h:real^N->real^3`; `e:real^N->real`;
        `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
        `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`] o
        check (fun th -> concl th = MOI_S34_RECOG_A));
      FIRST_X_ASSUM(MP_TAC o SPECL [`tt:(real^N->bool)->bool`;
        `kk:(real^N->bool)->bool`; `h:real^N->real^3`; `e:real^N->real`;
        `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
        `dd:(real^N->bool)->real^3->bool`; `rr:(real^N->bool)->real^3->bool`] o
        check (fun th -> concl th = MOI_S34_RECOG_B))] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s34_src_ok (tt:(real^N->bool)->bool) kk` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S34_SCELL_B)) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> concl th = MOI_S34_SCELL_A)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                                `h:real^N->real^3`; `e:real^N->real`;
                                `moi_s34_tgt tt kk (f1:real^N->real^3)
                                   (dd:(real^N->bool)->real^3->bool)
                                   (rr:(real^N->bool)->real^3->bool)`] o
    check (fun th -> concl th = MOI_S34_EXT_BODY)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^N->real^3` THEN ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* Part 5: sanity theorems (degenerate cases and small                      *)
(* checks of the new notions).                                               *)
(* ========================================================================= *)

(* The empty complex: no source cells, the source and target diagrams hold, *)
(* every frame condition holds, and the extension is trivial.               *)

let MOI_S4D_SAN_SIMP_EMPTY = prove
 (`!n. moi_s34_simp ({}:(real^N->bool)->bool) n = {}`,
  REWRITE_TAC[moi_s34_simp; NOT_IN_EMPTY; EMPTY_GSPEC]);;

let MOI_S4D_SAN_CB_EMPTY = prove
 (`complex_boundary ({}:(real^N->bool)->bool) = {}`,
  REWRITE_TAC[complex_boundary; NOT_IN_EMPTY; EMPTY_GSPEC; UNIONS_0]);;

let MOI_S4D_SAN_SCELLS_EMPTY = prove
 (`!tt:(real^N->bool)->bool. moi_s34_scells tt {} = {}`,
  REWRITE_TAC[moi_s34_scells; MOI_S4D_SAN_SIMP_EMPTY; MOI_S4D_SAN_CB_EMPTY;
              NOT_IN_EMPTY] THEN
  SET_TAC[]);;

let MOI_S4D_SAN_SKELETON_EMPTY = prove
 (`!n. skeleton n ({}:(real^N->bool)->bool) = {}`,
  REWRITE_TAC[skeleton; NOT_IN_EMPTY; EMPTY_GSPEC]);;

let MOI_S4D_SAN_NB_EMPTY = prove
 (`!tt:(real^N->bool)->bool. moi_s34_nb tt {} = {} /\ moi_s34_bd tt {} = {}`,
  REWRITE_TAC[moi_s34_nb; moi_s34_bd; MOI_S4D_SAN_SKELETON_EMPTY;
              MOI_CD_DERIVED_NBHD_EMPTY; derived_frontier; FRONTIER_OF_EMPTY]);;

let MOI_S4D_SAN_SRC_OK_EMPTY = prove
 (`!tt:(real^N->bool)->bool. moi_s34_src_ok tt {}`,
  REWRITE_TAC[moi_s34_src_ok; MOI_S4D_SAN_SCELLS_EMPTY; MOI_S4D_SAN_NB_EMPTY;
              NOT_IN_EMPTY; UNIONS_0; UNION_EMPTY]);;

let MOI_S4D_SAN_TGT_OK_EMPTY = prove
 (`!(tt:(real^N->bool)->bool) (h:real^N->real^3) ep b.
     moi_s34_tgt_ok tt {} h ep b`,
  REWRITE_TAC[moi_s34_tgt_ok; moi_s34_tgt_cells; moi_s34_tgt_meets;
              MOI_S4D_SAN_SCELLS_EMPTY; NOT_IN_EMPTY] THEN
  REWRITE_TAC[EMPTY_GSPEC; SET_RULE `{(b:(real^N->bool)->real^3->bool) l | l | F} = {}`;
              UNIONS_0; NOT_IN_EMPTY]);;

let MOI_S4D_SAN_FRAME_EMPTY = prove
 (`!(tt:(real^N->bool)->bool) (h:real^N->real^3) ep f1 car.
     moi_s34_frame tt {} h ep f1 car`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s34_frame; MOI_S4D_SAN_NB_EMPTY; MOI_S4D_SAN_SIMP_EMPTY;
              MOI_S4D_SAN_SKELETON_EMPTY; NOT_IN_EMPTY; UNIONS_0; IMAGE_CLAUSES;
              EMPTY_SUBSET; EMPTY_DIFF; pl_map_on; EMPTY_GSPEC; FINITE_EMPTY] THEN
  MESON_TAC[OPEN_UNIV; IN_UNIV]);;

let MOI_S4D_SAN_EXT_EMPTY = prove
 (`!(tt:(real^N->bool)->bool) (h:real^N->real^3) ep.
     ?f:real^N->real^3. pl_map_on (UNIONS {}) f /\
         (!x y. x IN UNIONS {} /\ y IN UNIONS {} /\ f x = f y ==> x = y) /\
         !x. x IN UNIONS {} ==> dist(f x,h x) < ep x`,
  REWRITE_TAC[UNIONS_0; NOT_IN_EMPTY; pl_map_on]);;

(* No 2-simplices: every face-ball family satisfies the invariants and the  *)
(* operations are vacuous.                                                   *)

let MOI_S4D_SAN_FBINV_NOTRI = prove
 (`!(tt:(real^N->bool)->bool) kk (h:real^N->real^3) f1 car cb.
     moi_s34_simp kk (&2) = {} ==> moi_s34_fbinv tt kk h f1 car cb`,
  SIMP_TAC[moi_s34_fbinv; NOT_IN_EMPTY]);;

(* The empty ball has rank 0; the trace of a ball lies in Bd N''. *)

let MOI_S4D_SAN_RANK_EMPTY = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3).
     moi_s34_rank tt kk f1 {} = 0`,
  REWRITE_TAC[moi_s34_rank; moi_s34_trace; FRONTIER_EMPTY; INTER_EMPTY] THEN
  REWRITE_TAC[COMPONENTS_EMPTY; CARD_CLAUSES; ADD_CLAUSES]);;

let MOI_S4D_SAN_TRACE_SUBSET = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) c.
     moi_s34_trace tt kk f1 c SUBSET frontier c /\
     moi_s34_trace tt kk f1 c SUBSET IMAGE f1 (moi_s34_bd tt kk)`,
  REWRITE_TAC[moi_s34_trace] THEN SET_TAC[]);;

(* The splitting disk of an edge with endpoints u and w is C_u INTER C_w. *)

let MOI_S4D_SAN_SD_EDGE = prove
 (`!(tt:(real^N->bool)->bool) kk g u w.
     {v | v IN g /\ {v} IN kk} = {u,w}
     ==> moi_s34_sd tt kk g = moi_s34_vb tt kk u INTER moi_s34_vb tt kk w`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_s34_sd] THEN
  SUBGOAL_THEN `{moi_s34_vb (tt:(real^N->bool)->bool) kk v | v | v IN g /\ {v} IN kk} =
                {moi_s34_vb tt kk u, moi_s34_vb tt kk w}`
  SUBST1_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    REWRITE_TAC[INTERS_2]]);;

(* Fineness and the empty complex. *)

let MOI_S4D_SAN_FINE_EMPTY = prove
 (`!(tt:(real^N->bool)->bool) (h:real^N->real^3) ep. moi_s34_fine tt {} h ep`,
  REWRITE_TAC[moi_s34_fine; NOT_IN_EMPTY]);;

(* MOI_S34_LF_FINE holds for the empty complex (t' and k' empty). *)

let MOI_S4D_SAN_LF_FINE_EMPTY = prove
 (`!(k:(real^N->bool)->bool) (cv:(real^N->bool)->bool).
     simplicial_subcomplex k {}
     ==> ?t' k'. lf_simplicial_complex t' /\ subdivides t' {} /\
                 simplicial_subcomplex k' t' /\ subdivides k' k /\
                 !v. {v} IN t'
                     ==> ?w. w IN cv /\
                             UNIONS {q | q IN t' /\
                                         ~(q INTER moi_s34_cstar t' {v} = {})}
                             SUBSET w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_subcomplex; SUBSET_EMPTY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`{}:(real^N->bool)->bool`; `{}:(real^N->bool)->bool`] THEN
  REWRITE_TAC[lf_simplicial_complex; subdivides; simplicial_subcomplex;
              NOT_IN_EMPTY; UNIONS_0; EMPTY_SUBSET]);;

(* The rank is the sum of the two counts of p.242 (a restatement for the    *)
(* units: Operation 1 lowers the first, Operation 2 the second).            *)

let MOI_S4D_SAN_RANK_LT = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) c c'.
     CARD (components (moi_s34_trace tt kk f1 c')) <
     CARD (components (moi_s34_trace tt kk f1 c)) /\
     CARD (frontier c' INTER moi_s34_rims tt kk f1) <=
     CARD (frontier c INTER moi_s34_rims tt kk f1) \/
     CARD (components (moi_s34_trace tt kk f1 c')) =
     CARD (components (moi_s34_trace tt kk f1 c)) /\
     CARD (frontier c' INTER moi_s34_rims tt kk f1) <
     CARD (frontier c INTER moi_s34_rims tt kk f1)
     ==> moi_s34_rank tt kk f1 c' < moi_s34_rank tt kk f1 c`,
  REWRITE_TAC[moi_s34_rank] THEN ARITH_TAC);;

(* The dimension of a PL cell is well defined (invariance of dimension for  *)
(* simplices: HOMEOMORPHIC_CONVEX_COMPACT_SETS_EQ); used by the assembly.   *)

let MOI_S4D_SAN_DIM_CELL = prove
 (`!n (l:real^N->bool) b. n <= 3 /\ pl_cell_with_boundary n l b ==> moi_s34_dim l = n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s34_dim] THEN
  SUBGOAL_THEN `!m b'. pl_cell_with_boundary m (l:real^N->bool) b' ==> m = n`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    UNDISCH_TAC `pl_cell_with_boundary n (l:real^N->bool) b` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    DISCH_THEN(X_CHOOSE_THEN `k':real^N->bool` (X_CHOOSE_THEN `f':real^N->real^N`
      (X_CHOOSE_THEN `g':real^N->real^N` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(k:real^N->bool) homeomorphic (k':real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN EXISTS_TAC `l:real^N->bool` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[];
        ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex (k:real^N->bool) /\ compact k /\
                  convex (k':real^N->bool) /\ compact k'`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; POLYTOPE_IMP_COMPACT; SIMPLEX_IMP_POLYTOPE];
      ALL_TAC] THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_CONVEX_COMPACT_SETS_EQ] THEN
    MP_TAC(ISPECL [`k:real^N->bool`; `&n:int`] AFF_DIM_SIMPLEX) THEN
    MP_TAC(ISPECL [`k':real^N->bool`; `&m:int`] AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `m:num` THEN EQ_TAC THENL
   [REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `b:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* Teeth for the tube hypothesis of MOI_S34_EXT_BODY: a junk element         *)
(* J = (r DIFF nb) UNION c added to kk0 keeps                                *)
(* the source cells, src_ok and tgt_ok, but UNIONS kk may stop being locally *)
(* polyhedral, so no PL map on it exists.                                    *)

let MOI_S4D_TTH_INVARIANT = prove
 (`!(tt:(real^N->bool)->bool) kk0 jj.
     aff_dim jj = &3
     ==> skeleton 1 (jj INSERT kk0) = skeleton 1 kk0 /\
         moi_s34_nb tt (jj INSERT kk0) = moi_s34_nb tt kk0 /\
         moi_s34_bd tt (jj INSERT kk0) = moi_s34_bd tt kk0 /\
         moi_s34_vb tt (jj INSERT kk0) = moi_s34_vb tt kk0 /\
         (!v. {v} IN jj INSERT kk0 <=> {v} IN kk0) /\
         moi_s34_sd tt (jj INSERT kk0) = moi_s34_sd tt kk0 /\
         moi_s34_simp (jj INSERT kk0) (&1) = moi_s34_simp kk0 (&1) /\
         moi_s34_simp (jj INSERT kk0) (&2) = moi_s34_simp kk0 (&2) /\
         moi_s34_simp (jj INSERT kk0) (&3) = jj INSERT moi_s34_simp kk0 (&3)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `skeleton 1 (jj INSERT kk0) = skeleton 1 (kk0:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[skeleton] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN
    ASM_CASES_TAC `s:real^N->bool = jj` THEN
    ASM_REWRITE_TAC[INT_ARITH `~(&3:int <= &1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. ~({v} = jj)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. {v} IN jj INSERT kk0 <=> {v} IN kk0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s34_nb; moi_s34_bd] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_s34_vb] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; moi_s34_sd; moi_s34_vb] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s34_simp] THEN
  REPEAT CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN
  ASM_CASES_TAC `s:real^N->bool = jj` THEN
  ASM_REWRITE_TAC[INT_ARITH `~(&3:int = &1) /\ ~(&3:int = &2)`]);;

let MOI_S4D_TTH_CB = prove
 (`!(kk0:(real^N->bool)->bool) jj.
     aff_dim jj = &3 /\ (!s. s IN kk0 /\ aff_dim s = &2 ==> ~(s SUBSET jj))
     ==> complex_boundary (jj INSERT kk0) = complex_boundary kk0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN kk0 /\ aff_dim s = &2
      ==> {r | r IN jj INSERT kk0 /\ aff_dim r = &3 /\ s SUBSET r} =
          {r | r IN kk0 /\ aff_dim r = &3 /\ s SUBSET r}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `r:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN
    ASM_CASES_TAC `r:real^N->bool = jj` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[complex_boundary] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `(s:real^N->bool) IN kk0 /\ aff_dim s = &2` THENL
   [ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[IN_INSERT];
    ASM_REWRITE_TAC[IN_INSERT] THEN
    ASM_CASES_TAC `s:real^N->bool = jj` THEN
    ASM_REWRITE_TAC[INT_ARITH `~(&3:int = &2)`] THEN ASM_MESON_TAC[]]);;

let MOI_S4D_TTH_FAM4 = prove
 (`!(nb:real^N->bool) s3 jj r.
     r IN s3 /\ jj DIFF nb = r DIFF nb
     ==> {closure (q DIFF nb) | q | q IN jj INSERT s3} =
         {closure (q DIFF nb) | q | q IN s3}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN ASM_MESON_TAC[]);;

let MOI_S4D_TTH_FAM5 = prove
 (`!(vb:real^N->real^N->bool) bd s3 (kk0:(real^N->bool)->bool) jj.
     (!v. {v} IN kk0 ==> ~(v IN jj))
     ==> {q INTER vb v INTER bd | q,v | q IN jj INSERT s3 /\ v IN q /\ {v} IN kk0} =
         {q INTER vb v INTER bd | q,v | q IN s3 /\ v IN q /\ {v} IN kk0}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN ASM_MESON_TAC[]);;

let MOI_S4D_TTH_FAM7 = prove
 (`!(sd:(real^N->bool)->real^N->bool) bd s1 s3 jj.
     (!g. g IN s1 ==> ~(g SUBSET jj))
     ==> {q INTER sd g INTER bd | q,g | q IN jj INSERT s3 /\ g IN s1 /\ g SUBSET q} =
         {q INTER sd g INTER bd | q,g | q IN s3 /\ g IN s1 /\ g SUBSET q}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN ASM_MESON_TAC[]);;

let MOI_S4D_TTH_DIFF = prove
 (`!(a:real^N->bool) bd u c.
     c INTER bd = {} ==> (a INTER bd) DIFF (u UNION c) = (a INTER bd) DIFF u`,
  SET_TAC[]);;

let MOI_S4D_TTH_SCELLS = prove
 (`!(tt:(real^N->bool)->bool) kk0 r c jj.
     r IN kk0 /\ aff_dim r = &3 /\
     (r DIFF moi_s34_nb tt kk0) UNION c = jj /\ aff_dim jj = &3 /\
     c SUBSET moi_s34_nb tt kk0 /\ c INTER moi_s34_bd tt kk0 = {} /\
     (!v. {v} IN kk0 ==> ~(v IN jj)) /\
     (!s. s IN kk0 /\ (aff_dim s = &1 \/ aff_dim s = &2) ==> ~(s SUBSET jj))
     ==> UNIONS (jj INSERT kk0) = UNIONS kk0 UNION c /\
         moi_s34_nb tt (jj INSERT kk0) = moi_s34_nb tt kk0 /\
         moi_s34_scells tt (jj INSERT kk0) = moi_s34_scells tt kk0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk0:(real^N->bool)->bool`;
                 `jj:real^N->bool`] MOI_S4D_TTH_INVARIANT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kk0:(real^N->bool)->bool`; `jj:real^N->bool`] MOI_S4D_TTH_CB) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `UNIONS (jj INSERT kk0) = UNIONS kk0 UNION (c:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_INSERT] THEN
    UNDISCH_TAC `(r DIFF moi_s34_nb tt kk0) UNION c = (jj:real^N->bool)` THEN
    UNDISCH_TAC `(r:real^N->bool) IN kk0` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN moi_s34_simp (kk0:(real^N->bool)->bool) (&1) ==> ~(g SUBSET jj)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s34_scells] THEN
  MP_TAC(ISPECL [`moi_s34_nb (tt:(real^N->bool)->bool) kk0`;
                 `moi_s34_simp (kk0:(real^N->bool)->bool) (&3)`;
                 `jj:real^N->bool`; `r:real^N->bool`] MOI_S4D_TTH_FAM4) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM];
      UNDISCH_TAC `(r DIFF moi_s34_nb tt kk0) UNION c = (jj:real^N->bool)` THEN
      UNDISCH_TAC `(c:real^N->bool) SUBSET moi_s34_nb tt kk0` THEN SET_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[MOI_S4D_TTH_FAM5; MOI_S4D_TTH_FAM7; MOI_S4D_TTH_DIFF]);;

let MOI_S4D_SAN_EXT_TEETH = prove
 (`!(tt:(real^N->bool)->bool) kk0 (h:real^N->real^3) ep b r c jj.
     moi_s34_src_ok tt kk0 /\ moi_s34_tgt_ok tt kk0 h ep b /\
     r IN kk0 /\ aff_dim r = &3 /\
     (r DIFF moi_s34_nb tt kk0) UNION c = jj /\ aff_dim jj = &3 /\
     c SUBSET moi_s34_nb tt kk0 /\ c INTER moi_s34_bd tt kk0 = {} /\
     c INTER UNIONS kk0 = {} /\
     (!v. {v} IN kk0 ==> ~(v IN jj)) /\
     (!s. s IN kk0 /\ (aff_dim s = &1 \/ aff_dim s = &2) ==> ~(s SUBSET jj)) /\
     (!x. x IN c
          ==> ?d. !l y z. l IN moi_s34_scells tt kk0 /\ x IN l /\
                          y IN IMAGE h l UNION b l /\ z IN IMAGE h l UNION b l
                          ==> dist(y,z) < d) /\
     ~locally_polyhedral (UNIONS kk0 UNION c)
     ==> ?ep'. moi_s34_src_ok tt (jj INSERT kk0) /\
               moi_s34_tgt_ok tt (jj INSERT kk0) h ep' b /\
               ~(?f:real^N->real^3. pl_map_on (UNIONS (jj INSERT kk0)) f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk0:(real^N->bool)->bool`;
                 `r:real^N->bool`; `c:real^N->bool`; `jj:real^N->bool`]
    MOI_S4D_TTH_SCELLS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC
   `\x:real^N. if x IN c
              then (@d. !l y z. l IN moi_s34_scells tt kk0 /\ x IN l /\
                                y IN IMAGE (h:real^N->real^3) l UNION b l /\
                                z IN IMAGE h l UNION b l
                                ==> dist(y,z) < d)
              else ep x` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `moi_s34_src_ok (tt:(real^N->bool)->bool) kk0` THEN
    REWRITE_TAC[moi_s34_src_ok] THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:real^N->bool) SUBSET moi_s34_nb tt kk0` THEN SET_TAC[];
    UNDISCH_TAC `moi_s34_tgt_ok (tt:(real^N->bool)->bool) kk0 h ep b` THEN
    REWRITE_TAC[moi_s34_tgt_ok; moi_s34_tgt_cells; moi_s34_tgt_meets] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "old")))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`l:real^N->bool`; `x:real^N`; `y:real^3`; `z:real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC))) THEN
    BETA_TAC THEN DISCH_THEN(DISJ_CASES_TAC o REWRITE_RULE[IN_UNION]) THENL
     [SUBGOAL_THEN `~((x:real^N) IN c)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `(x:real^N) IN UNIONS kk0` THEN
        UNDISCH_TAC `(c:real^N->bool) INTER UNIONS kk0 = {}` THEN SET_TAC[];
        ALL_TAC] THEN
      USE_THEN "old" MATCH_MP_TAC THEN EXISTS_TAC `l:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `dist:real^3#real^3->real`)) (concl th) &&
      can (find_term (fun t -> t = `c:real^N->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `l:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^3`
      (MP_TAC o MATCH_MP PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL)) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4D_SANITY =
  [MOI_S4D_SAN_SIMP_EMPTY; MOI_S4D_SAN_CB_EMPTY; MOI_S4D_SAN_SCELLS_EMPTY;
   MOI_S4D_SAN_SKELETON_EMPTY; MOI_S4D_SAN_NB_EMPTY; MOI_S4D_SAN_SRC_OK_EMPTY;
   MOI_S4D_SAN_TGT_OK_EMPTY; MOI_S4D_SAN_FRAME_EMPTY; MOI_S4D_SAN_EXT_EMPTY;
   MOI_S4D_SAN_FBINV_NOTRI; MOI_S4D_SAN_RANK_EMPTY; MOI_S4D_SAN_TRACE_SUBSET;
   MOI_S4D_SAN_SD_EDGE; MOI_S4D_SAN_FINE_EMPTY; MOI_S4D_SAN_LF_FINE_EMPTY;
   MOI_S4D_SAN_RANK_LT; MOI_S4D_SAN_DIM_CELL; MOI_S4D_TTH_INVARIANT;
   MOI_S4D_TTH_CB; MOI_S4D_TTH_FAM4; MOI_S4D_TTH_FAM5; MOI_S4D_TTH_FAM7;
   MOI_S4D_TTH_DIFF; MOI_S4D_TTH_SCELLS; MOI_S4D_SAN_EXT_TEETH];;

map (fun th -> length (hyp th)) MOI_S4D_SANITY;;

(* ------------------------------------------------------------------------- *)
(* Final checks (printed): every glue and sanity theorem has no hypotheses, *)
(* the closure has exactly the unit statements as antecedent and the        *)
(* producer MOI_PROD_34_EXT as conclusion, and no axiom was added.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4D_THEOREMS =
  [MOI_S4D_ZLE_POSET; MOI_S4D_ZLE_MIN; MOI_S4D_ZLE_CHAIN; MOI_S4D_ZORN;
   MOI_S4D_PL_BALL_COMPACT; MOI_S4D_PL_CELL_OPEN_CONNECTED; MOI_S4D_OP1_SIDE;
   MOI_S4D_FBINV_ZINV; MOI_S4D_TERMINAL; MOI_S4D_SUBDIVIDES_UNIONS;
   MOI_S4D_PROD_34_EXT] @ MOI_S4D_SANITY;;

let MOI_S4D_CHECK =
  forall (fun th -> hyp th = []) MOI_S4D_THEOREMS &&
  concl MOI_S4D_PROD_34_EXT =
  mk_imp(list_mk_conj MOI_S34_UNIT_TARGETS, MOI_PROD_34_EXT) &&
  forall (fun t -> type_of t = bool_ty && frees t = []) MOI_S34_UNIT_TARGETS &&
  length (axioms()) = 3;;

(length MOI_S34_UNIT_TARGETS, length MOI_S4D_THEOREMS, MOI_S4D_CHECK);;

