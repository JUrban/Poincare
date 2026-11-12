(* ========================================================================= *)
(* pc_moi_s33_sorstmt: the statements of pc_moi_s33_sorient (parts O3 and   *)
(* O4 of the route of pc_moi_s33_match), the three terms                    *)
(* MOI_S3MT_SORIENT_DICHOT_TERM, MOI_S3MT_SORIENT_CONST_TERM and            *)
(* MOI_S3MT_SORIENT_DIR_TERM.  pc_moi_s33_match takes them as mk_imp        *)
(* antecedents under these names and discharges them by MP with the         *)
(* theorems of pc_moi_s33_sorient, which have exactly these conclusions (up *)
(* to alpha).  The charts are named G, G' (F is the constant false); DICHOT *)
(* names the reflected map r by an equation antecedent; DIR names its       *)
(* circle parametrization j, j' and the open sets U, U'.  The file loads    *)
(* Multivariate/cross.ml (with the interface saved and restored) and        *)
(* pc_moi_lt_sphere (for moi_lsp_tau; its closure has holed_disk_model,     *)
(* combinatorial_manifold, pl_homeomorphism, pl_sphere, std_triangle).      *)
(* POS i a b c (the side sign of a flat triangle is +1, the right side      *)
(* of MOI_FSD_SG_GLOBAL) and SIDEPRES i i' A f (f preserves POS on all      *)
(* non-degenerate triangles of A on which it is affine) are written out.    *)
(* ========================================================================= *)

let moi_s3mt_saved_interface = !the_interface;;
needs "Multivariate/cross.ml";;
the_interface := moi_s3mt_saved_interface;;
needs "src/pc_moi_lt_sphere.ml";;

(* O3 DICHOT: a PLH f between pieces of two sided surfaces is side-        *)
(* preserving, or r = f o G o (model reflection y to 4 - y) o G' is.  The   *)
(* reflection maps holed_disk_model k onto itself and each frontier circle *)
(* onto itself.                                                              *)

let MOI_S3MT_SORIENT_DICHOT_TERM =
 `!(s:real^3->bool) (i:real^3->bool) (s':real^3->bool) (i':real^3->bool) k
 (G:real^2->real^3) (G':real^3->real^2) (A:real^3->bool) (A':real^3->bool)
 (f:real^3->real^3) (f':real^3->real^3) (r:real^3->real^3).
   (?m. FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = s) /\
   (?m'. FINITE m' /\ combinatorial_manifold 2 m' /\ UNIONS m' = s') /\
   (?e. open i /\ open e /\ DISJOINT i e /\ i UNION e = (:real^3) DIFF s /\
         frontier i = s /\ frontier e = s) /\
   (?e'. open i' /\ open e' /\ DISJOINT i' e' /\ i' UNION e' = (:real^3) DIFF s' /\
         frontier i' = s' /\ frontier e' = s') /\
   A SUBSET s /\ A' SUBSET s' /\
   pl_homeomorphism (holed_disk_model k,A) (G,G') /\ pl_homeomorphism (A,A') (f,f') /\
   (!x. r x = f (G (vector[(G' x)$1; &4 - (G' x)$2])))
   ==> (!a b c. ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET A /\
                (!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
                         ==> f(u % a + v % b + w % c) = u % f a + v % f b + w % f c) /\
                ~collinear {f a,f b,f c}
                ==> ((?p d. p IN relative_interior(convex hull {f a,f b,f c}) /\ &0 < d /\
                           !z. z IN ball(p,d) /\ &0 < ((f b - f a) cross (f c - f a)) dot (z - p)
                               ==> z IN i') <=>
                     (?p d. p IN relative_interior(convex hull {a,b,c}) /\ &0 < d /\
                            !z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p)
                                ==> z IN i))) \/
       (!a b c. ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET A /\
                (!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
                         ==> r(u % a + v % b + w % c) = u % r a + v % r b + w % r c) /\
                ~collinear {r a,r b,r c}
                ==> ((?p d. p IN relative_interior(convex hull {r a,r b,r c}) /\ &0 < d /\
                           !z. z IN ball(p,d) /\ &0 < ((r b - r a) cross (r c - r a)) dot (z - p)
                               ==> z IN i') <=>
                     (?p d. p IN relative_interior(convex hull {a,b,c}) /\ &0 < d /\
                            !z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p)
                                ==> z IN i)))`;;

(* O3 CONST: side-preservation spreads from a nonempty open part: a PLH f  *)
(* of the piece A that agrees on U INTER A with a side-preserving PLH g is  *)
(* side-preserving.                                                          *)

let MOI_S3MT_SORIENT_CONST_TERM =
 `!(s:real^3->bool) (i:real^3->bool) (s':real^3->bool) (i':real^3->bool) k
 (G:real^2->real^3) (G':real^3->real^2) (A:real^3->bool) (A':real^3->bool)
 (f:real^3->real^3) (f':real^3->real^3) (g:real^3->real^3) (g':real^3->real^3)
 (U:real^3->bool).
   (?m. FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = s) /\
   (?m'. FINITE m' /\ combinatorial_manifold 2 m' /\ UNIONS m' = s') /\
   (?e. open i /\ open e /\ DISJOINT i e /\ i UNION e = (:real^3) DIFF s /\
         frontier i = s /\ frontier e = s) /\
   (?e'. open i' /\ open e' /\ DISJOINT i' e' /\ i' UNION e' = (:real^3) DIFF s' /\
         frontier i' = s' /\ frontier e' = s') /\
   A SUBSET s /\ A' SUBSET s' /\
   pl_homeomorphism (holed_disk_model k,A) (G,G') /\
   pl_homeomorphism (A,A') (f,f') /\ pl_homeomorphism (A,A') (g,g') /\
   (!a b c. ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET A /\
            (!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
                     ==> g(u % a + v % b + w % c) = u % g a + v % g b + w % g c) /\
            ~collinear {g a,g b,g c}
            ==> ((?p d. p IN relative_interior(convex hull {g a,g b,g c}) /\ &0 < d /\
                       !z. z IN ball(p,d) /\ &0 < ((g b - g a) cross (g c - g a)) dot (z - p)
                           ==> z IN i') <=>
                 (?p d. p IN relative_interior(convex hull {a,b,c}) /\ &0 < d /\
                        !z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p)
                            ==> z IN i))) /\
   open U /\ ~(U INTER A = {}) /\ (!x. x IN U INTER A ==> f x = g x)
   ==> (!a b c. ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET A /\
                (!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
                         ==> f(u % a + v % b + w % c) = u % f a + v % f b + w % f c) /\
                ~collinear {f a,f b,f c}
                ==> ((?p d. p IN relative_interior(convex hull {f a,f b,f c}) /\ &0 < d /\
                           !z. z IN ball(p,d) /\ &0 < ((f b - f a) cross (f c - f a)) dot (z - p)
                               ==> z IN i') <=>
                     (?p d. p IN relative_interior(convex hull {a,b,c}) /\ &0 < d /\
                            !z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p)
                                ==> z IN i)))`;;

(* O4 DIR: two side-preserving piece maps f1 (on A1) and f2 (on A2) that   *)
(* carry the common boundary circle J of A1, A2 onto the common circle J'   *)
(* of A1', A2' differ on J by an orientation-preserving circle map:          *)
(* j' o f2' o f1 o j preserves the cyclic order of rf std_triangle for some *)
(* PL parametrization j of J.                                                *)

let MOI_S3MT_SORIENT_DIR_TERM =
 `!(s:real^3->bool) (i:real^3->bool) (s':real^3->bool) (i':real^3->bool)
 (A1:real^3->bool) (A2:real^3->bool) (A1':real^3->bool) (A2':real^3->bool)
 (J:real^3->bool) (J':real^3->bool) k1 k2
 (G1:real^2->real^3) (G1':real^3->real^2) (G2:real^2->real^3) (G2':real^3->real^2)
 (f1:real^3->real^3) (f1':real^3->real^3) (f2:real^3->real^3) (f2':real^3->real^3).
   (?m. FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = s) /\
   (?m'. FINITE m' /\ combinatorial_manifold 2 m' /\ UNIONS m' = s') /\
   (?e. open i /\ open e /\ DISJOINT i e /\ i UNION e = (:real^3) DIFF s /\
         frontier i = s /\ frontier e = s) /\
   (?e'. open i' /\ open e' /\ DISJOINT i' e' /\ i' UNION e' = (:real^3) DIFF s' /\
         frontier i' = s' /\ frontier e' = s') /\
   A1 SUBSET s /\ A2 SUBSET s /\ A1' SUBSET s' /\ A2' SUBSET s' /\
   pl_homeomorphism (holed_disk_model k1,A1) (G1,G1') /\
   pl_homeomorphism (holed_disk_model k2,A2) (G2,G2') /\
   A1 INTER A2 = J /\ A1' INTER A2' = J' /\ pl_sphere 1 J /\
   J SUBSET IMAGE G1 (frontier (holed_disk_model k1)) /\
   J SUBSET IMAGE G2 (frontier (holed_disk_model k2)) /\
   (?U. open U /\ J SUBSET U /\ s INTER U SUBSET A1 UNION A2) /\
   (?U'. open U' /\ J' SUBSET U' /\ s' INTER U' SUBSET A1' UNION A2') /\
   pl_homeomorphism (A1,A1') (f1,f1') /\ pl_homeomorphism (A2,A2') (f2,f2') /\
   IMAGE f1 J = J' /\ IMAGE f2 J = J' /\
   (!a b c. ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET A1 /\
            (!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
                     ==> f1(u % a + v % b + w % c) = u % f1 a + v % f1 b + w % f1 c) /\
            ~collinear {f1 a,f1 b,f1 c}
            ==> ((?p d. p IN relative_interior(convex hull {f1 a,f1 b,f1 c}) /\ &0 < d /\
                       !z. z IN ball(p,d) /\ &0 < ((f1 b - f1 a) cross (f1 c - f1 a)) dot (z - p)
                           ==> z IN i') <=>
                 (?p d. p IN relative_interior(convex hull {a,b,c}) /\ &0 < d /\
                        !z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p)
                            ==> z IN i))) /\
   (!a b c. ~collinear {a,b,c} /\ convex hull {a,b,c} SUBSET A2 /\
            (!u v w. &0 <= u /\ &0 <= v /\ &0 <= w /\ u + v + w = &1
                     ==> f2(u % a + v % b + w % c) = u % f2 a + v % f2 b + w % f2 c) /\
            ~collinear {f2 a,f2 b,f2 c}
            ==> ((?p d. p IN relative_interior(convex hull {f2 a,f2 b,f2 c}) /\ &0 < d /\
                       !z. z IN ball(p,d) /\ &0 < ((f2 b - f2 a) cross (f2 c - f2 a)) dot (z - p)
                           ==> z IN i') <=>
                 (?p d. p IN relative_interior(convex hull {a,b,c}) /\ &0 < d /\
                        !z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p)
                            ==> z IN i)))
   ==> ?(j:real^2->real^3) (j':real^3->real^2).
         pl_homeomorphism (relative_frontier std_triangle,J) (j,j') /\
         (!a b c. a IN relative_frontier std_triangle /\ b IN relative_frontier std_triangle /\ c IN relative_frontier std_triangle /\
                 (moi_lsp_tau a < moi_lsp_tau b /\ moi_lsp_tau b < moi_lsp_tau c \/
                  moi_lsp_tau b < moi_lsp_tau c /\ moi_lsp_tau c < moi_lsp_tau a \/
                  moi_lsp_tau c < moi_lsp_tau a /\ moi_lsp_tau a < moi_lsp_tau b)
                 ==> (moi_lsp_tau ((j' o f2' o f1 o j) a) < moi_lsp_tau ((j' o f2' o f1 o j) b) /\ moi_lsp_tau ((j' o f2' o f1 o j) b) < moi_lsp_tau ((j' o f2' o f1 o j) c) \/
                      moi_lsp_tau ((j' o f2' o f1 o j) b) < moi_lsp_tau ((j' o f2' o f1 o j) c) /\ moi_lsp_tau ((j' o f2' o f1 o j) c) < moi_lsp_tau ((j' o f2' o f1 o j) a) \/
                      moi_lsp_tau ((j' o f2' o f1 o j) c) < moi_lsp_tau ((j' o f2' o f1 o j) a) /\ moi_lsp_tau ((j' o f2' o f1 o j) a) < moi_lsp_tau ((j' o f2' o f1 o j) b)))`;;

(* Check: the three statement terms are closed boolean terms.               *)

let MOI_S3MT_SORIENT_TERMS =
  [MOI_S3MT_SORIENT_DICHOT_TERM; MOI_S3MT_SORIENT_CONST_TERM; MOI_S3MT_SORIENT_DIR_TERM];;

let moi_s3mt_sorstmt_ok =
  forall (fun t -> type_of t = bool_ty && frees t = []) MOI_S3MT_SORIENT_TERMS;;

if not moi_s3mt_sorstmt_ok then failwith "moi_s3mt_sorstmt_ok";;

print_string ("SORSTMT " ^
   string_of_bool (moi_s3mt_sorstmt_ok) ^
   "\n");;

