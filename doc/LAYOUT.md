# Layout of src/

src/ holds the load closure of src/pc_poincare_top.ml: 1,090 files with 1,699,221 lines (wc -l). make.ml
loads them in dependency order. The files fall into families by name prefix. Below, the families are listed
roughly from the foundations to the headline theorems, then the Moise family is broken down by the sections
of Moise's book, and the last part gives the chain of the main theorems below POINCARE_TOP. File and line
counts are from wc -l on the files of src/.

Sources: MT = Morgan-Tian, Ricci Flow and the Poincare Conjecture (Clay Mathematics Monographs 3, 2007);
Moise = Moise, Geometric Topology in Dimensions 2 and 3 (GTM 47, 1977); CM = Colding-Minicozzi, Width and
finite extinction time of Ricci flow (Geom. Topol. 12, 2008). Section numbers c.s mean Chapter c, Section s
of MT. doc/results.tsv maps the numbered results of MT and Moise to HOL theorems.

## File families

| Prefix | Contents | Sources | Files | Lines |
|---|---|---|---|---|
| poincare_statement*, pc_interfaces.ml, pc_audit_sanity.ml | the headline statements (POINCARE_STATEMENT, POINCARE_SMOOTH_STATEMENT, POINCARE_EMBEDDED_STATEMENT) with their few definitions; MOISE_SMOOTHING_STATEMENT and POINCARE_FROM_SMOOTH_AND_MOISE; sanity theorems for the statements | MT Cor 0.2(a), p. x | 4 | 894 |
| ns_ | C^k and smooth calculus on real^N with a smooth inverse function theorem, smooth cutoff functions, and the definitions they rest on: copies, with unchanged code, of five files of the Navier-Stokes HOL Light development (github.com/hol-light-family/Navier_Stokes) | | 5 | 3,583 |
| pc_mfd_ | smooth manifolds as topologies with atlases: charts, transition maps, smooth maps, restriction, diffeomorphisms, vector fields and their flows, level sets, cutoffs, tubular neighbourhoods, the Whitney embedding, Riemannian metrics and their curvature on manifolds, existence of a Riemannian metric | Lee; MT Ch 1 | 22 | 20,398 |
| pc_lrg | local Riemannian geometry on open subsets of real^N: Christoffel symbols, curvature tensor and its symmetries, Ricci and scalar curvature, naturality under pullback, Laplacian, tensor norms and covariant derivatives, scaling, constant curvature, the evolution formulas under Ricci flow | MT Ch 1, Ch 3 | 11 | 16,391 |
| pc_ode_ | ordinary differential equations with parameters: local and global flows, continuity and C^k dependence on initial data | | 7 | 8,396 |
| pc_grg_ | lengths of curves, Riemannian distance and its continuity, volume and integration on manifolds, the area formula, the divergence theorem, isometries, integrals along a Ricci flow | Lee; MT Ch 1 | 10 | 13,179 |
| pc_geo_ | geodesics and the exponential map, covariant derivatives along curves, parallel transport, Jacobi fields, normal coordinates and the Gauss lemma, Hopf-Rinow, injectivity radius, local isometries, the round S^3, the Killing-Hopf theorem in dimension 3 | MT Secs 1.3-1.4, Thm 1.11 | 21 | 20,078 |
| pc_cmp_ | comparison geometry: Jacobi's theorem, conjugate radius, Hessian and Laplacian comparison by Calabi barriers, Bishop-Gromov, Gunther, Cheeger-Gromov-Taylor, second variation, Toponogov (global and local), critical points of distance functions, Busemann functions, splitting, the soul theorem for sec > 0 | MT Secs 1.5-1.6, Ch 2, Claim 3.24, Lemma 11.13; Petersen | 41 | 38,795 |
| pc_lim_, pc_lck_swap.ml | smooth closeness of metrics and geometric limits of manifolds and flows: distances, curvature and volume of limits, restriction | MT Ch 5 | 9 | 4,011 |
| pc_pde_ | parabolic PDE: linear parabolic systems on a torus model (energy estimates, the continuity method from the heat equation), Seeley extension, the Ricci-DeTurck flow and its gauge, short-time existence and maximal flows on compact manifolds | MT Sec 3.3, Prop 4.12; Chow-Lu-Ni; Evans | 30 | 62,540 |
| pc_rf_ | Ricci flows: definitions and examples, extension, gluing in time, metric equivalence, uniqueness on compact manifolds and for complete flows of bounded curvature (Kotschwar's energy method) | MT Ch 3 | 9 | 17,014 |
| pc_rfa_, pc_vshi.ml | Ricci flow analysis: evolution of curvature, weak and strong maximum principles for scalars and tensors, scalar curvature bounds, Shi's estimates, Hamilton-Ivey pinching, Hamilton's matrix and trace Harnack inequalities, Hamilton's pinching for ancient compact flows, variation of distance, curvature bounds for surgery histories and standard flows | MT Ch 3-4; Chow-Lu-Ni; Hamilton | 66 | 75,124 |
| pc_rfs_ | Ricci flows with surgery as finite histories (stages, slabs, cut-and-cap events, surgery parameters), the geometric vocabulary (necks, caps, C-components, pinching, normalized metrics), the top statements of the smooth proof and their assembly RFS_POINCARE_SMOOTH | MT Chs 14-15 | 9 | 6,292 |
| pc_p2a_ | L-length, L-geodesics, reduced length and reduced volume, the bound min l <= n/2, non-collapsing (Thm 8.1), reduced length of ancient solutions (Prop 9.9), the universal kappa0, zero asymptotic volume, compactness of kappa-solutions and their necks | MT Chs 6-8, Secs 9.1, 9.5-9.8 | 91 | 112,949 |
| pc_p2b_, pc_z2x_, pc_soul_, pc_canon_diam.ml | kappa-solutions: the asymptotic gradient shrinking soliton, splitting at infinity, classification of shrinkers, canonical neighbourhoods of kappa-solutions and their stability (Prop 9.79), bounded curvature at bounded distance (Thm 10.2), necks of positively curved complete 3-manifolds (Prop 2.19) | MT Prop 2.19, Ch 9, Ch 10 | 139 | 163,436 |
| pc_s2ent_ | Hamilton's entropy for ancient 2-dimensional flows on S^2 | MT Cor 9.50; Hamilton | 3 | 5,458 |
| pc_p2c_ | Cheeger-Gromov and Hamilton compactness, blow-up limits, local compactness of incomplete limits, the limit at a singular time, horns and strong necks deep in horns, the standard solution (existence, uniqueness, symmetry, asymptotics, canonical neighbourhoods) | MT Ch 5, Ch 11, Ch 12 | 79 | 117,678 |
| pc_top_ | algebraic topology: covering spaces and lifting, local homology and orientations, Mayer-Vietoris, Hurewicz in low degrees, general position, simply connected 3-manifolds have a degree-one map from S^3 | Hatcher, Algebraic Topology | 12 | 14,229 |
| pc_sch_ | the smooth Schoenflies theorem in R^3, by induction on the saddles of a generic height function | Hatcher, Notes on basic 3-manifold topology | 24 | 59,777 |
| pc_apx_ | the topology of 3-manifolds covered by necks and caps: the geometry of eps-necks, shortest curves, overlapping necks, chains and eps-tubes, regions covered by necks and caps, compact components, the topology of a surgery event | MT Appendix | 28 | 55,279 |
| pc_p3_, pc_p3e_, pc_pv411.ml | Ricci flow with surgery: the surgery cap metrics, the history invariant, gluing evolving necks, one surgery step, the flow extension, non-collapsing and canonical neighbourhoods through surgery, surgery times do not accumulate, the continuation form of Thm 15.9 and the chain P3_FULL_CHAIN_2; the volume part of Prop 4.11 | MT Prop 4.11, Chs 13-17 | 78 | 93,205 |
| pc_wan_, pc_an_beltrami.ml | weak analysis in dimension 2: Sobolev spaces W^(1,2), mollification, Poisson and Laplace problems and potentials on planar domains, Lipschitz maps; conformal parametrizations of metrics on S^2 by the Beltrami equation | Evans; Ahlfors; CM App. D | 30 | 57,121 |
| pc_hm_ | 2-dimensional harmonic maps: the Dirichlet problem, energy convexity, epsilon-regularity, removable singularities, the Hopf differential, regularity of energy minimizers | Morrey; Schoen-Uhlenbeck; Sacks-Uhlenbeck; CM | 19 | 30,365 |
| pc_cm_, pc_cmc_, pc_cmr_, pc_cmw_ | the Colding-Minicozzi width: sweepouts by 2-spheres in an embedded target, harmonic replacement, compactness of almost harmonic sequences, the existence of good sweepouts, Lemma 1.22 for harmonic spheres, the width | CM Secs 1-3, Apps. A-B | 37 | 66,430 |
| pc_p4_ | finite extinction for the simply connected case: pinch maps at surgery times, the width system and its comparison ODE across events, the elementary area facts, the Colding-Minicozzi inequality in integrated form | MT Prop 15.12, Ch 18; CM Thm 1.7 | 8 | 11,504 |
| pc_smt_ | smooth topology: Smale's theorem in radial form, the weak disc theorem, twisted spheres, sphere and ball gluing, separation of spheres in simply connected manifolds, orientability, the topology of a surgery event, listed pieces, sphere systems; and the top files of the smooth proof, pc_smt_extinct.ml (RFS_EXTINCTION) and pc_smt_smooth.ml (POINCARE_SMOOTH) | MT Prop 15.3, Cor 15.4; Lee; Milnor | 22 | 21,468 |
| pc_moi_ | Moise's theorem: compact topological 3-manifolds have smooth atlases (broken down below) | Moise | 275 | 603,594 |
| pc_poincare_top.ml | POINCARE_TOP and POINCARE_EMBEDDED | | 1 | 33 |
| total | | | 1,090 | 1,699,221 |

The statement constants that connect the families are in files named *_iface.ml, *_stmt*.ml, *_defs*.ml and
*_route*.ml (for example src/pc_p3_iface.ml for the results of MT Chs 3-12 used by the surgery chapters, and
src/pc_p3_route.ml for the inputs of P3_FULL_CHAIN_2).

## The Moise family

| Files | Contents | Moise | Files | Lines |
|---|---|---|---|---|
| pc_moi_stmt, pc_moi_core_stmt, pc_moi_s2628_stmt, pc_moi_assembly, pc_moi_chain, pc_moi_glue, pc_moi_glue2, pc_moi_cglue, pc_moi_core_status, pc_moi_status | statement constants of the chain, chart gluing and PL atlases, the assembly of the core MOI_CORE_STATUS and of MOI_SST_HEADLINE | Thms 35.2, 35.3, 36.1 | 10 | 6,097 |
| pc_moi_plmap, polytope, real, bary, tridef, ptri, cone, cone_sides, lfopen, comb, star, smb, pl1m, pl2, fnd1, tube3, cells | PL maps and polyhedra, realization of complexes in R^N, barycentric subdivision, triangulations of open sets and of compact PL 3-manifolds, cones, combinatorial manifolds, smooth manifolds with boundary, the polygonal Schoenflies theorem, assembly of cells into PL homeomorphisms | Secs 2-8, 23 | 17 | 22,883 |
| pc_moi_fnd_ | PL topology of 3-manifolds in R^3 and R^N: collars and bicollars, sides of surfaces, regular neighbourhoods, general position, simplicial approximation, Euler characteristic, GF(2) and integral H_1, tubes and handles, double covers | used in Secs 23-35 | 47 | 140,433 |
| pc_moi_sch3_ | Alexander's PL Schoenflies theorem in R^3 | Sec 17 | 16 | 40,906 |
| pc_moi_lt_, pc_moi_loop_ | the loop theorem by the tower of double covers | Sec 25 | 32 | 66,442 |
| pc_moi_s26_, pc_moi_s27 | bicollars and the extension of the loop theorem; the Dehn lemma consequence | Secs 26-27 | 11 | 12,582 |
| pc_moi_s28_, s286, s288_cov, s2810 | polygons in the boundary of a combinatorial solid torus | Sec 28 | 8 | 13,431 |
| pc_moi_s30_, s30sep, s308, p305, s3032_ | polyhedral interpolation theorems, and statement files for Secs 30-32 | Sec 30 | 20 | 20,602 |
| pc_moi_s31_ | canonical configurations | Sec 31 | 6 | 4,303 |
| pc_moi_s32_ | handle decompositions of tubes, pseudo-cells | Sec 32 | 15 | 29,686 |
| pc_moi_s33_ | PLH approximations on regular neighbourhoods of graphs in R^3 | Sec 33 | 24 | 55,202 |
| pc_moi_s34_ | PLH approximations for polyhedral 3-cells | Sec 34 | 35 | 78,180 |
| pc_moi_s35_ | PLH approximations on neighbourhoods of 1-dimensional polyhedra; the approximation theorem | Sec 35 | 24 | 71,104 |
| pc_moi_smo_, pc_moi_pd2_ | smoothing of finite combinatorial 3-manifolds by metric smoothing (regular-tetrahedron metrics, angular rescaling at edges, cones over smoothed vertex links) and the 2-dimensional results for the vertex links | not in Moise | 10 | 41,743 |
| total | | | 275 | 603,594 |

## The chain below POINCARE_TOP

Each theorem is proved from the ones indented below it.

- POINCARE_TOP (src/pc_poincare_top.ml): |- POINCARE_STATEMENT (:A), by POINCARE_FROM_SMOOTH_AND_MOISE (src/pc_interfaces.ml) from
  - POINCARE_SMOOTH (src/pc_smt_smooth.ml): |- POINCARE_SMOOTH_STATEMENT (:A), by RFS_POINCARE_SMOOTH (src/pc_rfs_assembly.ml) from seven theorems:
    - METRIC_EXISTENCE (src/pc_mfd_metric_exists.ml): every compact Hausdorff smooth manifold has a Riemannian metric, from the Whitney embedding MFD_EMBEDDING_EXISTS (src/pc_mfd_embed.ml);
    - RFS_EXTINCTION (src/pc_smt_extinct.ml): a controlled Ricci flow with surgery from a closed simply connected 3-manifold becomes extinct; it is P3_FULL_CHAIN_2 (src/pc_p3_route2.ml) at the limit carrier real^3, whose inputs are
      - P3_RFS_EXTINCTION (src/pc_p3_assembly.ml), with P3_THM_15_9_FROM_PARTS (MT Thm 15.9 from Props 16.1, 17.1, Lemma 15.11, the flow extension and Lemma 17.12) and RFS_EXTINCTION_FROM_P3;
      - the route theorems of MT Chs 13-17, e.g. P3_THM_13_2 (src/pc_p3_s13thm.ml), P3E_LEMMA_15_11_ROUTE (src/pc_p3e_15_11.ml), P3L_PROP_16_1_ROUTE (src/pc_p3_s161.ml), P3_PROP_17_1_ROUTE_2 (src/pc_p3_c171e.ml), P3_LEMMA_17_12_ROUTE (src/pc_p3_c1712r.ml);
      - P2CFN_P2_ALL (src/pc_p2c_final.ml): the results of MT Chs 5 and 9-12 used by Chs 13-17 (Thms 5.11, 5.15, 10.2, 11.8, 11.19, 11.31, Lemmas 11.2, 11.30, Thm 12.5, Props 12.7, 12.31, Thm 12.32, Prop 9.79, Cor 9.95), from P2CX2_CHAIN_OPEN5 (src/pc_p2c_chainx2.ml) and the Chapter 9 theorems of src/pc_p2b_close9.ml and src/pc_p2b_close95.ml;
      - P4_EXTINCTION_ALL (src/pc_p4_final.ml): finite extinction, from P4_EXTINCTION_FROM_CUTCAP (src/pc_p4_wire.ml) and the Colding-Minicozzi width (src/pc_p4_cm.ml, src/pc_cm_width.ml);
      - the analytic inputs, e.g. PDEF_MAXIMAL_FLOW (src/pc_pde_final.ml), PDE_UNIQUENESS (src/pc_rf_unique.ml), RFA_P2_THM_3_28 (src/pc_rfa_shi328.ml), RFA_P2_THM_4_32 (src/pc_rfa_pinch.ml), P2AT_THM_8_1 (src/pc_p2a_t81u.ml);
    - EVENT_TOPOLOGY (src/pc_smt_evtop.ml): each surgery event cuts along neck spheres and discards listed pieces, from APX_EVENT_TOPOLOGY_FROM_LEAVES (src/pc_apx_event.ml) with APX_A25 (src/pc_apx_a25top.ml) and SMT_SC_SPHERE_SEP (src/pc_smt_sep.ml);
    - RFS_CUTCAP_SC (src/pc_rfs_ccsc.ml): cutting and capping keeps components simply connected;
    - RFS_LISTED_SC_S3 (src/pc_smt_listed.ml): a simply connected listed piece is S^3, with KILLING_HOPF_COMPONENT (src/pc_geo_kh.ml);
    - RFS_SPHERE_SYSTEM (src/pc_smt_system.ml): if every component of the capped manifold is S^3, so is every component before cutting;
    - SMT_POINCARE_CONVERSION (src/pc_smt_glue.ml): from a diffeomorphism with the standard S^3 to the form of POINCARE_SMOOTH_STATEMENT, with SMT_SMALE_RADIAL (src/pc_smt_straight.ml) and SMT_DISC (src/pc_smt_disc.ml) in the gluing layer;
  - MOI_SST_HEADLINE (src/pc_moi_status.ml): |- !u. MOISE_SMOOTHING_STATEMENT u, by MOI_MOISE_SMOOTHING_FROM_CORES (src/pc_moi_chain.ml) from
    - MOI_CORE_STATUS (src/pc_moi_core_status.ml): |- MOISE_352_COMPLEX_STATEMENT (:7), Moise 35.2 for locally finite combinatorial 3-manifolds in R^7 with target R^3, from the theorems of the same file for Moise Secs 25-35 (e.g. MOI_CST_LOOPN, the loop theorem; MOI_CST_331, 33.1; MOI_CST_34EXT_7, Sec 34; MOI_CST_PROD_351, 35.1);
    - MOI_SST_SMOOTH (src/pc_moi_status.ml): |- !u. COMBINATORIAL_SMOOTHING_STATEMENT u, from MOI_SMO_TOP_FROM_PARTS (src/pc_moi_smo_vertex.ml), MOI_SMO_EDGE and MOI_SMO_PD2_FROM_LEAVES.
- POINCARE_EMBEDDED (src/pc_poincare_top.ml): |- POINCARE_EMBEDDED_STATEMENT (:N), by POINCARE_STATEMENT_IMP_EMBEDDED (src/poincare_statement_sanity.ml) from POINCARE_TOP at the type real^N.
