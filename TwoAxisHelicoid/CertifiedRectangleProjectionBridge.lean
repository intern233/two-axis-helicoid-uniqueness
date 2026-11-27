import TwoAxisHelicoid.RectangleHeightProjection
import TwoAxisHelicoid.RectangleHeightEdgeGeometry
import TwoAxisHelicoid.CentralBandSpatialConclusion
import TwoAxisHelicoid.CertifiedWeierstrassSeparation

namespace TwoAxisHelicoid
open Complex Set Topology

/-- Two vertical height-edge shape checks and the Gauss quadrant yield
an embedded closed surface patch whose projection onto the (height,
first horizontal coordinate) plane is itself a closed embedding. -/
theorem certified_rectangle_vertical_graph_of_bounds
    (left : CheckedRectangleShape true (1/8) (3/8)) (right : CheckedRectangleShape false (1/8) (3/8)) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let K := {z : ℂ | z.re∈Icc (1/2:ℝ) (5/8) ∧ z.im∈Icc (1/8:ℝ) (3/8)}
    (∀ z∈K, (thetaGauss p.t p.a 1 z).im<0) →
    IsClosedEmbedding (fun z : K => (X z.1 2,X z.1 0)) ∧
    InjOn certifiedTorusImmersion (puncturedPlaneProjection certifiedPeriodPair '' (Subtype.val ⁻¹' K)) := by
  intro p X K sign
  let H := actualComplexHeight p.t p.a 1 p.height_pos
  have d : HasTwoAxisHelicoidCoordinateDifferential X p.t p.a 1 p.height_pos := fun z hz =>
    ((actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
      p.vertical_closed p.horizontal_closed).2.2.2 z hz).1
  have ty : (3/8:ℝ)<p.t := (by norm_num [rootTLower] : (3/8:ℝ)<rootTLower).trans certifiedClosedParameters_bounds.1.1
  have off {z : ℂ} (h : z∈K) : z∉certifiedPeriodPair.lattice :=
    rhombic_horizontal_strip_not_mem p.height_pos ⟨by linarith [h.2.1],h.2.2.trans_lt ty⟩
  obtain ⟨cv,inc⟩ := rectangle_height_edge_shapes left right
  have hi := quarter_rectangle_vertical_projection (L:=1/2) (R:=5/8) (B:=1/8) (T:=3/8) p.height_pos p.abscissa_mem
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ty d cv inc.monotoneOn (fun z hx hy => sign z ⟨hx,hy⟩)
  have pj : InjOn (fun z => (X z 2,X z 0)) K := by
    intro z hz w hw e
    apply hi hz hw
    have x0 : X z 0=X w 0 := congrArg Prod.snd e
    refine Prod.ext ?_ x0
    change (H z).re=(H w).re
    rw [← actual_complex_height_centered_primitive p.height_pos d (off hz),← actual_complex_height_centered_primitive p.height_pos d (off hw)]
    exact congrArg (fun v : ℝ => v-X 1 2) (congrArg Prod.fst e)
  have comp : IsCompact K := (isCompact_Icc : IsCompact (Icc (1/2:ℝ) (5/8))).reProdIm (isCompact_Icc : IsCompact (Icc (1/8:ℝ) (3/8)))
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp comp
  have cx : Continuous (fun z : K => X z.1) := continuousOn_iff_continuous_domRestrict.mp (fun z hz => (d z (off hz)).continuousAt.continuousWithinAt)
  refine ⟨(((continuous_apply 2).comp cx).prodMk ((continuous_apply 0).comp cx)).isClosedEmbedding
    (fun z w e => Subtype.ext (pj z.2 w.2 e)),?_⟩
  rintro _ ⟨z,hz,rfl⟩ _ ⟨w,hw,rfl⟩ e
  have eq : X z.1=X w.1 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.injective e
  exact congrArg (puncturedPlaneProjection certifiedPeriodPair) (Subtype.ext (pj hz hw (congrArg (fun v : Fin 3 → ℝ => (v 2,v 0)) eq)))

/-- The eight rational edge proofs discharge every hypothesis for
vertical-plane injectivity on the entire closed parameter rectangle. -/
theorem certified_closed_rectangle_of_eight_edges
    (lh : CheckedCentralBandEdge .heightNeg true (1/2) (1/8) (3/8))
    (rh : CheckedCentralBandEdge .heightPos true (5/8) (1/8) (3/8))
    (lg : CheckedCentralBandEdge .gauss true (1/2) (1/8) (3/8))
    (rg : CheckedCentralBandEdge .gauss true (5/8) (1/8) (3/8))
    (bg : CheckedCentralBandEdge .gauss false (1/8) (1/2) (5/8))
    (tg : CheckedCentralBandEdge .gauss false (3/8) (1/2) (5/8))
    (ls : CheckedRectangleShape true (1/8) (3/8)) (rs : CheckedRectangleShape false (1/8) (3/8)) :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let K := {z : ℂ | z.re∈Icc (1/2:ℝ) (5/8) ∧ z.im∈Icc (1/8:ℝ) (3/8)}
    IsClosedEmbedding (fun z : K => (X z.1 2,X z.1 0)) ∧
    InjOn certifiedTorusImmersion (puncturedPlaneProjection certifiedPeriodPair '' (Subtype.val ⁻¹' K)) :=
  certified_rectangle_vertical_graph_of_bounds ls rs (fun z hz =>
    ((central_band_spatial_conclusion lh rh lg rg bg tg).1 z hz.1 hz.2).2.trans_lt (by norm_num))

theorem checked_right_gauss_groups_cover
    (g0 : CheckedCentralBandEdge .gauss true (5/8) (1/8) (33/256))
    (g1 : CheckedCentralBandEdge .gauss true (5/8) (33/256) (137/1024))
    (g2 : CheckedCentralBandEdge .gauss true (5/8) (137/1024) (145/1024))
    (g3 : CheckedCentralBandEdge .gauss true (5/8) (145/1024) (153/1024))
    (g4 : CheckedCentralBandEdge .gauss true (5/8) (153/1024) (161/1024))
    (g5 : CheckedCentralBandEdge .gauss true (5/8) (161/1024) (87/512))
    (g6 : CheckedCentralBandEdge .gauss true (5/8) (87/512) (95/512))
    (g7 : CheckedCentralBandEdge .gauss true (5/8) (95/512) (103/512))
    (g8 : CheckedCentralBandEdge .gauss true (5/8) (103/512) (111/512))
    (g9 : CheckedCentralBandEdge .gauss true (5/8) (111/512) (119/512))
    (g10 : CheckedCentralBandEdge .gauss true (5/8) (119/512) (127/512))
    (g11 : CheckedCentralBandEdge .gauss true (5/8) (127/512) (71/256))
    (g12 : CheckedCentralBandEdge .gauss true (5/8) (71/256) (79/256))
    (g13 : CheckedCentralBandEdge .gauss true (5/8) (79/256) (87/256))
    (g14 : CheckedCentralBandEdge .gauss true (5/8) (87/256) (95/256))
    (g15 : CheckedCentralBandEdge .gauss true (5/8) (95/256) (3/8)) :
    CheckedCentralBandEdge .gauss true (5/8) (1/8) (3/8) :=
  (.join (.join (.join (.join g0 g1) (.join g2 g3)) (.join (.join g4 g5) (.join g6 g7))) (.join (.join (.join g8 g9) (.join g10 g11)) (.join (.join g12 g13) (.join g14 g15))))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.checked_right_gauss_groups_cover
#print axioms TwoAxisHelicoid.certified_closed_rectangle_of_eight_edges
#print axioms TwoAxisHelicoid.certified_rectangle_vertical_graph_of_bounds
