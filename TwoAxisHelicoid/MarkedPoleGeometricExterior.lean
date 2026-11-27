import TwoAxisHelicoid.IntegerBranchGeometricExterior
import TwoAxisHelicoid.GeometricExteriorPullback
import TwoAxisHelicoid.HorizontalLinePlacement
import TwoAxisHelicoid.SchwarzNormalizedImmersion
import TwoAxisHelicoid.TorusEndScalingOrders
import TwoAxisHelicoid.ConformalTorusScaling
import TwoAxisHelicoid.MeromorphicSpatialOrientation

namespace TwoAxisHelicoid
open Complex Matrix Set Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- The arbitrary marked torus with two actual poles and its two contained
straight lines acquires a geometric exterior chart in an orthogonal frame.
No global period uniqueness or selection of the integer branch is used. -/
theorem marked_poles_two_lines_geometric_exterior
    (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (hX : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (d : ℂ) (hd : ‖d‖ = 1) (A : Fin 3 → ℝ)
    (hline : ∀ r : ℝ, A+r • ![d.re,d.im,0] ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (hver : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    {α : ℝ} (hα : α ≠ 0)
    (hend : ApproachesSetAtInfinity (range (fun q : PuncturedPeriodTorus L => X q.1)) (range (axisRuledHelicoid I α 0)))
    (hhi : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧ Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z))
    (hheight : meromorphicOrderAt (fun w => immersionComplexCoefficient (X ∘ periodTorusProjection L) w 2) 0 = (-2 : ℤ))
    (hgauss : meromorphicOrderAt (immersionGaussLogDerivative (X ∘ periodTorusProjection L)) 0 = (-2 : ℤ)) :
    ∃ (T : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ)) (b : Fin 3 → ℝ), (∀ u v, T u ⬝ᵥ T v = u ⬝ᵥ v) ∧
      Nonempty (GeometricExteriorCoordinate (fun q : PuncturedPeriodTorus L => b+T (X q.1))) := by
  let C : Fin 3 → ℝ := ![0,0,A 2]
  let R₀ := lineAxisCoordinates d hd C
  obtain ⟨_,hclosed,hhor,hvert,hreg,hh₀,hg₀⟩ := horizontal_line_axes_placement L X hX d hd A hline hver hα hend hhi
  obtain ⟨s,t,hs,ht,hp,hY⟩ := straight_axes_to_two_axis_harmonic_immersion L (R₀ ∘ X) hclosed hhor hvert hreg
  let M := rhombicPeriodPair t ht
  obtain ⟨_,e,_,_,_,hef,hei,_,he⟩ := scaled_harmonic_biholomorphic_correspondence L M s hs hp (R₀ ∘ X) hY
  obtain ⟨hh,hg⟩ := marked_torus_scaled_end_orders L M ((R₀ ∘ X) ∘ periodTorusProjection L) s⁻¹
    (inv_ne_zero hs) (fun z hz => ⟨(hreg z hz).1,(hreg z hz).2.1⟩) (hh₀.trans hheight) (hg₀.trans hgauss)
  obtain ⟨a,c,m,R,ha,hc,_,_,hR,hW,hWH,hWG⟩ := harmonic_meromorphic_oriented_integer_data ht hY hh hg
  obtain ⟨U⟩ := harmonic_integer_geometric_exterior ht ha hc m hW hWH hWG
  let J := (R₀.trans R).trans verticalQuarterTurnHomeomorph
  have hJ (u v : Fin 3 → ℝ) : (∑ j, (J u j-J v j)^2) = ∑ j, (u j-v j)^2 := by
    calc
      _ = ∑ j, (verticalRotation I (R (R₀ u)-R (R₀ v)) j)^2 :=
        congrArg (fun w : Fin 3 → ℝ => ∑ j, (w j)^2) ((verticalRotation I).map_sub _ _).symm
      _ = ∑ j, (R (R₀ u) j-R (R₀ v) j)^2 := verticalRotation_preserves_squared_length Complex.norm_I _
      _ = _ := (hR (R₀ u) (R₀ v)).trans (lineAxisCoordinates_dist_sq d hd C u v)
  obtain ⟨T,b,hT,hb⟩ := orthogonal_affine_coordinates_of_displacement J hJ
  refine ⟨T,b,hT,geometric_exterior_coordinate_pullback e hef hei ?_ U⟩
  intro q
  change verticalRotation I (harmonicTorusImmersion hW (e q)) = b+T (X q.1)
  rw [harmonicTorusImmersion_space_map hY R hW]
  change verticalRotation I (R (harmonicTorusImmersion hY (e q))) = _
  rw [he]
  exact hb (X q.1)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_poles_two_lines_geometric_exterior
