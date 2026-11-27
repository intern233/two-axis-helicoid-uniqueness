import TwoAxisHelicoid.PuncturedTorusUnmarkedReflectionParity
import TwoAxisHelicoid.EmbeddedHalfTurnNormalSign
import TwoAxisHelicoid.OriginalSurfaceSchwarz
import TwoAxisHelicoid.PuncturedTorusRealOrientation
import TwoAxisHelicoid.GeometricHelicoidHypotheses
import TwoAxisHelicoid.OriginalCartesianUnitNormal

namespace TwoAxisHelicoid
open Set Filter Matrix Complex Topology
open scoped Topology Manifold ContDiff

/-- D.2 for an actual smooth family through a geometric TwoAxisHelicoid surface.
Nearby minimal slices contain the two fixed straight lines. Their Schwarz
actions, their pointwise continuous lifts, and the parity of the actual
derivative are derived for either continuous unit normal on the central surface. -/
theorem OriginalSmoothHelicoid.fixed_axes_family_normal_velocity_odd
    (base : OriginalSmoothHelicoid) (X : ℝ → base.carrier → Fin 3 → ℝ) (atZero : X 0 = base.position)
    (family : ∀ p, ContDiffAt ℝ ∞
      (fun a : ℝ × ℂ => X a.1 ((chartAt ℂ p).symm a.2)) (0,chartAt ℂ p p))
    (slices : ∀ᶠ s in 𝓝 (0:ℝ), IsClosedEmbedding (X s) ∧
      ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (X s) ∧
      (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (X s) p)) ∧
      (∀ p, coordinateMeanCurvature (X s ∘ (chartAt ℂ p).symm) (chartAt ℂ p p)=0) ∧
      (∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ)∈range (X s)) ∧
      (∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ)∈range (X s)))
    (N : base.carrier → Fin 3 → ℝ)
    (cn : Continuous N) (unit : ∀ p, N p ⬝ᵥ N p = 1)
    (normal : ∀ p h, fderiv ℝ (base.position ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) h ⬝ᵥ N p = 0) :
    let u := fun p => deriv (fun s => X s p) 0 ⬝ᵥ N p
    ∃ ρX ρZ : base.carrier ≃ₜ base.carrier, ∀ p,
      base.position (ρX p) = halfTurnX (base.position p) ∧ base.position (ρZ p) = halfTurnZ (base.position p) ∧
      u (ρX p) = -u p ∧ u (ρZ p) = -u p ∧
      (halfTurnX (base.position p) = base.position p ∨ halfTurnZ (base.position p) = base.position p → u p=0) := by
  let := punctured_torus_is_path_connected base.modelTorus
  let : PathConnectedSpace base.carrier :=
    base.topologicalType.symm.surjective.pathConnectedSpace base.topologicalType.symm.continuous
  have symmetric : ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, halfTurnX (X s p) ∈ range (X s) ∧
      halfTurnZ (X s p) ∈ range (X s) := by
    filter_upwards [slices] with s hs
    obtain ⟨emb,sm,imm,minimal,horizontal,vertical⟩ := hs
    obtain ⟨S,man,charts⟩ := punctured_torus_minimal_induced_harmonic_atlas base.topologicalType sm imm minimal
    let : ChartedSpace ℂ base.carrier := S
    let : IsManifold 𝓘(ℂ,ℂ) ω base.carrier := man
    obtain ⟨h,_,_,hx⟩ := horizontal_schwarz_on_original_surface emb charts horizontal
    obtain ⟨v,_,_,vz⟩ := vertical_schwarz_on_original_surface emb charts vertical
    exact fun p => ⟨⟨h p,hx p⟩,⟨v p,vz p⟩⟩
  have regular (p : base.carrier) := smooth_surface_regular_manifold_chart base.smooth base.immersion p
    (chartAt ℂ p p) ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
  obtain ⟨_,_,_,_,lineX,lineZ⟩ := slices.self_of_nhds
  obtain ⟨signX,signZ⟩ := embedded_coordinate_half_turn_normal_signs base.closedEmbedding.isEmbedding
    (chartAt ℂ) (mem_chart_source ℂ) (fun p => (regular p).1) (fun p => (regular p).2)
    cn unit normal (by simpa only [atZero] using symmetric.self_of_nhds)
    (by simpa only [atZero] using lineX) (by simpa only [atZero] using lineZ)
  have proper : IsProperMap (X 0) := by rw [atZero]; exact base.closedEmbedding.isProperMap
  have result := punctured_torus_fixed_axes_normal_velocity_odd base.topologicalType X proper
    (slices.mono fun _ hs => hs.1.isEmbedding) (chartAt ℂ) (mem_chart_source ℂ) family
    (by simpa only [atZero] using fun p => (regular p).2) N
    (by simpa only [atZero] using normal) symmetric (by simpa only [atZero] using signX)
    (by simpa only [atZero] using signZ)
  simpa only [atZero] using result

/-- The original geometric assumptions on the family supply all the data in
D.2, including the central continuous unit normal used to measure its velocity. -/
theorem OriginalSmoothHelicoid.exists_fixed_axes_odd_normal_velocity
    (base : OriginalSmoothHelicoid) (X : ℝ → base.carrier → Fin 3 → ℝ) (atZero : X 0 = base.position)
    (family : ∀ p, ContDiffAt ℝ ∞
      (fun a : ℝ × ℂ => X a.1 ((chartAt ℂ p).symm a.2)) (0,chartAt ℂ p p))
    (slices : ∀ᶠ s in 𝓝 (0:ℝ), IsClosedEmbedding (X s) ∧
      ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ (X s) ∧
      (∀ p, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (X s) p)) ∧
      (∀ p, coordinateMeanCurvature (X s ∘ (chartAt ℂ p).symm) (chartAt ℂ p p)=0) ∧
      (∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ) ∈ range (X s)) ∧
      (∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range (X s))) :
    ∃ N : base.carrier → Fin 3 → ℝ, Continuous N ∧ (∀ p, N p ⬝ᵥ N p = 1) ∧
      (∀ p v, fderiv ℝ (base.position ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) v ⬝ᵥ N p = 0) ∧
      let u := fun p => deriv (fun s => X s p) 0 ⬝ᵥ N p
      ∃ ρX ρZ : base.carrier ≃ₜ base.carrier, ∀ p,
        base.position (ρX p) = halfTurnX (base.position p) ∧ base.position (ρZ p) = halfTurnZ (base.position p) ∧
        u (ρX p) = -u p ∧ u (ρZ p) = -u p ∧
        (halfTurnX (base.position p) = base.position p ∨ halfTurnZ (base.position p) = base.position p → u p=0) := by
  obtain ⟨N,cn,unit,normal⟩ := base.exists_cartesian_unit_normal
  exact ⟨N,cn,unit,normal,base.fixed_axes_family_normal_velocity_odd X atZero family slices N cn unit normal⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.fixed_axes_family_normal_velocity_odd
#print axioms TwoAxisHelicoid.OriginalSmoothHelicoid.exists_fixed_axes_odd_normal_velocity
