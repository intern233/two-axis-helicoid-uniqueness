import TwoAxisHelicoid.HelicoidInteriorCrossing

namespace TwoAxisHelicoid
open Complex Filter Set Topology InnerProductSpace
open scoped Topology

/-- At a tangency to a comparison helicoid the embedded marked torus
takes both signs even when restricted to an inward tangent disk side
in its own parameters. -/
theorem marked_torus_crosses_tangent_helicoid_within {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) (hE : IsClosedEmbedding (harmonicTorusImmersion hX))
    {g : ℂ} (hg : normSq g=1) (α b : ℝ) {z : ℂ} (hz : z ∉ L.lattice)
    {S : Set ℂ} (disks : HasInwardTangentDisksAt S z) (on : X z ∈ range (axisRuledHelicoid g α b))
    (tangent : fderiv ℝ (fun w => axisHelicoidSide g α b (X w)) z=0) :
    (∃ᶠ w in 𝓝[S] z, 0 < axisHelicoidSide g α b (X w)) ∧ (∃ᶠ w in 𝓝[S] z, axisHelicoidSide g α b (X w)<0) := by
  have reg : ∀ᶠ w in 𝓝 z, (∀ j, HarmonicAt (fun u => X u j) w) ∧ ConformalCoordinateDerivatives X w :=
    Filter.mem_of_superset (L.isClosed_lattice.isOpen_compl.mem_nhds hz) fun w hw => ⟨hX.harmonic w hw,hX.conformal w hw⟩
  have fac := harmonic_immersion_helicoid_drift_factor reg (hX.immersion z hz) hg α b
  have eq := (axisHelicoidSide_eq_zero_iff hg α b _).mpr on
  have no := marked_torus_not_locally_contained_in_helicoid hX hE hg α b hz
  constructor
  · intro h
    have np := eventually_nhdsWithin_iff.mp (h.mono fun _ hw => le_of_not_gt hw)
    exact no ((fac.boundary_contact disks eq tangent (Or.inr np)).mono fun w hw => (axisHelicoidSide_eq_zero_iff hg α b _).mp hw)
  · intro h
    have nn := eventually_nhdsWithin_iff.mp (h.mono fun _ hw => le_of_not_gt hw)
    exact no ((fac.boundary_contact disks eq tangent (Or.inl nn)).mono fun w hw => (axisHelicoidSide_eq_zero_iff hg α b _).mp hw)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_torus_crosses_tangent_helicoid_within
