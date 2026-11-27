import TwoAxisHelicoid.CompactnessNormalCoreGraphs
import TwoAxisHelicoid.NormalTubeHeightConvergence

namespace TwoAxisHelicoid
open Set Filter
open scoped Topology ContDiff

/-- In a smooth normal-coordinate tube, the actual height of the point
over a given base point is obtained by applying the signed coordinate
to its Euclidean position. Spatial C¹ convergence on the marked core
therefore gives the two height convergence conditions in the HWV input. -/
theorem marked_core_plane_heights_decay {A : PeriodPair} (C : TorusGeneratingCoreModel A)
    (W : ℕ → PitchNormalizedBasicImmersion) (D : ∀ n, TorusNormalCorePatch C (rhombicPeriodPair (W n).t (W n).ht))
    (X : ℂ → EuclideanSpace ℝ (Fin 3)) (Z : ℕ → ℂ → EuclideanSpace ℝ (Fin 3))
    (signed : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hpos : ∀ n (b : (D n).patch) z, ((D n).project b).1 = periodTorusProjection A z →
      Z n z = (W n).torusPosition b.1)
    (hsign : ∀ n (b : (D n).patch), (D n).height b = signed ((W n).torusPosition b.1)) :
    let U := periodTorusProjection A ⁻¹' C.carrier
    (∀ z ∈ U, ContDiffAt ℝ 1 X z) → (∀ n z, z ∈ U → DifferentiableAt ℝ (Z n) z) →
    (∀ z ∈ U, ContDiffAt ℝ 1 signed (X z)) → (∀ n z, z ∈ U → DifferentiableAt ℝ signed (Z n z)) →
    (∀ z ∈ U, signed (X z) = 0) → TendstoLocallyUniformlyOn Z X atTop U →
    TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ X) atTop U →
    (∀ n z, z ∈ U → DifferentiableAt ℝ (D n).planeHeight z) ∧
    TendstoLocallyUniformlyOn (fun n => (D n).planeHeight) (fun _ => 0) atTop U ∧
    TendstoLocallyUniformlyOn (fun n => fderiv ℝ (D n).planeHeight) (fun _ => 0) atTop U := by
  dsimp only
  intro hX hZ hδ hδZ hzero hv hd
  have hu (n : ℕ) (z : ℂ) (hz : periodTorusProjection A z ∈ C.carrier) :
      (D n).planeHeight z = signed (Z n z) := by
    let q : C.carrier := ⟨_,hz⟩
    let b := ((D n).onto q).choose
    have hb : ((D n).project b).1 = periodTorusProjection A z :=
      congrArg Subtype.val ((D n).onto q).choose_spec
    rw [hpos n b z hb]
    simpa only [TorusNormalCorePatch.planeHeight,dite_eq_left hz] using hsign n b
  exact spatial_C1_convergence_gives_tube_height_decay
    (C.isOpen_carrier.preimage QuotientAddGroup.continuous_mk) X Z signed _ hX hZ hδ hδZ hzero hu hv hd

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_core_plane_heights_decay
