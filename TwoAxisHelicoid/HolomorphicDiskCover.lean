import TwoAxisHelicoid.DiskMobiusDistance
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace TwoAxisHelicoid
open Complex Metric Set Filter Topology
open scoped Topology ContDiff Manifold ComplexConjugate

def unitDiskOpen : TopologicalSpace.Opens ℂ := ⟨complexUnitDisk,isOpen_ball⟩

abbrev RiemannUnitDisk := ↥unitDiskOpen

noncomputable def unitDiskExtension (f : RiemannUnitDisk → RiemannUnitDisk) : ℂ → ℂ :=
  by classical exact fun z => if h : z ∈ complexUnitDisk then (f ⟨z,h⟩).1 else 0

theorem unitDiskExtension_apply (f : RiemannUnitDisk → RiemannUnitDisk) (x : RiemannUnitDisk) :
    unitDiskExtension f x.1 = (f x).1 := by
  unfold unitDiskExtension
  split
  · rfl
  · next hx => exact (hx x.2).elim

theorem unitDiskExtension_analytic {f : RiemannUnitDisk → RiemannUnitDisk}
    (hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) : AnalyticOnNhd ℂ (unitDiskExtension f) complexUnitDisk := by
  intro z hz
  let x : RiemannUnitDisk := ⟨z,hz⟩
  have hc : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun q : RiemannUnitDisk => unitDiskExtension f q.1) x := by
    apply ((contMDiff_subtype_val (U := unitDiskOpen)).comp hf x).congr_of_eventuallyEq
    exact Eventually.of_forall (unitDiskExtension_apply f)
  exact (contMDiffAt_subtype_iff.mp hc).contDiffAt.analyticAt

noncomputable def unitDiskDistance (x y : RiemannUnitDisk) : ℝ := ‖diskMobius x.1 y.1‖

theorem unitDisk_biholomorphic_distance (f : RiemannUnitDisk ≃ₜ RiemannUnitDisk)
    (hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) (hi : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f.symm)
    (x y : RiemannUnitDisk) : unitDiskDistance (f x) (f y) = unitDiskDistance x y := by
  have hc {g : RiemannUnitDisk → RiemannUnitDisk} (hg : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g)
      (a b : RiemannUnitDisk) : unitDiskDistance (g a) (g b) ≤ unitDiskDistance a b := by
    have hm : MapsTo (unitDiskExtension g) complexUnitDisk complexUnitDisk := fun z hz => by
      rw [show unitDiskExtension g z = (g ⟨z,hz⟩).1 from unitDiskExtension_apply g ⟨z,hz⟩]
      exact (g ⟨z,hz⟩).2
    simpa only [unitDiskDistance,unitDiskExtension_apply] using
      disk_holomorphic_distance_nonexpanding (unitDiskExtension_analytic hg) hm a.2 b.2
  exact le_antisymm (hc hf x y) (by simpa only [f.symm_apply_apply] using hc hi (f x) (f y))

/-- Any continuous self-lift of a locally biholomorphic covering is holomorphic. -/
theorem holomorphic_of_cover_deck {E M : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace ℂ M] {p : E → M}
    (hp : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p)
    {f : E → E} (hf : Continuous f) (he : ∀ z, p (f z) = p z) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f := by
  intro x
  let h := hp (f x)
  have hx : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h.localInverse (p x) := he x ▸ h.contMDiffAt_localInverse
  apply (hx.comp x (hp x).contMDiffAt).congr_of_eventuallyEq
  filter_upwards [hf.continuousAt.eventually (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)] with z hz
  change f z = h.localInverse (p z)
  rw [← he z,h.localInverse_left_inv hz]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unitDisk_biholomorphic_distance
#print axioms TwoAxisHelicoid.holomorphic_of_cover_deck
