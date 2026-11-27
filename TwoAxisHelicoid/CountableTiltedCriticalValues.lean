import TwoAxisHelicoid.SimpleImmersionHeightContacts
import Mathlib.Topology.Algebra.Module.Cardinality

namespace TwoAxisHelicoid
open Complex Set Filter Topology MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace Topology

/-- For almost every physical tilt the actual critical values of
a smooth immersed patch form a countable set. The patch can be
noncompact and may periodically cover the surface. -/
theorem ae_countable_tilted_critical_values {D : Set ℂ} {F : ℂ → Fin 3 → ℝ}
    (smooth : ∀ z∈D, ContDiffAt ℝ 3 F z) (imm : ∀ z∈D, Function.Injective (fderiv ℝ F z)) :
    ∀ᵐ s : ℂ, ((tiltedSpatialHeight s ∘ F) '' {z | z∈D ∧ fderiv ℝ (tiltedSpatialHeight s ∘ F) z=0}).Countable := by
  classical
  obtain ⟨C,ct,W,f,sw,cover⟩ := countable_horizontal_graph_contact_cover smooth imm
  let : Countable C := ct.to_subtype
  choose K count V P inv branch using fun i => countable_graph_slope_inverses (sw i)
  let (i : C) : Countable (K i) := (count i).to_subtype
  filter_upwards [ae_nondegenerate_graph_height_slopes W f (fun i x hx => (sw i x hx).of_le (by norm_num))] with s good
  let heights := fun j : Σ i : C, K i => f j.1 (P j.1 j.2 s)-⟪s,P j.1 j.2 s⟫_ℝ
  apply (countable_range heights).mono
  rintro _ ⟨z,⟨hz,crit⟩,rfl⟩
  obtain ⟨i,inside,eq,slope,_⟩ := cover s z hz crit
  obtain ⟨k,_,atPoint⟩ := branch i _ inside (good i _ inside slope)
  rw [slope] at atPoint
  refine ⟨⟨i,k⟩,?_⟩
  change f i (P i k s)-⟪s,P i k s⟫_ℝ=F z 2-⟪s,spatialGraphProjection 0 1 (F z)⟫_ℝ
  rw [atPoint,eq]

/-- A neighborhood condition on heights can always be achieved away
from all critical values in a given countable exceptional set. -/
theorem exists_height_outside_countable {B : Set ℝ} (small : B.Countable) {v : ℝ}
    {P : ℝ → Prop} (atHeight : ∀ᶠ s in 𝓝 v, P s) : ∃ s, s∉B ∧ P s := by
  obtain ⟨U,sub,op,inside⟩ := mem_nhds_iff.mp atHeight
  obtain ⟨s,regular,hs⟩ := (small.dense_compl ℝ).exists_mem_open op ⟨v,inside⟩
  exact ⟨s,regular,sub hs⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ae_countable_tilted_critical_values
#print axioms TwoAxisHelicoid.exists_height_outside_countable
