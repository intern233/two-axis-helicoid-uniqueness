import TwoAxisHelicoid.LatticePoleSets
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Normed.Field.Lemmas

namespace TwoAxisHelicoid
open Complex Set Filter Bornology Metric
open scoped Topology

noncomputable def cutOffReciprocal (b : ContDiffBump (0:ℂ)) (z : ℂ) : ℂ :=
  (1-b z) • z⁻¹

theorem cutOffReciprocal_contDiff (b : ContDiffBump (0:ℂ)) :
    ContDiff ℝ 1 (cutOffReciprocal b) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases zero : z=0
  · subst z
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [b.eventuallyEq_one] with x hx
    change (1-b x) • x⁻¹=0
    simp [show b x=1 from hx]
  · exact (contDiffAt_const.sub b.contDiffAt).smul (contDiffAt_id.inv zero)

theorem cutOffReciprocal_bound (b : ContDiffBump (0:ℂ)) (z : ℂ) :
    ‖cutOffReciprocal b z‖≤b.rIn⁻¹ := by
  by_cases small : ‖z‖≤b.rIn
  · have one := b.one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right] using small)
    simp [cutOffReciprocal,one,b.rIn_pos.le]
  · have pos := lt_of_not_ge small
    have s : 0≤1-b z := sub_nonneg.mpr b.le_one
    rw [cutOffReciprocal,norm_smul,Real.norm_eq_abs,abs_of_nonneg s,norm_inv]
    calc
      (1-b z)*‖z‖⁻¹ ≤ 1*‖z‖⁻¹ := mul_le_mul_of_nonneg_right (sub_le_self _ b.nonneg) (by positivity)
      _ ≤ b.rIn⁻¹ := by simpa only [one_mul] using (inv_le_inv₀ (b.rIn_pos.trans pos) b.rIn_pos).mpr pos.le

theorem cutOffReciprocal_exact {b : ContDiffBump (0:ℂ)} {z : ℂ} (large : b.rOut≤‖z‖) :
    cutOffReciprocal b z=z⁻¹ := by
  have away := b.zero_of_le_dist (by simpa only [dist_zero_right] using large)
  simp [cutOffReciprocal,away]

theorem cutOffReciprocal_mul_factor (b : ContDiffBump (0:ℂ)) (z : ℂ) :
    ∃ k∈Icc (0:ℝ) 1, cutOffReciprocal b z*z=(k:ℂ) := by
  by_cases hz : z=0
  · exact ⟨0,⟨le_rfl,zero_le_one⟩,by simp [hz]⟩
  · refine ⟨1-b z,⟨sub_nonneg.mpr b.le_one,sub_le_self _ b.nonneg⟩,?_⟩
    rw [cutOffReciprocal,Complex.real_smul,mul_assoc,inv_mul_cancel₀ hz,mul_one]

/-- The reciprocal of a meromorphic coefficient, cut off only near
its zeros, extends smoothly by zero at its lattice poles. It yields a
globally bounded vector field for transport between regular levels. -/
theorem smooth_bounded_lattice_reciprocal (L : PeriodPair) (f : ℂ → ℂ)
    (reg : ∀ z∉L.lattice, AnalyticAt ℂ f z)
    (mer : ∀ z∈L.lattice, MeromorphicAt f z)
    (pole : ∀ z∈L.lattice, Tendsto f (𝓝[≠] z) (cobounded ℂ))
    (per : ∀ z w, w∈L.lattice → f (z+w)=f z) {δ : ℝ} (hδ : 0<δ) :
    ∃ V : ℂ → ℂ, ContDiff ℝ 1 V ∧ (∀ z, ‖V z‖≤(δ/2)⁻¹) ∧
      (∀ z w, w∈L.lattice → V (z+w)=V z) ∧ (∀ z∈L.lattice, V z=0) ∧
      (∀ z∉L.lattice, δ≤‖f z‖ → V z=(f z)⁻¹) ∧
      ∀ z∉L.lattice, ∃ k∈Icc (0:ℝ) 1, V z*f z=(k:ℂ) := by
  classical
  let b : ContDiffBump (0:ℂ) := ⟨δ/2,δ,by positivity,by linarith⟩
  let V := fun z => if z∈L.lattice then 0 else cutOffReciprocal b (f z)
  have equal {z : ℂ} (hz : z∉L.lattice) : V =ᶠ[𝓝 z] cutOffReciprocal b ∘ f := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with x hx using ite_eq_right hx
  refine ⟨V,contDiff_iff_contDiffAt.mpr (fun z => ?_),?_,?_,?_,?_,?_⟩
  · by_cases hz : z∈L.lattice
    · have E : (fun x => (f x)⁻¹) =ᶠ[𝓝[≠] z] V := by
        filter_upwards [(tendsto_norm_atTop_iff_cobounded.mpr (pole z hz)).eventually_ge_atTop δ,
          latticePoleSet_punctured_avoids L (finite_singleton (0:ℂ)) z] with x big avoids
        have off : x∉L.lattice := fun h => avoids ⟨0,rfl,by simpa using h⟩
        simp only [V,ite_eq_right off,cutOffReciprocal_exact (b := b) big]
      have mv : MeromorphicAt V z := (mer z hz).inv.congr E
      have cv : ContinuousAt V z := by
        apply continuousAt_iff_punctured_nhds.mpr
        simpa only [V,ite_eq_left hz] using ((tendsto_inv₀_cobounded.comp (pole z hz)).congr' E)
      exact ((mv.analyticAt cv).restrictScalars (𝕜 := ℝ)).contDiffAt
    · exact ((cutOffReciprocal_contDiff b).contDiffAt.comp z
        ((reg z hz).restrictScalars (𝕜 := ℝ)).contDiffAt).congr_of_eventuallyEq (equal hz)
  · intro z
    by_cases hz : z∈L.lattice
    · rw [show V z=0 from ite_eq_left hz,norm_zero]
      positivity
    · rw [show V z=cutOffReciprocal b (f z) from ite_eq_right hz]
      exact cutOffReciprocal_bound b (f z)
  · intro z w hw
    have equiv : z+w∈L.lattice ↔ z∈L.lattice :=
      ⟨fun h => by simpa using L.lattice.sub_mem h hw,fun h => L.lattice.add_mem h hw⟩
    simp only [V,equiv,per z w hw]
  · intro z hz
    exact ite_eq_left hz
  · intro z hz h
    exact (ite_eq_right hz : V z=cutOffReciprocal b (f z)).trans (cutOffReciprocal_exact h)

  · intro z hz
    rw [show V z=cutOffReciprocal b (f z) from ite_eq_right hz]
    exact cutOffReciprocal_mul_factor b _

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_bounded_lattice_reciprocal
