import TwoAxisHelicoid.FiniteModulusHelicoidEnd

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- If the infinite spatial end is the inner circle of an isothermal
annulus, that circle has radius zero. Inversion changes its position
without changing isothermality or spatial properness. -/
theorem HasHelicoidC1End.inner_radius_zero {M : Type*} [TopologicalSpace M]
    {X : M → HelicoidTubeCoordinates} (endGraph : HasHelicoidC1End X) (cont : Continuous X)
    {r R : ℝ} (nonneg : 0≤r) (lt : r<R) {Y : ℂ → HelicoidTubeCoordinates}
    (diff : ∀ z : ℂ, r<‖z‖ → ‖z‖<R → DifferentiableAt ℝ Y z)
    (image : ∀ z : ℂ, r<‖z‖ → ‖z‖<R → Y z∈range X)
    (inj : InjOn Y {z | r<‖z‖ ∧ ‖z‖<R})
    (conf : ∀ z : ℂ, r<‖z‖ → ‖z‖<R → ∃ c : ℝ, ∀ v : ℂ,
      (∑ j, (tubeCartesian (fderiv ℝ Y z v) j)^2)=c*‖v‖^2)
    (esc : ∀ B : ℝ, ∃ s>r, ∀ z : ℂ, r<‖z‖ → ‖z‖<s → B<‖Y z‖) : r=0 := by
  by_contra nz
  have hr : 0<r := lt_of_le_of_ne nonneg (Ne.symm nz)
  have hR : 0<R := hr.trans lt
  have pos {z : ℂ} (hz : R⁻¹<‖z‖) : 0<‖z‖ := (inv_pos.mpr hR).trans hz
  have region {z : ℂ} (hz : R⁻¹<‖z‖) (hz' : ‖z‖<r⁻¹) :
      r<‖z⁻¹‖ ∧ ‖z⁻¹‖<R := by
    rw [norm_inv]
    exact ⟨(lt_inv_comm₀ hr (pos hz)).mpr hz',(inv_lt_comm₀ (pos hz) hR).mpr hz⟩
  have dr {z : ℂ} (hz : R⁻¹<‖z‖) := (hasDerivAt_inv (norm_pos_iff.mp (pos hz))).hasFDerivAt.restrictScalars ℝ
  apply endGraph.no_outer_circle cont (r := R⁻¹) (Y := Y ∘ Inv.inv) (inv_pos.mpr hr)
    ((inv_lt_inv₀ hR hr).mpr lt)
  · intro z hz hz'
    exact (diff _ (region hz hz').1 (region hz hz').2).comp z (dr hz).differentiableAt
  · intro z hz hz'
    exact image _ (region hz hz').1 (region hz hz').2
  · intro z hz w hw he
    exact inv_injective (inj (region hz.1 hz.2) (region hw.1 hw.2) he)
  · intro z hz hz'
    obtain ⟨c,hc⟩ := conf _ (region hz hz').1 (region hz hz').2
    let a : ℂ := -(z^2)⁻¹
    refine ⟨c*‖a‖^2,fun v => ?_⟩
    have de : fderiv ℝ (Y ∘ Inv.inv) z v=fderiv ℝ Y z⁻¹ (v*a) :=
      congrArg (fun L : ℂ →L[ℝ] HelicoidTubeCoordinates => L v)
        (((diff _ (region hz hz').1 (region hz hz').2).hasFDerivAt.comp z (dr hz)).fderiv)
    rw [de,hc,norm_mul,mul_pow]
    ring
  · intro B
    obtain ⟨s,hs,hB⟩ := esc B
    have sPos := hr.trans hs
    refine ⟨s⁻¹,(inv_lt_inv₀ sPos hr).mpr hs,?_⟩
    intro z hz hz'
    have zPos := (inv_pos.mpr sPos).trans hz
    exact hB z⁻¹ (by rw [norm_inv]; exact (lt_inv_comm₀ hr zPos).mpr hz')
      (by rw [norm_inv]; exact (inv_lt_comm₀ zPos sPos).mpr hz)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidC1End.inner_radius_zero
