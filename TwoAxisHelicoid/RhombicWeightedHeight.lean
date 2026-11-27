import TwoAxisHelicoid.RhombicClosedAxisCell
import TwoAxisHelicoid.RhombicPhysicalAxisPreimages

namespace TwoAxisHelicoid
open Set Complex Filter Topology
open scoped Topology ComplexConjugate

/-- Bounded height multiplied by a factor vanishing at the two infinite
corners. The zero set away from those corners is the genuine zero-height
set of the immersion. -/
noncomputable def rhombicCellWeight (t : ℝ) (z : ℂ) : ℝ :=
  (z.im-z.re)*(t+1-(z.im-z.re))

noncomputable def rhombicWeightedHeight (t : ℝ) (X : ℂ → Fin 3 → ℝ) (z : ℂ) : ℝ :=
  rhombicCellWeight t z*(X z 2/(1+|X z 2|))

private theorem weight_continuous (t : ℝ) : Continuous (rhombicCellWeight t) := by
  unfold rhombicCellWeight
  fun_prop

theorem rhombicCellWeight_pos {t : ℝ} {z : ℂ} (hz : z ∈ regularClosedRhombicAxisCell t) :
    0<rhombicCellWeight t z := mul_pos hz.2.1 (sub_pos.mpr hz.2.2)

theorem rhombicWeightedHeight_zero_iff {t : ℝ} {z : ℂ} (hz : z ∈ regularClosedRhombicAxisCell t)
    (X : ℂ → Fin 3 → ℝ) : rhombicWeightedHeight t X z=0 ↔ X z 2=0 := by
  have den : 1+|X z 2|≠0 := by positivity
  rw [rhombicWeightedHeight,mul_eq_zero,or_iff_right (rhombicCellWeight_pos hz).ne',div_eq_zero_iff,or_iff_left den]

theorem rhombicWeightedHeight_continuousOn {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X) :
    ContinuousOn (rhombicWeightedHeight t X) (closedRhombicAxisCell t) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  by_cases good : z ∉ (rhombicPeriodPair t ht).lattice
  · have cx : ContinuousAt (fun w => X w 2) z := (continuous_apply (2 : Fin 3)).continuousAt.comp (hX.differentiable z good).continuousAt
    exact (weight_continuous t).continuousAt.mul (cx.div (continuousAt_const.add cx.abs) (by positivity))
  have puncture := (closedRhombicAxisCell_lattice_points ht hz).mp (not_not.mp good)
  have zero : rhombicCellWeight t z=0 := by
    rcases puncture with rfl | rfl <;> simp [rhombicCellWeight]
  have atz : rhombicWeightedHeight t X z=0 := by simp [rhombicWeightedHeight,zero]
  unfold ContinuousAt
  rw [atz]
  have lim : Tendsto (fun w => |rhombicCellWeight t w|) (𝓝 z) (𝓝 0) := by
    simpa only [zero,abs_zero] using ((weight_continuous t).continuousAt (x := z)).abs.tendsto
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [lim.eventually_lt_const hε] with w hw
  rw [Real.dist_eq,sub_zero,rhombicWeightedHeight,abs_mul]
  have d : 0<1+|X w 2| := by positivity
  have ratio : |X w 2/(1+|X w 2|)|≤1 := by
    rw [abs_div,abs_of_pos d,div_le_one d]
    linarith
  exact (mul_le_of_le_one_right (abs_nonneg _) ratio).trans_lt hw

theorem rhombicCell_middle_regular {t : ℝ} (ht : 0<t) (p : unitInterval × unitInterval)
    (mid : (0:ℝ)<p.2 ∧ (p.2:ℝ)<1) : rhombicCellPoint t p ∈ regularClosedRhombicAxisCell t := by
  have cell := rhombicCellPoint_mem ht p
  refine ⟨cell,?_,?_⟩
  · change 0<t*(p.2:ℝ)-((p.1:ℝ)-1)
    linarith [mul_pos ht mid.1,p.1.2.2]
  · change t*(p.2:ℝ)-((p.1:ℝ)-1)<t+1
    linarith [mul_lt_of_lt_one_right ht mid.2,p.1.2.1]

private theorem no_integral_height_between {t v : ℝ} (ht : 0<t) (h₀ : 0<v) (h₁ : v<1) :
    ¬ ∃ k : ℤ, t*v=k*t := by
  rintro ⟨k,e⟩
  have eq : v=(k:ℝ) := mul_right_cancel₀ ht.ne' (by simpa [mul_comm t v] using e)
  have low : (0:ℤ)<k := by exact_mod_cast (eq ▸ h₀)
  have high : k<(1:ℤ) := by exact_mod_cast (eq ▸ h₁)
  omega

/-- The regular points of the open horizontal strip cannot lie on the
physical horizontal axis. The actual weighted height on each open
vertical edge is nonzero. -/
theorem rhombic_middle_avoids_horizontal_axis {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hi : Function.Injective (harmonicTorusImmersion hX)) (p : unitInterval × unitInterval)
    (mid : (0:ℝ)<p.2 ∧ (p.2:ℝ)<1) :
    let z := rhombicCellPoint t p
    ¬ (X z 1=0 ∧ X z 2=0) ∧ (p.1=0 ∨ p.1=1 →
      rhombicWeightedHeight t X z≠0) := by
  let z := rhombicCellPoint t p
  have good := rhombicCell_middle_regular ht p mid
  have axes := rhombic_physical_axes_preimages ht hX hi ((regularClosedRhombicAxisCell_iff ht _).mp good).2
  have no : ¬ (X z 1=0 ∧ X z 2=0) := fun h => no_integral_height_between ht mid.1 mid.2 (axes.2.mp h)
  refine ⟨no,fun edge zero => ?_⟩
  have int : ∃ k : ℤ, z.re=k := by
    rcases edge with l | r
    · exact ⟨-1,by simp [z,rhombicCellPoint,l]⟩
    · exact ⟨0,by simp [z,rhombicCellPoint,r]⟩
  exact no ⟨(axes.1.mpr int).2,(rhombicWeightedHeight_zero_iff good X).mp zero⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombicWeightedHeight_continuousOn
#print axioms TwoAxisHelicoid.rhombic_middle_avoids_horizontal_axis
