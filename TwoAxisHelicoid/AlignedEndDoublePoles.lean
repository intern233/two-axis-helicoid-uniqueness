import TwoAxisHelicoid.AlignedGaussLogGerm

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology
set_option maxHeartbeats 1500000

noncomputable def immersionGaussMap (X : ℂ → Fin 3 → ℝ) (z : ℂ) : ℂ :=
  nullGauss (immersionComplexCoefficient X z)

noncomputable def immersionGaussLogDerivative (X : ℂ → Fin 3 → ℝ) (z : ℂ) : ℂ :=
  deriv (immersionGaussMap X) z/immersionGaussMap X z

theorem immersionGaussMap_differentiableAt_of_coefficients {X : ℂ → Fin 3 → ℝ} {z : ℂ}
    (ha : ∀ j, AnalyticAt ℂ (fun w => immersionComplexCoefficient X w j) z)
    (hp : ComplexNull (immersionComplexCoefficient X z)) (h₂ : immersionComplexCoefficient X z 2 ≠ 0) :
    DifferentiableAt ℂ (immersionGaussMap X) z ∧ immersionGaussMap X z ≠ 0 := by
  have hn := (null_horizontal_nonzero_of_height hp h₂).1
  constructor
  · exact (ha 2).differentiableAt.div
      ((ha 0).differentiableAt.sub ((ha 1).differentiableAt.const_mul I)) hn
  · exact div_ne_zero h₂ hn

/-- Directions aligned by positional asymptotics give the same two pole
orders in the original frame. The Gauss gauge is derived from the
actual immersion using its Euclidean change of coordinates. -/
theorem asymptotic_helicoid_actual_end_double_poles {S : Set (Fin 3 → ℝ)}
    (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (hL : ∀ u v, L u ⬝ᵥ L v = u ⬝ᵥ v)
    (P : Fin 3 → ℝ) (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (h₁ : ApproachesSetAtInfinity ((fun p => P+L p) '' range (axisRuledHelicoid I β 0)) S)
    (h₂ : ApproachesSetAtInfinity S (range (axisRuledHelicoid I α 0)))
    (X : ℂ → Fin 3 → ℝ) (z : ℂ)
    (hX : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℝ X w ∧ ComplexNull (immersionComplexCoefficient X w) ∧
      ∀ j, AnalyticAt ℂ (fun y => immersionComplexCoefficient X y j) w)
    (hmh : MeromorphicAt (fun w => immersionComplexCoefficient X w 2) z)
    (hoh : meromorphicOrderAt (fun w => immersionComplexCoefficient X w 2) z = -2)
    (hmg : MeromorphicAt (immersionGaussLogDerivative X) z)
    (hog : meromorphicOrderAt (immersionGaussLogDerivative X) z = -2) :
    let Y := fun w => P+L (X w)
    MeromorphicAt (fun w => immersionComplexCoefficient Y w 2) z ∧
      meromorphicOrderAt (fun w => immersionComplexCoefficient Y w 2) z = -2 ∧
      MeromorphicAt (immersionGaussLogDerivative Y) z ∧
      meromorphicOrderAt (immersionGaussLogDerivative Y) z = -2 := by
  let Y := fun w => P+L (X w)
  have haxis := helicoid_axis_alignment_through_surface L hL P α β hα hβ h₁ h₂
  obtain ⟨a,b,t,e,hab,ht,he,hcoef⟩ := aligned_orthogonal_immersion_coefficients L P hL haxis
  have hen : (e:ℂ) ≠ 0 := by rcases he with he | he <;> rw [he] <;> norm_num
  have hh : (fun w => immersionComplexCoefficient Y w 2) =ᶠ[𝓝[≠] z]
      fun w => (e:ℂ)*immersionComplexCoefficient X w 2 := by
    filter_upwards [hX] with w hw
    exact congrFun (hcoef X w hw.1) 2
  have hhn : ∀ᶠ w in 𝓝[≠] z, immersionComplexCoefficient X w 2 ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmh).mp (by rw [hoh]; norm_num)
  have hd : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ (immersionGaussMap X) w ∧ immersionGaussMap X w ≠ 0 := by
    filter_upwards [hX,hhn] with w hw hn
    exact immersionGaussMap_differentiableAt_of_coefficients hw.2.2 hw.2.1 hn
  let u := (e:ℂ)/((a:ℂ)-I*b)
  have hun : u ≠ 0 := div_ne_zero hen (aligned_horizontal_unit_ne_zero hab)
  have hgg : ∃ d : ℂ, d ≠ 0 ∧ ((immersionGaussMap Y =ᶠ[𝓝[≠] z] fun w => d*immersionGaussMap X w) ∨
      (immersionGaussMap Y =ᶠ[𝓝[≠] z] fun w => d/immersionGaussMap X w)) := by
    rcases ht with ht | ht
    · refine ⟨u,hun,Or.inl ?_⟩
      filter_upwards [hX,hhn] with w hw hn
      exact (aligned_nullGauss_formula a b t e (hcoef X w hw.1) hw.2.1 hn hab).1 ht
    · refine ⟨-u,neg_ne_zero.mpr hun,Or.inr ?_⟩
      filter_upwards [hX,hhn] with w hw hn
      exact (aligned_nullGauss_formula a b t e (hcoef X w hw.1) hw.2.1 hn hab).2 ht
  obtain ⟨d,hdn,hg⟩ := hgg
  obtain ⟨s,hsn,hs⟩ := gauss_log_gauge_germ hdn hd hg
  have hh' := meromorphicOrderAt_of_punctured_constant_multiple hen hmh hh
  have hg' := meromorphicOrderAt_of_punctured_constant_multiple (f := immersionGaussLogDerivative X)
    (g := immersionGaussLogDerivative Y) hsn hmg hs
  exact ⟨hh'.1,hh'.2.trans hoh,hg'.1,hg'.2.trans hog⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.asymptotic_helicoid_actual_end_double_poles
