import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace TwoAxisHelicoid
open Complex Real Set Filter
open scoped Topology

/-- An unwrapped continuous angle on a connected set which avoids
one fixed circle direction stays between two finite multiples of 2π. -/
theorem bounded_angle_avoiding_one {α : Type*} [TopologicalSpace α] {S : Set α} (con : IsPreconnected S)
    {f : α → ℝ} (cf : ContinuousOn f S) (avoid : ∀ x∈S, Complex.exp ((f x:ℂ)*I)≠1) :
    ∃ B : ℝ, 0≤B ∧ ∀ x∈S, |f x|≤B := by
  rcases S.eq_empty_or_nonempty with em|⟨x,hx⟩
  · exact ⟨0,le_rfl,by simp [em]⟩
  obtain ⟨n,hn⟩ := exists_nat_gt (|f x|+1)
  let B := (n:ℝ)*(2*π)
  have p : 0≤B := by dsimp [B]; positivity
  have b : |f x|<B := by
    dsimp [B]
    have nn : (0:ℝ)≤n := Nat.cast_nonneg _
    nlinarith [Real.pi_gt_three,mul_nonneg nn (by linarith [Real.pi_gt_three] : 0≤2*π-1)]
  have pos : Complex.exp ((B:ℂ)*I)=1 := by
    simpa [B,mul_assoc] using Complex.exp_int_mul_two_pi_mul_I (n:ℤ)
  have neg : Complex.exp (((-B:ℝ):ℂ)*I)=1 := by rw [ofReal_neg,neg_mul,Complex.exp_neg,pos,inv_one]
  have no (a : ℝ) (ha : Complex.exp ((a:ℂ)*I)=1) : a∉f '' S := by
    rintro ⟨u,hu,rfl⟩
    exact avoid u hu ha
  have ci := con.image f cf
  have xb := abs_lt.mp b
  refine ⟨B,p,fun u hu => abs_le.mpr ⟨?_,?_⟩⟩
  · by_contra! lt
    exact no (-B) neg (ci.Icc_subset (mem_image_of_mem f hu) (mem_image_of_mem f hx) ⟨lt.le,xb.1.le⟩)
  · by_contra! lt
    exact no B pos (ci.Icc_subset (mem_image_of_mem f hx) (mem_image_of_mem f hu) ⟨xb.2.le,lt.le⟩)

theorem positive_imaginary_ray_tendsto :
    Tendsto (fun y : ℝ => (y:ℂ)*I) (𝓝[>] (0:ℝ)) (𝓝[≠] (0:ℂ)) := by
  have c : Continuous (fun y : ℝ => (y:ℂ)*I) := Complex.continuous_ofReal.mul continuous_const
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · simpa only [Complex.ofReal_zero,zero_mul] using c.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  · filter_upwards [self_mem_nhdsWithin] with y hy using mul_ne_zero (Complex.ofReal_ne_zero.mpr (show 0<y from hy).ne') I_ne_zero

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.bounded_angle_avoiding_one
