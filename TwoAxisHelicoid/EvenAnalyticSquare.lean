import TwoAxisHelicoid.EvenTaylorFourth
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace TwoAxisHelicoid
set_option maxHeartbeats 200000
open Filter FormalMultilinearSeries
open scoped Topology NNReal ENNReal

/-- An even real analytic germ descends to the square of its argument. -/
theorem even_analytic_factor_square {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (he : (fun x : ℝ => f (-x)) =ᶠ[𝓝 0] f) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ (∀ᶠ x in 𝓝 0, f x = g (x^2)) := by
  let c : ℕ → ℝ := fun n => iteratedDeriv n f 0/n.factorial
  let p := FormalMultilinearSeries.ofScalars ℝ c
  let q := FormalMultilinearSeries.ofScalars ℝ (fun n => c (2*n))
  have hp : HasFPowerSeriesAt f p 0 := hf.hasFPowerSeriesAt
  have hodd (n : ℕ) : c (2*n+1) = 0 := by
    have hh := he.iteratedDeriv_eq (2*n+1)
    rw [iteratedDeriv_comp_neg] at hh
    have hn : Odd (2*n+1) := ⟨n,by omega⟩
    simp only [neg_zero,hn.neg_one_pow,neg_one_smul] at hh
    have hz : iteratedDeriv (2*n+1) f 0 = 0 := by linarith
    simp only [c,hz,zero_div]
  obtain ⟨r,hr0,hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.radius_pos
  have hrpos : 0 < r := by exact_mod_cast hr0
  obtain ⟨C,_hC,hbound⟩ := p.norm_mul_pow_le_of_lt_radius hr
  have hqr : ((r^2:ℝ≥0):ℝ≥0∞) ≤ q.radius := by
    apply q.le_radius_of_bound C
    intro n
    simpa only [p,q,FormalMultilinearSeries.ofScalars_norm,NNReal.coe_pow,pow_mul] using hbound (2*n)
  have hqp : 0 < q.radius := lt_of_lt_of_le (by exact_mod_cast pow_pos hrpos 2) hqr
  refine ⟨q.sum,(q.hasFPowerSeriesOnBall hqp).analyticAt,?_⟩
  have hseries := hasFPowerSeriesAt_iff.mp hp
  filter_upwards [hseries] with x hx
  have hx' : HasSum (fun n : ℕ => x^n*c n) (f x) := by
    simpa only [p,zero_add,FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul] using hx
  have heS : Summable (fun n : ℕ => x^(2*n)*c (2*n)) :=
    hx'.summable.comp_injective (i := fun n : ℕ => 2*n) (fun m n h => by dsimp only at h; omega)
  have hoS : HasSum (fun n : ℕ => x^(2*n+1)*c (2*n+1)) 0 := by
    simpa only [hodd,mul_zero] using (hasSum_zero : HasSum (fun _ : ℕ => (0:ℝ)) 0)
  have hsum : HasSum (fun n : ℕ => x^n*c n) ((∑' n : ℕ, x^(2*n)*c (2*n))+0) :=
    HasSum.even_add_odd (f := fun n : ℕ => x^n*c n) heS.hasSum hoS
  have hid : (∑' n : ℕ, x^(2*n)*c (2*n)) = f x := by
    simpa only [add_zero] using hsum.unique hx'
  rw [← hid]
  change _ = ∑' n : ℕ, q n (fun _ => x^2)
  apply tsum_congr
  intro n
  simp only [q,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul,pow_mul]
  ring

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.even_analytic_factor_square
