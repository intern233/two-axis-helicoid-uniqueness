import TwoAxisHelicoid.PolynomialGaussLogFactor
import TwoAxisHelicoid.MarkedLogGaussGrowth

namespace TwoAxisHelicoid
open Complex Set Filter Metric InnerProductSpace
open scoped Topology

/-- Growth of the actual Cartesian coordinates controls the logarithmic
Gauss factor on a punctured disk. All estimates use only the three
local complex potentials and the pole order of the height. -/
theorem punctured_null_gauss_meromorphic_of_growth {X : ℂ → Fin 3 → ℝ} {N : ℕ} {C : ℝ} (hC : 0<C)
    (spatial : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∀ j, |X z j|≤2*Real.exp (C/‖z‖^N))
    (reg : ∀ᶠ z in 𝓝[≠] (0:ℂ), (∀ j, HarmonicAt (fun w => X w j) z) ∧ ConformalCoordinateDerivatives X z)
    (primitive : ∀ j, ∃ H : ℂ → ℂ, ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt H (immersionComplexCoefficient X z j) z ∧ (H z).re=X z j)
    (ord : meromorphicOrderAt (fun z => immersionComplexCoefficient X z 2) 0=(-2:ℤ)) :
    let g := immersionGaussMap X
    ∃ (n : ℤ) (F : ℂ → ℂ), MeromorphicAt F 0 ∧ MeromorphicAt (logDeriv g) 0 ∧
      ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (logDeriv g z-(n:ℂ)/z) z ∧ g z=z^n*exp (F z) := by
  intro g
  let p := immersionComplexCoefficient X
  have neg : meromorphicOrderAt (fun z => p z 2) 0<0 := by rw [ord]; exact_mod_cast (by decide : (-2:ℤ)<0)
  have big : ∀ᶠ z in 𝓝[≠] (0:ℂ), 1≤‖p z 2‖ := (tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_of_meromorphicOrderAt_neg neg)).eventually_ge_atTop 1
  have good : ∀ᶠ z in 𝓝[≠] (0:ℂ), AnalyticAt ℂ g z ∧ g z≠0 := by
    filter_upwards [big,reg] with z b off
    have nz := norm_pos_iff.mp (zero_lt_one.trans_le b)
    exact ⟨nullGauss_analyticAt_of_height (fun j => scalarComplexCoefficient_analyticAt (off.1 j)) (immersionComplexCoefficient_null off.2) nz,nullGauss_ne_zero_of_height (immersionComplexCoefficient_null off.2) nz⟩
  let B := 16*2+2^N*C
  have coeff (j : Fin 3) : ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖p z j‖≤Real.exp (B/‖z‖^(N+1)) := by
    obtain ⟨H,hd⟩ := primitive j
    obtain ⟨R,hR,sub⟩ := Metric.mem_nhdsWithin_iff.mp (spatial.and hd)
    have get (z : ℂ) (n : 0<‖z‖) (s : ‖z‖<R) := sub (show z∈ball (0:ℂ) R ∩ {0}ᶜ from
      ⟨by rwa [mem_ball,dist_zero_right],norm_pos_iff.mp n⟩)
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) (half_pos hR)),
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one),hd] with z nz small one dh
    have est := derivative_of_exponential_real_growth (H := H) hC (by norm_num : (0:ℝ)<2) N
      (fun w n s => (get w n s).2.1.differentiableAt) (fun w n s => by
        rw [(get w n s).2.2]; exact (get w n s).1 j) (norm_pos_iff.mpr nz)
      (by simpa only [mem_ball,dist_zero_right] using small) (show ‖z‖≤1 from (show ‖z‖<1 by simpa only [mem_ball,dist_zero_right] using one).le)
    rwa [dh.1.deriv] at est
  apply punctured_unit_meromorphic_log_factor (g := g) (show 0<B+2 by dsimp [B]; positivity) N good
  filter_upwards [coeff 0,coeff 1,big,good,reg,self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one)] with z a b h nz off n small
  let s := ‖z‖^(N+1)
  have hs : 0<s := pow_pos (norm_pos_iff.mpr n) _
  have us : s≤1 := pow_le_one₀ (norm_nonneg _) (show ‖z‖<1 by simpa only [mem_ball,dist_zero_right] using small).le
  have al := null_gauss_both_norm_bounds (immersionComplexCoefficient_null off.2) h
  have up : ‖p z 0‖+‖p z 1‖≤Real.exp ((B+2)/s) := by
    apply (add_le_add a b).trans
    calc
      _ = 2*Real.exp (B/s) := (two_mul _).symm
      _ ≤ Real.exp 2*Real.exp (B/s) := mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp 2]) (Real.exp_pos _).le
      _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        calc
          2+B/s ≤ 2/s+B/s := add_le_add_left ((le_div_iff₀ hs).mpr (by linarith)) _
          _ = (B+2)/s := by ring
  have gp := norm_pos_iff.mpr nz.2
  have plus := Real.log_le_log gp (al.1.trans up)
  have invBound : ‖(g z)⁻¹‖≤Real.exp ((B+2)/s) := al.2.trans up
  have minus := Real.log_le_log (inv_pos.mpr gp) (by simpa only [norm_inv] using invBound)
  rw [Real.log_exp] at plus
  rw [Real.log_inv,Real.log_exp] at minus
  exact abs_le.mpr ⟨by linarith,plus⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_null_gauss_meromorphic_of_growth
