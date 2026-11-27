import TwoAxisHelicoid.MarkedHelicoidHeightPole
import TwoAxisHelicoid.HelicoidGraphSpatialGrowth
import TwoAxisHelicoid.ExponentialHeightDerivative
import TwoAxisHelicoid.EvenPuncturedPrimitive
import TwoAxisHelicoid.GaussMultiplierContinuation

namespace TwoAxisHelicoid
open Complex Set Filter Metric Bornology
open scoped Topology

theorem null_gauss_both_norm_bounds {p : Fin 3 → ℂ} (hp : ComplexNull p) (height : 1≤‖p 2‖) :
    ‖nullGauss p‖≤‖p 0‖+‖p 1‖ ∧ ‖(nullGauss p)⁻¹‖≤‖p 0‖+‖p 1‖ := by
  have nz := norm_pos_iff.mp (zero_lt_one.trans_le height)
  have eq := nullGauss_mul_height hp nz
  have norm (g : ℂ) : ‖g‖≤‖g*p 2‖ := by rw [norm_mul]; simpa only [mul_one] using mul_le_mul_of_nonneg_left height (norm_nonneg g)
  have ip : ‖I*p 1‖=‖p 1‖ := by rw [norm_mul,Complex.norm_I,one_mul]
  constructor
  · exact (norm _).trans ((by rw [eq.1,norm_neg]; exact (norm_add_le _ _).trans_eq (by rw [ip])) :
      ‖nullGauss p*p 2‖≤_)
  · exact (norm _).trans ((by rw [eq.2]; exact (norm_sub_le _ _).trans_eq (by rw [ip])) :
      ‖(nullGauss p)⁻¹*p 2‖≤_)

private theorem component_bound (v : Fin 3 → ℝ) (j : Fin 3) : |v j|≤‖coordinateToTube v‖ := by
  change |v j|≤max (max ‖v 0‖ ‖v 1‖) ‖v 2‖
  simp only [Real.norm_eq_abs]
  fin_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

/-- For an actual proper marked harmonic C¹ helicoidal immersion, the
Gauss map has a single-valued meromorphic logarithm near the puncture.
Its finite order follows from the graph's area distortion and the
horizontal coordinate functions. -/
theorem marked_helicoid_meromorphic_gauss_log {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (proper : IsProperMap (harmonicTorusImmersion hX))
    (graph : HasHelicoidC1End (coordinateToTube ∘ harmonicTorusImmersion hX)) :
    let p := puncturedImmersionCoefficient (rhombicPeriodPair t ht) X
    let g := fun z => nullGauss (p z)
    ∃ F : ℂ → ℂ, MeromorphicAt F 0 ∧ ∀ᶠ z in 𝓝[≠] (0:ℂ),
      HasDerivAt F (logDeriv g z) z ∧ Complex.exp (F z)=g z := by
  let L := rhombicPeriodPair t ht
  let p := puncturedImmersionCoefficient L X
  let g := fun z => nullGauss (p z)
  let := punctured_complex_curve_noncompact (0:PeriodTorus L)
  let : LocallyCompactSpace (PuncturedPeriodTorus L) := ChartedSpace.locallyCompactSpace ℂ _
  obtain ⟨E,eq,sm,iso⟩ := hX.standard_end_chart
  obtain ⟨N,_,C,hC,sp⟩ := graph.isothermal_spatial_growth (coordinateToTube_isProperMap proper) E sm iso
  have spatial : ∀ᶠ z in 𝓝[≠] (0:ℂ), ∀ j : Fin 3, |X z j|≤2*Real.exp (C/‖z‖^N) := by
    filter_upwards [eq,sp] with z e bd j
    exact (component_bound _ j).trans ((congrArg norm e).symm.trans_le bd)
  have hp := hX.null_differential (fun _ hz => rhombic_conj_mem ht hz)
  obtain ⟨_,ord⟩ := marked_helicoid_height_double_pole ht hX proper graph
  have neg : meromorphicOrderAt (fun z => p z 2) 0<0 := by rw [ord]; exact_mod_cast (by decide : (-2:ℤ)<0)
  have big : ∀ᶠ z in 𝓝[≠] (0:ℂ), 1≤‖p z 2‖ := (tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_of_meromorphicOrderAt_neg neg)).eventually_ge_atTop 1
  have reg : ∀ᶠ z in 𝓝[≠] (0:ℂ), AnalyticAt ℂ g z ∧ g z≠0 ∧ logDeriv g (-z)=logDeriv g z := by
    filter_upwards [big,punctured_lattice_regular_near_zero L] with z b hz
    have hn := norm_pos_iff.mp (zero_lt_one.trans_le b)
    have an := fun j => puncturedImmersionCoefficient_analyticAt hX hz j
    exact ⟨nullGauss_analyticAt_of_height an (hp.null z hz) hn,nullGauss_ne_zero_of_height (hp.null z hz) hn,
      null_gauss_log_derivative_neg hp (fun _ h j => puncturedImmersionCoefficient_analyticAt hX h j) hz hn⟩
  obtain ⟨r,hr,hrg⟩ := Metric.mem_nhdsWithin_iff.mp reg
  have rg (z : ℂ) (nz : 0<‖z‖) (small : ‖z‖<r) := hrg (show z∈ball (0:ℂ) r ∩ {0}ᶜ from
    ⟨by rwa [mem_ball,dist_zero_right],norm_pos_iff.mp nz⟩)
  obtain ⟨F,fd⟩ := punctured_log_of_even_log_derivative (g := g) hr
    (fun z nz s => ⟨(rg z nz s).1,(rg z nz s).2.1⟩) (fun z nz s => (rg z nz s).2.2)
  have fEv : ∀ᶠ z in 𝓝[≠] (0:ℂ), HasDerivAt F (logDeriv g z) z ∧ Complex.exp (F z)=g z := by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) hr)] with z nz small
    exact fd z (norm_pos_iff.mpr nz) (by simpa only [mem_ball,dist_zero_right] using small)
  let B := 16*2+2^N*C
  have coeff (j : Fin 3) : ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖p z j‖≤Real.exp (B/‖z‖^(N+1)) := by
    obtain ⟨H,d⟩ := hX.complex_coordinate_primitive ht j
    obtain ⟨R,hR,hg⟩ := Metric.mem_nhdsWithin_iff.mp (spatial.and (punctured_lattice_regular_near_zero L))
    have get (z : ℂ) (nz : 0<‖z‖) (small : ‖z‖<R) := hg (show z∈ball (0:ℂ) R ∩ {0}ᶜ from
      ⟨by rwa [mem_ball,dist_zero_right],norm_pos_iff.mp nz⟩)
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) (half_pos hR)),
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one),punctured_lattice_regular_near_zero L] with z nz small one off
    have est := derivative_of_exponential_real_growth (H := H) hC (by norm_num : (0:ℝ)<2) N
      (fun w n h => (d w (get w n h).2).1.differentiableAt) (fun w n h => by
        rw [(d w (get w n h).2).2]; exact (get w n h).1 j) (norm_pos_iff.mpr nz)
      (by simpa only [mem_ball,dist_zero_right] using small) (by exact (show ‖z‖<1 by simpa only [mem_ball,dist_zero_right] using one).le)
    rwa [(d z off).1.deriv] at est
  have realBound : ∀ᶠ z in 𝓝[≠] (0:ℂ), |(F z).re|≤(B+2)/‖z‖^(N+1) := by
    filter_upwards [fEv,coeff 0,coeff 1,big,punctured_lattice_regular_near_zero L,self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one)] with z hd a b h hz nz small
    let s := ‖z‖^(N+1)
    have ns : 0<s := pow_pos (norm_pos_iff.mpr nz) _
    have small' : ‖z‖<1 := by simpa only [mem_ball,dist_zero_right] using small
    have us : s≤1 := pow_le_one₀ (norm_nonneg _) small'.le
    have al := null_gauss_both_norm_bounds (hp.null z hz) h
    have up : ‖p z 0‖+‖p z 1‖≤Real.exp ((B+2)/s) := by
      apply (add_le_add a b).trans
      calc
        _ = 2*Real.exp (B/s) := (two_mul _).symm
        _ ≤ Real.exp 2*Real.exp (B/s) := mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp 2]) (Real.exp_pos _).le
        _ ≤ _ := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          calc
            2+B/s ≤ 2/s+B/s := add_le_add_left ((le_div_iff₀ ns).mpr (by linarith)) _
            _ = (B+2)/s := by ring
    have plus := al.1.trans up
    have minus := al.2.trans up
    change ‖g z‖≤_ at plus
    change ‖(g z)⁻¹‖≤_ at minus
    rw [← hd.2,Complex.norm_exp,Real.exp_le_exp] at plus
    rw [← hd.2,← Complex.exp_neg,Complex.norm_exp,Complex.neg_re,Real.exp_le_exp] at minus
    exact abs_le.mpr ⟨by linarith,plus⟩
  obtain ⟨S,hS,germ⟩ := Metric.mem_nhdsWithin_iff.mp (fEv.and realBound)
  have get (z : ℂ) (nz : 0<‖z‖) (small : ‖z‖<S) := germ (show z∈ball (0:ℂ) S ∩ {0}ᶜ from
    ⟨by rwa [mem_ball,dist_zero_right],norm_pos_iff.mp nz⟩)
  refine ⟨F,meromorphic_of_polynomial_real_height hS (show 0<B+2 by dsimp [B]; positivity) (N+1)
    (fun z nz s => (get z nz s).1.1.differentiableAt) (fun z nz s => (get z nz s).2),fEv⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_helicoid_meromorphic_gauss_log
