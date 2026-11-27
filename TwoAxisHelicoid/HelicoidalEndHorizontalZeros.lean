import TwoAxisHelicoid.EllipticLogResidueObstruction
import TwoAxisHelicoid.NullGaussAlgebra

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- On any marked torus, one residue-free helicoidal Gauss end and an
order-two height pole force zeros of both horizontal characteristic forms.
Their locations are obtained on the actual punctured torus, without axes
or an assumption about the interior Gauss divisor. -/
theorem helicoidal_end_both_horizontal_characteristics_vanish (L : PeriodPair) (p : ℂ → Fin 3 → ℂ)
    (hhol : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hper : ∀ z ω, ω ∈ L.lattice → p (z+ω) = p z)
    (hnull : ∀ z ∉ L.lattice, ComplexNull (p z))
    (hh : meromorphicOrderAt (fun z => p z 2) 0 = (-2 : ℤ))
    {κ : ℂ} {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0)
    (hend : ∀ᶠ z in 𝓝[≠] (0:ℂ), logDeriv (nullGauss ∘ p) z = κ/z^2+R z) :
    (∃ a ∉ L.lattice, nullHorizontalMinus (p a) = 0) ∧
    (∃ b ∉ L.lattice, nullHorizontalPlus (p b) = 0) := by
  let H := fun z => p z 2
  let M := nullHorizontalMinus ∘ p
  let P := nullHorizontalPlus ∘ p
  let G := nullGauss ∘ p
  have hM (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℂ M z :=
    (hhol z hz 0).sub (analyticAt_const.mul (hhol z hz 1))
  have hP (z : ℂ) (hz : z ∉ L.lattice) : AnalyticAt ℂ P z :=
    (hhol z hz 0).add (analyticAt_const.mul (hhol z hz 1))
  have ho : meromorphicOrderAt H 0 = ((-2 : ℤ) : WithTop ℤ) := hh
  have hmero : MeromorphicAt H 0 := meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [ho]; decide)
  have hnH : ∀ᶠ z in 𝓝[≠] (0:ℂ), H z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmero).mp (by rw [ho]; decide)
  obtain ⟨S,hS,hs⟩ := meromorphic_log_derivative_residue_at_zero hmero ho
  have hreg : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∉ L.lattice := by
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),self_mem_nhdsWithin] with z hz hn
    exact fun h => hz ⟨h,hn⟩
  have heP : P =ᶠ[𝓝[≠] (0:ℂ)] fun z => -(G z*H z) := by
    filter_upwards [hreg,hnH] with z hz hn
    have e := null_horizontal_product (hnull z hz)
    have h := (null_horizontal_nonzero_of_height (hnull z hz) hn).1
    change nullHorizontalPlus (p z) = -(p z 2/nullHorizontalMinus (p z)*p z 2)
    field_simp [h]
    linear_combination e
  have ne : ((-2:ℤ):ℂ) ≠ 0 := by norm_num
  have both : ∀ᶠ z in 𝓝[≠] (0:ℂ),
      (logDeriv M z = (-κ)/z^2+((-2:ℤ):ℂ)/z+(S z-R z)) ∧
      (logDeriv P z = κ/z^2+((-2:ℤ):ℂ)/z+(S z+R z)) := by
    filter_upwards [hreg,hnH,hend,hs,logDeriv_congr_nhdsNE heP] with z hz hH hG hS' hp
    have nn : M z ≠ 0 := (null_horizontal_nonzero_of_height (hnull z hz) hH).1
    have dH : DifferentiableAt ℂ H z := (hhol z hz 2).differentiableAt
    have dM := (hM z hz).differentiableAt
    have dG : DifferentiableAt ℂ G z := dH.div dM nn
    have gne : G z ≠ 0 := div_ne_zero hH nn
    have em : logDeriv G z = logDeriv H z-logDeriv M z := logDeriv_fun_div z hH nn dH dM
    rw [logDeriv_neg,logDeriv_fun_mul z gne hH dG dH] at hp
    change logDeriv G z = _ at hG
    constructor
    · linear_combination hS' + em - hG
    · linear_combination hp + hG + hS'
  exact ⟨periodic_coefficient_has_zero_of_log_residue L M _ hM
    (fun z ω hω => congrArg nullHorizontalMinus (hper z ω hω)) (hS.sub hR)
    (both.mono fun _ h => h.1) ne,
    periodic_coefficient_has_zero_of_log_residue L P _ hP
    (fun z ω hω => congrArg nullHorizontalPlus (hper z ω hω)) (hS.add hR)
    (both.mono fun _ h => h.2) ne⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.helicoidal_end_both_horizontal_characteristics_vanish
