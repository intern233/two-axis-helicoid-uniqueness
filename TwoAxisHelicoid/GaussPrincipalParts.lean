import TwoAxisHelicoid.ZetaDifferenceLattice
import TwoAxisHelicoid.ZetaPoleRegular

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology
attribute [local irreducible] thetaZeta thetaSigma thetaEtaExpression
set_option maxHeartbeats 1200000

def gaussLogPoleSet (L : PeriodPair) (a : ℂ) : Set ℂ := latticePoleSet L {0,a,-a}

theorem not_mem_gaussLogPoleSet (L : PeriodPair) (a z : ℂ) :
    z ∉ gaussLogPoleSet L a ↔ z ∉ L.lattice ∧ z-a ∉ L.lattice ∧ z+a ∉ L.lattice := by
  simp [gaussLogPoleSet,latticePoleSet,sub_neg_eq_add,not_or]

theorem thetaZeta_analyticAt_of_pos {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : z ∉ (rhombicPeriodPair t ht).lattice) : AnalyticAt ℂ (thetaZeta t) z := by
  have hd : DifferentiableOn ℂ (thetaZeta t) (rhombicPeriodPair t ht).latticeᶜ :=
    fun w hw => (thetaZeta_hasDerivAt_of_pos ht ht hw).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (rhombicPeriodPair t ht).isClosed_lattice.isOpen_compl z hz

/-- Comparing the genuine local principal parts of a periodic meromorphic
coefficient produces its global Gauss differential form. The principal
parts are a residue-free double pole at zero and residues `+1,-1` at `a,-a`.
The additive constant is proved to exist, not assumed in the input. -/
theorem gauss_log_differential_principal_parts {t : ℝ} (ht : 0 < t) {a κ : ℂ}
    (ha : a ∉ (rhombicPeriodPair t ht).lattice)
    (h2a : 2*a ∉ (rhombicPeriodPair t ht).lattice)
    {f g₀ gPos gNeg : ℂ → ℂ}
    (hf : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a, AnalyticAt ℂ f z)
    (hp : ∀ z ω, ω ∈ (rhombicPeriodPair t ht).lattice →
      z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a → f (z+ω) = f z)
    (hg₀ : AnalyticAt ℂ g₀ 0) (hgPos : AnalyticAt ℂ gPos a) (hgNeg : AnalyticAt ℂ gNeg (-a))
    (he₀ : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = κ/z^2+g₀ z)
    (hePos : ∀ᶠ z in 𝓝[≠] a, f z = (z-a)⁻¹+gPos z)
    (heNeg : ∀ᶠ z in 𝓝[≠] (-a), f z = -(z+a)⁻¹+gNeg z) :
    ∃ β : ℂ, ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      f z = κ*(rhombicPeriodPair t ht).weierstrassP z+β+
        thetaZeta t (z-a)-thetaZeta t (z+a) := by
  let L := rhombicPeriodPair t ht
  let A : Set ℂ := {0,a,-a}
  have hA : A.Finite := by simp [A]
  have hna : -a ∉ L.lattice := fun h => ha (by simpa only [neg_neg] using L.lattice.neg_mem h)
  have hn2a : -(2*a) ∉ L.lattice :=
    fun h => h2a (by simpa only [neg_neg] using L.lattice.neg_mem h)
  let F : ℂ → ℂ := fun z => f z-κ*L.weierstrassP z-
    (thetaZeta t (z-a)-thetaZeta t (z+a))
  have hregular (z : ℂ) (hz : z ∉ latticePoleSet L A) :
      z ∉ L.lattice ∧ z-a ∉ L.lattice ∧ z+a ∉ L.lattice :=
    (not_mem_gaussLogPoleSet L a z).mp hz
  have hF : ∀ z ∉ latticePoleSet L A, AnalyticAt ℂ F z := by
    intro z hz
    obtain ⟨hz₀,hzPos,hzNeg⟩ := hregular z hz
    exact ((hf z hz).sub (analyticAt_const.mul (L.analyticOnNhd_weierstrassP z hz₀))).sub
      (((thetaZeta_analyticAt_of_pos ht hzPos).comp (f := fun w : ℂ => w-a) (by fun_prop)).sub
        ((thetaZeta_analyticAt_of_pos ht hzNeg).comp (f := fun w : ℂ => w+a) (by fun_prop)))
  have hperiod : ∀ z ω, ω ∈ L.lattice → z ∉ latticePoleSet L A → F (z+ω) = F z := by
    intro z ω hω hz
    obtain ⟨_,hm,hn⟩ := hregular z hz
    dsimp only [F]
    rw [hp z ω hω hz,L.weierstrassP_add_coe z (⟨ω,hω⟩ : L.lattice),
      zetaDifference_add_lattice ht hω hm hn]
  have hloc : ∀ b ∈ A, ∃ g : ℂ → ℂ, AnalyticAt ℂ g b ∧ F =ᶠ[𝓝[≠] b] g := by
    intro b hb
    have hb' : b=0 ∨ b=a ∨ b= -a := by simpa only [A,mem_insert_iff,mem_singleton_iff] using hb
    rcases hb' with hb0 | hba | hbna
    · subst b
      refine ⟨fun z => g₀ z-κ*L.weierstrassPExcept 0 z-
        (thetaZeta t (z-a)-thetaZeta t (z+a)),?_,?_⟩
      · have hm : AnalyticAt ℂ (fun z : ℂ => thetaZeta t (z-a)) 0 := by
          have h : AnalyticAt ℂ (thetaZeta t) (0-a) := by
            simpa only [zero_sub] using thetaZeta_analyticAt_of_pos ht hna
          exact h.comp (f := fun z : ℂ => z-a) (by fun_prop)
        have hn : AnalyticAt ℂ (fun z : ℂ => thetaZeta t (z+a)) 0 := by
          have h : AnalyticAt ℂ (thetaZeta t) (0+a) := by
            simpa only [zero_add] using thetaZeta_analyticAt_of_pos ht ha
          exact h.comp (f := fun z : ℂ => z+a) (by fun_prop)
        exact (hg₀.sub (analyticAt_const.mul (L.analyticAt_weierstrassPExcept 0))).sub (hm.sub hn)
      · filter_upwards [he₀] with z hz
        have hwp : L.weierstrassP z = 1/z^2+L.weierstrassPExcept 0 z := by
          simpa only [Submodule.coe_zero,sub_zero,zero_pow (by decide : 2 ≠ 0),div_zero,add_comm]
            using (L.weierstrassPExcept_add (0 : L.lattice) z).symm
        dsimp only [F]
        rw [hz,hwp]
        ring
    · subst b
      refine ⟨fun z => gPos z-κ*L.weierstrassP z-zetaPoleRegular t (z-a)+thetaZeta t (z+a),?_,?_⟩
      · have hr : AnalyticAt ℂ (fun z : ℂ => zetaPoleRegular t (z-a)) a := by
          have h : AnalyticAt ℂ (zetaPoleRegular t) (a-a) :=
            zetaPoleRegular_analyticAt ht (Or.inr (sub_self a))
          exact h.comp (f := fun z : ℂ => z-a) (by fun_prop)
        have hn : AnalyticAt ℂ (fun z : ℂ => thetaZeta t (z+a)) a := by
          have h : AnalyticAt ℂ (thetaZeta t) (a+a) :=
            thetaZeta_analyticAt_of_pos ht (by simpa only [two_mul] using h2a)
          exact h.comp (f := fun z : ℂ => z+a) (by fun_prop)
        exact ((hgPos.sub (analyticAt_const.mul (L.analyticOnNhd_weierstrassP a ha))).sub hr).add hn
      · filter_upwards [hePos,latticePoleSet_punctured_avoids L hA a] with z hz hn
        dsimp only [F]
        rw [hz,thetaZeta_eq_inv_add_regular ht (hregular z hn).2.1]
        ring
    · subst b
      refine ⟨fun z => gNeg z-κ*L.weierstrassP z-thetaZeta t (z-a)+zetaPoleRegular t (z+a),?_,?_⟩
      · have hr : AnalyticAt ℂ (fun z : ℂ => zetaPoleRegular t (z+a)) (-a) := by
          have h : AnalyticAt ℂ (zetaPoleRegular t) (-a+a) :=
            zetaPoleRegular_analyticAt ht (Or.inr (neg_add_cancel a))
          exact h.comp (f := fun z : ℂ => z+a) (by fun_prop)
        have hm : AnalyticAt ℂ (fun z : ℂ => thetaZeta t (z-a)) (-a) := by
          have h : AnalyticAt ℂ (thetaZeta t) (-a-a) :=
            thetaZeta_analyticAt_of_pos ht (by rw [show -a-a = -(2*a) by ring]; exact hn2a)
          exact h.comp (f := fun z : ℂ => z-a) (by fun_prop)
        exact ((hgNeg.sub (analyticAt_const.mul (L.analyticOnNhd_weierstrassP (-a) hna))).sub hm).add hr
      · filter_upwards [heNeg,latticePoleSet_punctured_avoids L hA (-a)] with z hz hn
        dsimp only [F]
        rw [hz,thetaZeta_eq_inv_add_regular ht (hregular z hn).2.2]
        ring
  obtain ⟨β,hβ⟩ := elliptic_finite_principal_parts_constant L hA hF hperiod hloc
  refine ⟨β,?_⟩
  intro z hz
  have he := hβ z hz
  dsimp only [F] at he
  linear_combination he

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.gauss_log_differential_principal_parts
