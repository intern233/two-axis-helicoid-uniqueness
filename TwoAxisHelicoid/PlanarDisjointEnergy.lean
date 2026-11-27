import TwoAxisHelicoid.PlanarEnergyStability
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace TwoAxisHelicoid
open Set MeasureTheory Function
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem sum_sq_of_pairwise_products_zero {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (h : Pairwise (fun i j => a i*a j = 0)) : (∑ i, a i)^2 = ∑ i, a i^2 := by
  classical
  rw [pow_two,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    exact h hji.symm
  · simp

theorem disjoint_tsupport_mul_eq_zero {f g : ℝ × ℝ → ℝ}
    (h : Disjoint (tsupport f) (tsupport g)) (p : ℝ × ℝ) : f p*g p = 0 := by
  by_cases hf : f p = 0
  · simp [hf]
  · have hg : g p = 0 := by
      by_contra hg
      exact Set.disjoint_left.mp h (subset_closure hf) (subset_closure hg)
    simp [hg]

theorem disjoint_tsupport_derivative_mul_eq_zero {f g : ℝ × ℝ → ℝ}
    (h : Disjoint (tsupport f) (tsupport g)) (p w : ℝ × ℝ) :
    fderiv ℝ f p w*fderiv ℝ g p w = 0 :=
  disjoint_tsupport_mul_eq_zero
    (h.mono (tsupport_fderiv_apply_subset ℝ w) (tsupport_fderiv_apply_subset ℝ w)) p

theorem planarQuadraticEnergy_disjoint_sum {ι : Type*} [Fintype ι]
    {W : ℝ × ℝ → ℝ} (hW : Continuous W) {v : ι → ℝ × ℝ → ℝ}
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) (hs : ∀ i, HasCompactSupport (v i))
    (hdis : Pairwise (fun i j => Disjoint (tsupport (v i)) (tsupport (v j)))) (c : ι → ℝ) :
    planarQuadraticEnergy W (fun p => ∑ i, c i*v i p) =
      ∑ i, c i^2*planarQuadraticEnergy W (v i) := by
  classical
  have hdf (p w : ℝ × ℝ) : fderiv ℝ (fun q => ∑ i, c i*v i q) p w =
      ∑ i, c i*fderiv ℝ (v i) p w := by
    have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (((hv i).differentiable (by simp)) p).hasFDerivAt.const_smul (c i))
    have he := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L w) hd.fderiv
    simpa [Pi.smul_apply,smul_eq_mul] using! he
  have hval (p : ℝ × ℝ) : (∑ i, c i*v i p)^2 = ∑ i, c i^2*v i p^2 := by
    rw [sum_sq_of_pairwise_products_zero (fun i => c i*v i p) (by
      intro i j hij
      have hh := disjoint_tsupport_mul_eq_zero (hdis hij) p
      calc
        _ = c i*c j*(v i p*v j p) := by ring
        _ = 0 := by rw [hh,mul_zero])]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hgrad (p w : ℝ × ℝ) :
      (∑ i, c i*fderiv ℝ (v i) p w)^2 = ∑ i, c i^2*(fderiv ℝ (v i) p w)^2 := by
    rw [sum_sq_of_pairwise_products_zero (fun i => c i*fderiv ℝ (v i) p w) (by
      intro i j hij
      have hh := disjoint_tsupport_derivative_mul_eq_zero (hdis hij) p w
      calc
        _ = c i*c j*(fderiv ℝ (v i) p w*fderiv ℝ (v j) p w) := by ring
        _ = 0 := by rw [hh,mul_zero])]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold planarQuadraticEnergy
  simp_rw [hdf,hgrad,hval,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    by
      have hh := (smooth_compact_planar_energy_integrable hW (hv i) (hs i)).const_mul (c i^2)
      convert hh using 1
      funext p
      ring)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_const_mul]
  congr 1
  funext p
  ring

theorem planarQuadraticEnergy_disjoint_sum_negative {ι : Type*} [Fintype ι]
    {W : ℝ × ℝ → ℝ} (hW : Continuous W) {v : ι → ℝ × ℝ → ℝ}
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) (hs : ∀ i, HasCompactSupport (v i))
    (hdis : Pairwise (fun i j => Disjoint (tsupport (v i)) (tsupport (v j))))
    (hq : ∀ i, planarQuadraticEnergy W (v i) < 0) {c : ι → ℝ} (hc : c ≠ 0) :
    planarQuadraticEnergy W (fun p => ∑ i, c i*v i p) < 0 := by
  classical
  rw [planarQuadraticEnergy_disjoint_sum hW hv hs hdis]
  apply Finset.sum_neg' (fun i _ => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hq i).le)
  have hex : ∃ i, c i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hc (funext hn)
  obtain ⟨i,hi⟩ := hex
  exact ⟨i,Finset.mem_univ i,mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hi) (hq i)⟩

theorem planar_negative_disjoint_family_independent {ι : Type*} [Fintype ι]
    {W : ℝ × ℝ → ℝ} (hW : Continuous W) {v : ι → ℝ × ℝ → ℝ}
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) (hs : ∀ i, HasCompactSupport (v i))
    (hdis : Pairwise (fun i j => Disjoint (tsupport (v i)) (tsupport (v j))))
    (hq : ∀ i, planarQuadraticEnergy W (v i) < 0) : LinearIndependent ℝ v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c he
  by_contra hn
  have hc : c ≠ 0 := by intro h; subst c; exact hn (by simp)
  have hneg := planarQuadraticEnergy_disjoint_sum_negative hW hv hs hdis hq hc
  have hfun : (fun p => ∑ i, c i*v i p) = 0 := by
    funext p
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using congrFun he p
  rw [hfun] at hneg
  simp [planarQuadraticEnergy] at hneg

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.planarQuadraticEnergy_disjoint_sum
#print axioms TwoAxisHelicoid.planar_negative_disjoint_family_independent
