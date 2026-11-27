import TwoAxisHelicoid.GroundStateCompactApproximation
import TwoAxisHelicoid.PlanarNegativeDirection

namespace TwoAxisHelicoid
open MeasureTheory Filter Topology
open scoped ContDiff

/-- After choosing the compact transverse cutoff of the sech mode, every
nonzero compact smooth axial function yields a negative two-dimensional
variation for all sufficiently large axial scales, with the exact energy
identity from Appendix D.3. -/
theorem ground_state_axial_dilation_eventually_negative :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → (∃ x, χ x≠0) →
        ∀ᶠ L : ℝ in atTop,
          let V := fun t : ℝ => 2*helicoidGroundState t^2
          let v := fun p : ℝ × ℝ => χ (p.1/L)*ψ p.2
          ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
            planarSchrodingerEnergy V v = L*lineMass χ*lineSchrodingerEnergy V ψ+
              L⁻¹*lineDirichletEnergy χ*lineMass ψ ∧ planarSchrodingerEnergy V v<0 := by
  obtain ⟨ψ,reg,supp,neg⟩ := helicoidGroundState_compact_cutoff_negative
  refine ⟨ψ,reg,supp,?_⟩
  intro χ smooth cpt nt
  let V := fun t => 2*helicoidGroundState t^2
  have cV : Continuous V := continuous_const.mul (helicoidGroundState_smooth.continuous.pow 2)
  obtain ⟨x,hx⟩ := nt
  have positive := lineMass_positive_of_nonzero smooth cpt hx
  let a := -lineMass χ*lineSchrodingerEnergy V ψ
  let b := lineDirichletEnergy χ*lineMass ψ
  have ap : 0<a := mul_pos_of_neg_of_neg (neg_lt_zero.mpr positive) neg
  filter_upwards [eventually_gt_atTop (max 1 (b/a))] with L big
  have one : 1<L := (le_max_left _ _).trans_lt big
  have lp : 0<L := zero_lt_one.trans one
  obtain ⟨sm,hs⟩ := smooth_compact_dilate smooth cpt lp
  obtain ⟨s₂,h₂⟩ := smooth_compact_tensor sm reg hs supp
  refine ⟨s₂,h₂,?_,?_⟩
  · rw [planarSchrodingerEnergy_tensor cV sm reg hs supp,
      lineDirichletEnergy_dilate (smooth.differentiable (by simp)) lp,lineMass_dilate χ lp]
    ring
  · have small := (div_lt_iff₀ ap).mp ((le_max_right _ _).trans_lt big)
    have larger : b<L^2*a := small.trans (mul_lt_mul_of_pos_right (show L<L^2 by nlinarith) ap)
    rw [planarSchrodingerEnergy_tensor cV sm reg hs supp,
      lineDirichletEnergy_dilate (smooth.differentiable (by simp)) lp,lineMass_dilate χ lp]
    apply (mul_lt_mul_iff_right₀ lp).mp
    rw [mul_zero]
    change L*(lineDirichletEnergy χ/L*lineMass ψ+L*lineMass χ*lineSchrodingerEnergy V ψ)<0
    dsimp [a,b] at larger
    field_simp [lp.ne']; nlinarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.ground_state_axial_dilation_eventually_negative
