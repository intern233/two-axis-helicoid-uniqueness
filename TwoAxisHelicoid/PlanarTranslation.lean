import TwoAxisHelicoid.PlanarEnergyStability
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.Group.ContinuousDiv

namespace TwoAxisHelicoid
open Set MeasureTheory Filter Function
open scoped ContDiff

local instance : (volume : Measure (ℝ × ℝ)).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddRightInvariant (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))

noncomputable def planarTranslate (v : ℝ × ℝ → ℝ) (s : ℝ) (p : ℝ × ℝ) : ℝ :=
  v (p-(s,0))

theorem planarTranslate_contDiff {v : ℝ × ℝ → ℝ} (hv : ContDiff ℝ ∞ v) (s : ℝ) :
    ContDiff ℝ ∞ (planarTranslate v s) := hv.comp (contDiff_id.sub contDiff_const)

theorem planarTranslate_hasCompactSupport {v : ℝ × ℝ → ℝ} (hs : HasCompactSupport v)
    (s : ℝ) : HasCompactSupport (planarTranslate v s) :=
  hs.comp_homeomorph (Homeomorph.subRight (s,0))

theorem planarTranslate_tsupport (v : ℝ × ℝ → ℝ) (s : ℝ) :
    tsupport (planarTranslate v s) = (fun p => p-(s,0)) ⁻¹' tsupport v :=
  tsupport_comp_eq_preimage v (Homeomorph.subRight (s,0))

theorem planarTranslate_fderiv {v : ℝ × ℝ → ℝ} (hv : Differentiable ℝ v) (s : ℝ)
    (p : ℝ × ℝ) : fderiv ℝ (planarTranslate v s) p = fderiv ℝ v (p-(s,0)) := by
  have h := (hv (p-(s,0))).hasFDerivAt.comp p ((hasFDerivAt_id p).sub_const (s,0))
  simpa only [planarTranslate,ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using! h.fderiv

theorem planarQuadraticEnergy_translate {v : ℝ × ℝ → ℝ} (hv : Differentiable ℝ v)
    (W : ℝ × ℝ → ℝ) (s : ℝ) :
    planarQuadraticEnergy W (planarTranslate v s) =
      planarQuadraticEnergy (fun p => W (p+(s,0))) v := by
  unfold planarQuadraticEnergy
  simp_rw [planarTranslate_fderiv hv,planarTranslate]
  have he := integral_sub_right_eq_self
    (fun p : ℝ × ℝ => (fderiv ℝ v p (1,0))^2+(fderiv ℝ v p (0,1))^2-
      W (p+(s,0))*v p^2) (s,0) (μ := volume)
  simpa only [sub_add_cancel] using he

theorem planarMass_translate (v : ℝ × ℝ → ℝ) (s : ℝ) :
    planarMass (planarTranslate v s) = planarMass v :=
  integral_sub_right_eq_self (fun p : ℝ × ℝ => v p^2) (s,0)

/-- Compact uniform convergence of translated potentials preserves the
negative energy of one fixed compact test function sufficiently far out. -/
theorem planar_negative_translates_eventually {W V v : ℝ × ℝ → ℝ}
    (hW : Continuous W) (hV : Continuous V) (hv : ContDiff ℝ ∞ v)
    (hs : HasCompactSupport v) (hq : planarQuadraticEnergy V v < 0)
    (hlimit : ∀ ε > 0, ∃ S : ℝ, ∀ s ≥ S, ∀ p ∈ tsupport v,
      |W (p+(s,0))-V p| ≤ ε) :
    ∃ S : ℝ, ∀ s ≥ S, planarQuadraticEnergy W (planarTranslate v s) < 0 := by
  have hm : 0 ≤ planarMass v := integral_nonneg (fun p => sq_nonneg (v p))
  let ε := -planarQuadraticEnergy V v/(2*(planarMass v+1))
  have hε : 0 < ε := div_pos (neg_pos.mpr hq) (by linarith)
  have hmargin : ε*planarMass v < -planarQuadraticEnergy V v := by
    dsimp [ε]
    have hden : 0 < 2*(planarMass v+1) := by positivity
    apply (mul_lt_mul_iff_right₀ hden).mp
    field_simp
    nlinarith
  obtain ⟨S,hS⟩ := hlimit ε hε
  refine ⟨S,?_⟩
  intro s hsS
  rw [planarQuadraticEnergy_translate (hv.differentiable (by simp))]
  exact planarQuadraticEnergy_negative_of_close
    (hW.comp (continuous_id.add continuous_const)) hV hv hs (hS s hsS) hmargin

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.planarQuadraticEnergy_translate
#print axioms TwoAxisHelicoid.planar_negative_translates_eventually
