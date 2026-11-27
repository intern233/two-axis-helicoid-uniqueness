import TwoAxisHelicoid.SimilarityFieldRigidity
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace TwoAxisHelicoid
open Matrix Complex Filter
open scoped Topology

noncomputable def similarityLinear (b : Fin 3 → ℝ) (d : ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap (crossProduct b+d • LinearMap.id)

@[simp] theorem similarityLinear_apply (b : Fin 3 → ℝ) (d : ℝ) (v : Fin 3 → ℝ) :
    similarityLinear b d v = b ⨯₃ v+d • v := rfl

/-- The final linear-algebra step of Appendix D.1 needs only one genuine
two-dimensional immersion point and vanishing in a neighborhood of it. -/
theorem similarityField_zero_near_immersion {X : ℂ → Fin 3 → ℝ} {p : ℂ}
    {D : ℂ →L[ℝ] (Fin 3 → ℝ)} (hX : HasFDerivAt X D p)
    (hD : Function.Injective D) {a b : Fin 3 → ℝ} {d : ℝ}
    (hzero : ∀ᶠ z in 𝓝 p, similarityField a b d (X z) = 0) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  have hdiff : HasFDerivAt (fun z => similarityField a b d (X z))
      ((similarityLinear b d).comp D) p := by
    convert ((similarityLinear b d).hasFDerivAt.comp p hX).const_add a using 1
    funext z
    simp only [similarityField,Function.comp_apply,similarityLinear_apply,add_assoc]
  have hdz : (similarityLinear b d).comp D = 0 :=
    hdiff.unique ((hasFDerivAt_const (0 : Fin 3 → ℝ) p).congr_of_eventuallyEq hzero)
  have hbase : LinearIndependent ℝ ![(1 : ℂ),I] := by
    rw [← Complex.coe_basisOneI]
    exact Complex.basisOneI.linearIndependent
  have hpair : LinearIndependent ℝ ![D 1,D I] := by
    have h := hbase.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr hD)
    convert h using 1
    funext j
    fin_cases j <;> rfl
  have h₁ : b ⨯₃ D 1+d • D 1 = 0 := by
    have h := congrArg (fun A : ℂ →L[ℝ] (Fin 3 → ℝ) => A 1) hdz
    exact h
  have hI : b ⨯₃ D I+d • D I = 0 := by
    have h := congrArg (fun A : ℂ →L[ℝ] (Fin 3 → ℝ) => A I) hdz
    exact h
  obtain ⟨hb,hd⟩ := similarity_linear_part_annihilates_pair hpair h₁ hI
  refine ⟨?_,hb,hd⟩
  have hp := hzero.self_of_nhds
  simpa [similarityField,hb,hd] using hp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.similarityField_zero_near_immersion
