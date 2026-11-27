import TwoAxisHelicoid.HolomorphicCoverPullback
import TwoAxisHelicoid.UnorientedIsothermalChartHarmonic

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology ContDiff Manifold

/-- A regular conformal parametrization on a punctured compact model,
written directly in coordinates of that model at each finite point. -/
def IsothermalAwayFromPoint {N : Type*} [TopologicalSpace N] [ChartedSpace ℂ N]
    (Z : N → Fin 3 → ℝ) (p : N) : Prop :=
  ∀ c ∈ atlas ℂ N, ∀ w ∈ c.target, c.symm w ≠ p →
    ContDiffAt ℝ ∞ (Z ∘ c.symm) w ∧ Function.Injective (fderiv ℝ (Z ∘ c.symm) w) ∧
      ConformalCoordinateDerivatives (Z ∘ c.symm) w

/-- Pull back the actual Riemann surface structure from a punctured
conformal model. The resulting charts are isothermal for the given
spatial map and the finite inclusion is a holomorphic local diffeomorphism. -/
theorem puncture_pullback_isothermal_atlas {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [T2Space N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ,ℂ) ω N] (p : N) (j : M ≃ₜ {q : N // q ≠ p})
    (X : M → Fin 3 → ℝ) (Z : N → Fin 3 → ℝ) (hZ : ∀ x, Z (j x).1 = X x)
    (hiso : IsothermalAwayFromPoint Z p) :
    ∃ S : ChartedSpace ℂ M, let _ := S
      IsManifold 𝓘(ℂ,ℂ) ω M ∧ (∀ e ∈ atlas ℂ M, InducedIsothermalChart X e) ∧
        IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun x => (j x).1) := by
  let i := fun x => (j x).1
  have hopen : IsOpen {q : N | q ≠ p} := isOpen_compl_singleton
  have hi : IsLocalHomeomorph i := (hopen.isOpenEmbedding_subtypeVal.comp j.isOpenEmbedding).isLocalHomeomorph
  let S := holomorphicCoverAtlas hi
  let _ := S
  have hm : IsManifold 𝓘(ℂ,ℂ) ω M := holomorphicCoverAtlas_isManifold hi
  refine ⟨S,hm,?_,holomorphicCoverAtlas_localDiffeomorph hi⟩
  rintro e ⟨d,c,hd,hc,rfl⟩
  let e := d.trans c
  have heq {w : ℂ} (hw : w ∈ e.target) : X (e.symm w) = Z (c.symm w) := by
    rw [← hZ]
    change Z (i (d.symm (c.symm w))) = Z (c.symm w)
    rw [hd,d.right_inv hw.2]
  have hp' {w : ℂ} (hw : w ∈ e.target) : c.symm w ≠ p := by
    have h := (j (d.symm (c.symm w))).2
    change i (d.symm (c.symm w)) ≠ p at h
    rwa [hd,d.right_inv hw.2] at h
  have hdata (w : ℂ) (hw : w ∈ e.target) := hiso c hc w hw.1 (hp' hw)
  have hg {w : ℂ} (hw : w ∈ e.target) : X ∘ e.symm =ᶠ[𝓝 w] Z ∘ c.symm :=
    (show ∀ᶠ z in 𝓝 w, z ∈ e.target from e.open_target.mem_nhds hw).mono fun _ hz => heq hz
  constructor
  · intro w hw
    have hh := hdata w hw
    refine ⟨hh.1.congr_of_eventuallyEq (hg hw),?_⟩
    rw [(hg hw).fderiv_eq (𝕜 := ℝ)]
    exact hh.2.1
  · intro w hw
    have hh := hdata w hw
    have hdif := hh.1.differentiableAt (by simp)
    apply (conformalCoordinateDerivatives_iff_dot (hdif.congr_of_eventuallyEq (hg hw))).mpr
    rw [(hg hw).fderiv_eq (𝕜 := ℝ)]
    exact (conformalCoordinateDerivatives_iff_dot hdif).mp hh.2.2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.puncture_pullback_isothermal_atlas
