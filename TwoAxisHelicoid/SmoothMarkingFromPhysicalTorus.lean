import TwoAxisHelicoid.ManifoldImmersionTest
import TwoAxisHelicoid.HarmonicMarkedTorusCompleteness
import TwoAxisHelicoid.OneHandleGraphExteriorRigidity

namespace TwoAxisHelicoid
open Complex Set Filter Function Topology InnerProductSpace
open scoped Topology Manifold ContDiff

/-- A homeomorphism identifying two actual smooth immersions is smooth in
both directions, even when the homeomorphism arrived from a topological construction. -/
theorem smooth_marking_of_common_positions
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    (f : M ≃ₜ N) {X : M → Fin 3 → ℝ} {Y : N → Fin 3 → ℝ}
    (sx : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (ix : ∀ p, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X p))
    (sy : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ Y)
    (iy : ∀ p, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) Y p))
    (same : ∀ x, Y (f x)=X x) :
    ∃ e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M N ∞, ∀ x, e x=f x := by
  have forward : Y ∘ f=X := funext same
  have inverse : X ∘ f.symm=Y := funext fun y =>
    (same (f.symm y)).symm.trans (congrArg Y (f.apply_symm_apply y))
  have sf : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f :=
    fun x => contMDiffAt_of_comp_regular_map (sy _) (iy _) f.continuous.continuousAt (by rw [forward]; exact sx x)
  have si : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f.symm :=
    fun y => contMDiffAt_of_comp_regular_map (sx _) (ix _) f.symm.continuous.continuousAt (by rw [inverse]; exact sy y)
  exact ⟨⟨f.toEquiv,sf,si⟩,fun _ => rfl⟩

/-- A harmonic torus parametrization of a real immersion gives a smooth
marking in the immersion's original real manifold structure. -/
theorem smooth_marking_of_harmonic_torus_model {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {L : PeriodPair} (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ)
    {X : M → Fin 3 → ℝ} (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (imm : ∀ x, Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x)) (agrees : ∀ x, Y (f x).1=X x)
    (regular : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
      Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z)) :
    ∃ e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞, ∀ x, e x=f x := by
  let Yp := fun q : PuncturedPeriodTorus L => Y q.1
  let Z := puncturedTorusPullback L Yp
  have jets (z : ℂ) (hz : z∉L.lattice) :
      (∀ j, HarmonicAt (fun w => Z w j) z) ∧ Injective (fderiv ℝ Z z) := by
    have eq : Z=ᶠ[𝓝 z] Y ∘ periodTorusProjection L := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      change w∉L.lattice at hw
      simp [Z,Yp,puncturedTorusPullback,hw,puncturedPlaneProjection]
    obtain ⟨harm,inj⟩ := regular z hz
    exact ⟨fun j => (harmonicAt_congr_nhds (eq.mono fun w h => congrFun h j)).mpr (harm j),
      by rwa [eq.fderiv_eq]⟩
  have harm := fun z hz => (jets z hz).1
  have smooth : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ Yp :=
    (harmonic_marked_torus_contMDiff L Yp harm).of_le (by simp)
  have inj (q : PuncturedPeriodTorus L) : Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) Yp q) := by
    rw [(harmonic_marked_torus_hasMFDerivAt L Yp harm q).mfderiv]
    exact (jets _ (puncturedPeriodTorus_chart_not_lattice L q)).2
  exact smooth_marking_of_common_positions f sm imm smooth inj agrees

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.smooth_marking_of_harmonic_torus_model

