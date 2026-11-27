import TwoAxisHelicoid.AnalyticRoundQuotient
import TwoAxisHelicoid.RoundCylinderParameter
import Mathlib.Analysis.Complex.CoveringMap

namespace TwoAxisHelicoid
open Complex Filter Set Metric Function Topology TopologicalSpace
open scoped Topology ContDiff Manifold

private theorem analytic_into_open_at {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {S : Opens ℂ} {f : M → S} {x : M}
    (h : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (Subtype.val ∘ f) x) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f x := by
  rw [← contMDiffWithinAt_univ]
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := S) f univ x).mp h.contMDiffWithinAt

/-- A covering between plane domains given by an unramified analytic
function is a local analytic diffeomorphism in the specified atlases. -/
theorem analytic_open_local_diffeomorphism {S T : Opens ℂ} (F : ℂ → ℂ) (f : S → T)
    (pos : ∀ x : S, (f x).1=F x.1) (reg : ∀ z∈S, AnalyticAt ℂ F z ∧ deriv F z≠0)
    (localMap : IsLocalHomeomorph f) : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f := by
  have forward (x : S) : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f x := by
    apply analytic_into_open_at
    have eq : Subtype.val ∘ f=F ∘ Subtype.val := funext pos
    rw [eq]
    exact contMDiffAt_subtype_iff.mpr (reg x x.2).1.contDiffAt.contMDiffAt
  intro x
  obtain ⟨e,inside,eq⟩ := localMap x
  have back (y : T) (hy : y∈e.target) : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm y := by
    let a := e.symm y
    obtain ⟨an,nd⟩ := reg a.1 a.2
    let g := an.hasStrictDerivAt.localInverse _ _ _ nd
    have val : F a.1=y.1 := (pos a).symm.trans (congrArg Subtype.val ((congrFun eq a).trans (e.right_inv hy)))
    have smooth : AnalyticAt ℂ g y.1 := val ▸ an.analyticAt_localInverse nd
    have inv : Tendsto (fun w : T => (e.symm w).1) (𝓝 y) (𝓝 a.1) :=
      (continuous_subtype_val.continuousAt.comp (e.symm.continuousAt hy)).tendsto
    apply analytic_into_open_at
    apply (show ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (g ∘ Subtype.val) y from
      contMDiffAt_subtype_iff.mpr smooth.contDiffAt.contMDiffAt).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hy,inv.eventually (an.hasStrictDerivAt.eventually_left_inverse nd)] with w hw left
    have image : F (e.symm w).1=w.1 :=
      (pos _).symm.trans (congrArg Subtype.val ((congrFun eq _).trans (e.right_inv hw)))
    change (e.symm w).1=g w.1
    rw [← image]
    exact left.symm
  let d : PartialDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) S T ω := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := by
      change ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e e.source
      rw [← eq]
      exact fun z _ => (forward z).contMDiffWithinAt
    contMDiffOn_invFun := fun z hz => (back z hz).contMDiffWithinAt }
  exact ⟨d,inside,fun z _ => congrFun eq z⟩

def roundLogDomain (T : Opens ℂ) : Opens ℂ := ⟨Complex.exp ⁻¹' (T : Set ℂ),T.isOpen.preimage Complex.continuous_exp⟩

/-- Restricting the exponential covering to an arbitrary open subset
of the punctured plane gives a covering with its standard analytic
complex structures on both open sets. -/
theorem round_log_domain_exponential (T : Opens ℂ) (nz : ∀ z∈T, z≠0) :
    ∃ f : roundLogDomain T → T, IsCoveringMap f ∧ Surjective f ∧
      IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f := by
  let F := fun z : ℂ => (⟨Complex.exp z,Complex.exp_ne_zero z⟩ : {w : ℂ // w≠0})
  let V := {w : {w : ℂ // w≠0} | w.1∈T}
  let E : V ≃ₜ T := {
    toFun := fun z => ⟨z.1.1,z.2⟩
    invFun := fun z => ⟨⟨z.1,nz z z.2⟩,z.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  let f : roundLogDomain T → T := E ∘ V.restrictPreimage F
  have cover : IsCoveringMap f := (Complex.isCoveringMap_exp.restrictPreimage V).homeomorph_comp E
  have sur : Surjective f := by
    rintro ⟨z,hz⟩
    have eq := Complex.exp_log (nz z hz)
    exact ⟨⟨Complex.log z,show Complex.exp (Complex.log z)∈T from by rwa [eq]⟩,Subtype.ext eq⟩
  refine ⟨f,cover,sur,analytic_open_local_diffeomorphism Complex.exp f (fun _ => rfl) (fun z _ => ?_) cover.isLocalHomeomorph⟩
  exact ⟨analyticAt_cexp,(Complex.hasDerivAt_exp _).deriv.symm ▸ Complex.exp_ne_zero z⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_open_local_diffeomorphism
#print axioms TwoAxisHelicoid.round_log_domain_exponential
