import TwoAxisHelicoid.HolomorphicParameterQuotient
import TwoAxisHelicoid.MeromorphicHeightPowerCoordinate
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

namespace TwoAxisHelicoid
open Complex Set Filter Function TopologicalSpace
open scoped Topology ContDiff Manifold

private theorem holomorphic_into_open {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    {S : Opens ℂ} {A : M → S} {x : M}
    (h : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (Subtype.val ∘ A) x) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω A x := by
  rw [← contMDiffWithinAt_univ]
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := S) A univ x).mp h.contMDiffWithinAt

/-- An analytic function of nonzero derivative locally lifts points
of the target through a holomorphic section, with values remaining
in the specified open domain. -/
theorem analytic_open_section {S T : Opens ℂ} {F : ℂ → ℂ} (x : S)
    (analytic : AnalyticAt ℂ F x.1) (non : deriv F x.1≠0) (image : F x.1∈T) :
    let y : T := ⟨F x.1,image⟩
    ∃ g : T → S, ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g y ∧
      ∀ᶠ w in 𝓝 y, F (g w).1=w.1 := by
  classical
  let y : T := ⟨F x.1,image⟩
  let f := analytic.hasStrictDerivAt.localInverse _ _ _ non
  have af : AnalyticAt ℂ f y.1 := analytic.analyticAt_localInverse non
  have eq : f y.1=x.1 := (analytic.hasStrictDerivAt.eventually_left_inverse non).self_of_nhds
  have range : ∀ᶠ w in 𝓝 y, f w.1∈S :=
    (af.continuousAt.comp continuous_subtype_val.continuousAt).eventually (S.isOpen.mem_nhds (show (f ∘ Subtype.val) y∈S from by change f y.1∈S; rw [eq]; exact x.2))
  let g := fun w : T => if h : f w.1∈S then (⟨f w.1,h⟩ : S) else x
  have ev : Subtype.val ∘ g =ᶠ[𝓝 y] f ∘ Subtype.val := range.mono fun _ h => by simp [g,h]
  refine ⟨g,holomorphic_into_open ((af.contDiffAt.contMDiffAt.comp y contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq ev),?_⟩
  have right := analytic.hasStrictDerivAt.eventually_right_inverse non
  filter_upwards [ev,continuous_subtype_val.continuousAt.tendsto.eventually right] with w hw h
  change (g w).1=f w.1 at hw
  rwa [hw]

/-- A holomorphic local parameter on a covering domain descends to a
biholomorphism onto its exact range if it separates precisely the
covering fibers. -/
theorem analytic_function_uniformizes_quotient {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (S T : Opens ℂ) {p : S → M} (hp : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p)
    (onto : Surjective p) (F : ℂ → ℂ) (reg : ∀ z∈S, AnalyticAt ℂ F z ∧ deriv F z≠0)
    (im : F '' (S : Set ℂ)=(T : Set ℂ)) (fibers : ∀ a b : S, F a.1=F b.1 ↔ p a=p b) :
    ∃ E : Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M T ω, ∀ z : S, (E (p z)).1=F z.1 := by
  classical
  let G := fun z : S => (⟨F z.1,by change F z.1∈(T:Set ℂ); rw [← im]; exact mem_image_of_mem F z.2⟩ : T)
  have gs : Surjective G := by
    rintro ⟨w,hw⟩
    obtain ⟨x,hx,eq⟩ := (show w∈F '' (S : Set ℂ) from by rw [im]; exact hw)
    exact ⟨⟨x,hx⟩,Subtype.ext eq⟩
  let f := fun m => G ((onto m).choose)
  let g := fun q => p ((gs q).choose)
  have hf (z : S) : f (p z)=G z := Subtype.ext ((fibers _ _).mpr (onto _).choose_spec)
  have hg (z : S) : g (G z)=p z := (fibers _ _).mp (congrArg Subtype.val (gs _).choose_spec)
  have df : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f := by
    intro m
    obtain ⟨z,rfl⟩ := onto m
    let h := hp z
    have holG : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω G := fun a => holomorphic_into_open
      (contMDiffAt_subtype_iff.mpr (reg _ a.2).1.contDiffAt.contMDiffAt)
    apply (holG.contMDiffAt.comp (p z) h.contMDiffAt_localInverse).congr_of_eventuallyEq
    filter_upwards [h.localInverse_open_source.mem_nhds h.localInverse_mem_source] with y hy
    exact (congrArg f (h.localInverse_right_inv hy)).symm.trans (hf _)
  have dg : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g := by
    intro t
    obtain ⟨z,rfl⟩ := gs t
    obtain ⟨d,diff,ev⟩ := analytic_open_section z (reg _ z.2).1 (reg _ z.2).2 (G z).2
    apply ((hp (d (G z))).contMDiffAt.comp (G z) diff).congr_of_eventuallyEq
    filter_upwards [ev] with w h
    exact (congrArg g (show G (d w)=w from Subtype.ext h)).symm.trans (hg _)
  let E : Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M T ω :=
    { toFun := f
      invFun := g
      left_inv := fun m => by obtain ⟨z,rfl⟩ := onto m; rw [hf,hg]
      right_inv := fun n => by obtain ⟨z,rfl⟩ := gs n; rw [hg,hf]
      contMDiff_toFun := df
      contMDiff_invFun := dg }
  exact ⟨E,fun z => congrArg Subtype.val (hf z)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.analytic_function_uniformizes_quotient
