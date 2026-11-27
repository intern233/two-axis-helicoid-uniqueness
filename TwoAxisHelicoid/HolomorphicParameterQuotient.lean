import TwoAxisHelicoid.HolomorphicCoverPullback

namespace TwoAxisHelicoid
open Complex Set Function Filter
open scoped ContDiff Manifold Topology

private theorem holomorphic_map_through_local_coordinates {P M N : Type*}
    [TopologicalSpace P] [ChartedSpace ℂ P] [TopologicalSpace M] [ChartedSpace ℂ M]
    [TopologicalSpace N] [ChartedSpace ℂ N]
    {p : P → M} (hp : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p) (onto : Surjective p)
    {F : P → N} (hF : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F) {f : M → N}
    (eq : ∀ z, f (p z)=F z) : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f := by
  intro x
  obtain ⟨z,rfl⟩ := onto x
  let h := hp z
  apply (hF.contMDiffAt.comp (p z) h.contMDiffAt_localInverse).congr_of_eventuallyEq
  filter_upwards [h.localInverse_open_source.mem_nhds h.localInverse_mem_source] with y hy
  exact (congrArg f (h.localInverse_right_inv hy)).symm.trans (eq _)

/-- Holomorphic coordinates with exactly the same identified points
induce a genuine global biholomorphism between their quotient surfaces. -/
theorem biholomorph_of_identical_cover_fibers {P M N : Type*}
    [TopologicalSpace P] [ChartedSpace ℂ P] [TopologicalSpace M] [ChartedSpace ℂ M]
    [TopologicalSpace N] [ChartedSpace ℂ N]
    {p : P → M} (hp : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p) (ps : Surjective p)
    {F : P → N} (hF : IsLocalDiffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F) (fs : Surjective F)
    (fibers : ∀ x y, p x=p y ↔ F x=F y) :
    ∃ U : Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M N ω, ∀ x, U (p x)=F x := by
  classical
  let f := fun m => F ((ps m).choose)
  let g := fun n => p ((fs n).choose)
  have hf (z : P) : f (p z)=F z := (fibers _ _).mp (ps _).choose_spec
  have hg (z : P) : g (F z)=p z := (fibers _ _).mpr (fs _).choose_spec
  let e : M ≃ N :=
    { toFun := f
      invFun := g
      left_inv := fun m => by obtain ⟨z,rfl⟩ := ps m; rw [hf,hg]
      right_inv := fun n => by obtain ⟨z,rfl⟩ := fs n; rw [hg,hf] }
  let U : Diffeomorph 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) M N ω :=
    { toEquiv := e
      contMDiff_toFun := holomorphic_map_through_local_coordinates hp ps (fun z => (hF z).contMDiffAt) hf
      contMDiff_invFun := holomorphic_map_through_local_coordinates hF fs (fun z => (hp z).contMDiffAt) hg }
  exact ⟨U,hf⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.biholomorph_of_identical_cover_fibers
