import TwoAxisHelicoid.HelicoidalC1Similarity

namespace TwoAxisHelicoid
open Set

/-- A homeomorphic change of parameter acts on the actual compact core
and the domain of the end projection; the same scalar graph works. -/
theorem HasHelicoidC1End.comp_homeomorph {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {Y : N → HelicoidTubeCoordinates} (h : HasHelicoidC1End Y) (e : M ≃ₜ N) :
    HasHelicoidC1End (Y ∘ e) := by
  obtain ⟨C,hC,R,hR,hcomp,E,hE,u,hu,hgraph,hlim⟩ := h
  let D := helicoidProjectedEnd Y C (exteriorPlaneBase R)
  let U := helicoidProjectedEnd (Y ∘ e) (e ⁻¹' C) (exteriorPlaneBase R)
  let V : U ≃ₜ D := e.subtype (p := fun x => x ∈ U) (q := fun x => x ∈ D) (fun _ => Iff.rfl)
  refine ⟨e ⁻¹' C,e.isCompact_preimage.mpr hC,R,hR,e.isCompact_preimage.mpr hcomp,
    V.trans E,?_,u,hu,?_,hlim⟩
  · funext x
    exact congrFun hE (V x)
  · intro p
    refine ⟨(hgraph p).1,?_⟩
    change Y (e (e.symm (E.symm p).1)) = _
    simpa only [e.apply_symm_apply] using (hgraph p).2

theorem HasHelicoidalC1End.comp_homeomorph {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    {Y : N → Fin 3 → ℝ} (h : HasHelicoidalC1End Y) (e : M ≃ₜ N) :
    HasHelicoidalC1End (Y ∘ e) := by
  obtain ⟨R,k,hk,hd,hg⟩ := h
  exact ⟨R,k,hk,hd,hg.comp_homeomorph e⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.HasHelicoidalC1End.comp_homeomorph
