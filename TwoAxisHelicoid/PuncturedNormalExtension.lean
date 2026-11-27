import TwoAxisHelicoid.SpatialDifferentialNormal
import TwoAxisHelicoid.PuncturedChartNeighborhood

namespace TwoAxisHelicoid
open Set Topology

/-- Patch a function on a punctured space to a local function which is
already defined on an open neighborhood of the missing point. -/
theorem punctured_field_patch {M X : Type*} [TopologicalSpace M] [T1Space M] [TopologicalSpace X]
    (p : M) {V : Set M} (hV : IsOpen V) (hpV : p ∈ V)
    (f : C({x : M // x ≠ p},X)) (g : C(V,X))
    (h : ∀ v : V, ∀ hv : v.1 ≠ p, f ⟨v.1,hv⟩ = g v) :
    ∃ F : C(M,X), (∀ x : {x : M // x ≠ p}, F x.1 = f x) ∧ ∀ v : V, F v.1 = g v := by
  classical
  let F := fun x : M => if hx : x ≠ p then f ⟨x,hx⟩ else g ⟨p,hpV⟩
  have hF (x : {x : M // x ≠ p}) : F x.1 = f x := by simp [F,x.2]
  have hG (x : V) : F x.1 = g x := by
    by_cases hx : x.1 ≠ p
    · exact (hF ⟨x.1,hx⟩).trans (h x hx)
    · have he := not_ne_iff.mp hx
      have heq : x = ⟨p,hpV⟩ := Subtype.ext he
      rw [heq]
      simp [F]
  have hopen : IsOpen ({p}ᶜ : Set M) := isOpen_compl_singleton
  have hc : ContinuousOn F ({p}ᶜ : Set M) := continuousOn_iff_continuous_domRestrict.mpr (by
    change Continuous (fun x : {x : M // x ≠ p} => F x.1)
    simpa only [hF] using f.continuous)
  have hgc : ContinuousOn F V := continuousOn_iff_continuous_domRestrict.mpr (by
    change Continuous (fun x : V => F x.1)
    simpa only [hG] using g.continuous)
  refine ⟨⟨F,continuous_iff_continuousAt.mpr (fun x => ?_)⟩,hF,hG⟩
  by_cases hx : x ≠ p
  · exact (hc x hx).continuousAt (hopen.mem_nhds hx)
  · exact (hgc x (not_ne_iff.mp hx ▸ hpV)).continuousAt (hV.mem_nhds (not_ne_iff.mp hx ▸ hpV))

/-- A locally unoriented normal extends a globally chosen orientation across
one puncture of a surface. Connectedness of the deleted chart neighborhood
forces one common sign for its full normal field. -/
theorem punctured_unit_normal_extends {M : Type*} [TopologicalSpace M] [T1Space M]
    (p : M) {V : Set M} (hV : IsOpen V) (hpV : p ∈ V) (hc : IsConnected {v : V | v.1 ≠ p})
    (f : C({x : M // x ≠ p},Fin 3 → ℝ)) (g : C(V,Fin 3 → ℝ)) (hn : ∀ v, g v ≠ 0)
    (h : ∀ v : V, ∀ hv : v.1 ≠ p, f ⟨v.1,hv⟩ = g v ∨ f ⟨v.1,hv⟩ = -g v) :
    ∃ F : C(M,Fin 3 → ℝ), (∀ x : {x : M // x ≠ p}, F x.1 = f x) ∧
      ((∀ v : V, F v.1 = g v) ∨ ∀ v : V, F v.1 = -g v) := by
  let D := {v : V | v.1 ≠ p}
  let _ : ConnectedSpace D := isConnected_iff_connectedSpace.mp hc
  let f' : C(D,Fin 3 → ℝ) := ⟨fun x => f ⟨x.1.1,x.2⟩,f.continuous.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
  let g' : C(D,Fin 3 → ℝ) := ⟨fun x => g x.1,g.continuous.comp continuous_subtype_val⟩
  rcases continuous_signed_normal_unique f' g' (fun x => hn x.1) (fun x => h x.1 x.2) with h | h
  · obtain ⟨F,hf,hg⟩ := punctured_field_patch p hV hpV f g (fun v hv => h ⟨v,hv⟩)
    exact ⟨F,hf,Or.inl hg⟩
  · obtain ⟨F,hf,hg⟩ := punctured_field_patch p hV hpV f (-g) (fun v hv => h ⟨v,hv⟩)
    exact ⟨F,hf,Or.inr hg⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.punctured_unit_normal_extends
