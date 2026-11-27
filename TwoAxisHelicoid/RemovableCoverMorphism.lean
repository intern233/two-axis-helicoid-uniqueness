import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.DenseEmbedding

namespace TwoAxisHelicoid
open Filter Set Topology

/-- An extension on a single simply connected neighborhood: the specified
punctured part must be connected, so one prescribed sheet determines the
whole local lift. -/
theorem covering_map_lift_on_connected_deleted_neighborhood
    {A B E : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E]
    {p : E → B} (hp : IsCoveringMap p) {D V : Set A}
    [SimplyConnectedSpace V] [LocallyPathConnectedSpace V] (hC : IsConnected {v : V | v.1 ∈ D})
    (φ : C(A,B)) (f : C(D,E)) (hf : ∀ a, p (f a) = φ a.1) :
    ∃ g : C(V,E), (∀ v, p (g v) = φ v.1) ∧ ∀ v : V, ∀ hv : v.1 ∈ D, g v = f ⟨v.1,hv⟩ := by
  let S := {v : V | v.1 ∈ D}
  let _ : ConnectedSpace S := isConnected_iff_connectedSpace.mp hC
  obtain ⟨v₀,hv₀⟩ := hC.nonempty
  let φV : C(V,B) := ⟨fun v => φ v.1,φ.continuous.comp continuous_subtype_val⟩
  let d : D := ⟨v₀.1,hv₀⟩
  obtain ⟨g,⟨hg0,hg⟩,_⟩ := hp.existsUnique_continuousMap_lifts φV v₀ (f d) (hf d)
  have hD : Continuous (fun v : S => (⟨v.1.1,v.2⟩ : D)) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he : (fun v : S => g v.1) = fun v : S => f ⟨v.1.1,v.2⟩ := by
    apply hp.eq_of_comp_eq (g.continuous.comp continuous_subtype_val) (f.continuous.comp hD) _ ⟨v₀,hv₀⟩ hg0
    exact funext fun x => (congrFun hg x.1).trans (hf ⟨x.1.1,x.2⟩).symm
  exact ⟨g,fun x => congrFun hg x,fun v hv => congrFun he ⟨v,hv⟩⟩

/-- Punctured lifts extend uniquely over a dense deletion when every point
has a simply connected neighborhood with connected deleted complement.
Both the sheet selection and agreement on overlaps are consequences. -/
theorem dense_cover_lift_extends
    {A B E : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E]
    [T2Space B] [T3Space E] {p : E → B} (hp : IsCoveringMap p) {D : Set A} (hd : Dense D)
    (hloc : ∀ a : A, ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ SimplyConnectedSpace V ∧
      LocallyPathConnectedSpace V ∧ IsConnected {v : V | v.1 ∈ D})
    (φ : C(A,B)) (f : C(D,E)) (hf : ∀ a, p (f a) = φ a.1) :
    ∃! H : C(A,E), (∀ a, p (H a) = φ a) ∧ ∀ a : D, H a.1 = f a := by
  classical
  have hlim (a : A) : ∃ b, Tendsto f (comap ((↑) : D → A) (𝓝 a)) (𝓝 b) := by
    obtain ⟨V,hV,ha,h₁,h₂,hC⟩ := hloc a
    let _ := h₁
    let _ := h₂
    obtain ⟨g,_,hag⟩ := covering_map_lift_on_connected_deleted_neighborhood hp hC φ f hf
    let G := fun x : A => if hx : x ∈ V then g ⟨x,hx⟩ else g ⟨a,ha⟩
    have hgV (v : V) : G v.1 = g v := by simp [G,v.2]
    have hGC : ContinuousOn G V := continuousOn_iff_continuous_domRestrict.mpr (by
      change Continuous (fun v : V => G v.1)
      simpa only [hgV] using g.continuous)
    have heq : (G ∘ (Subtype.val : D → A)) =ᶠ[comap (Subtype.val : D → A) (𝓝 a)] f := by
      apply eventually_comap.mpr
      filter_upwards [hV.mem_nhds ha] with x hx
      rintro v rfl
      exact (hgV ⟨v.1,hx⟩).trans (hag ⟨v.1,hx⟩ v.2)
    exact ⟨G a,(Filter.Tendsto.comp ((hGC a ha).continuousAt (hV.mem_nhds ha)) tendsto_comap).congr' heq⟩
  let H : C(A,E) := ⟨hd.extend f,hd.continuous_extend hlim⟩
  have he (a : D) : H a.1 = f a := hd.extend_eq f.continuous a
  have hpeq : p ∘ H = φ := Continuous.ext_on hd (hp.continuous.comp H.continuous) φ.continuous
    (fun x hx => (congrArg p (he ⟨x,hx⟩)).trans (hf ⟨x,hx⟩))
  refine ⟨H,⟨fun x => congrFun hpeq x,he⟩,?_⟩
  intro T hT
  exact DFunLike.ext' (Continuous.ext_on hd T.continuous H.continuous
    (fun x hx => (hT.2 ⟨x,hx⟩).trans (he ⟨x,hx⟩).symm))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.dense_cover_lift_extends
