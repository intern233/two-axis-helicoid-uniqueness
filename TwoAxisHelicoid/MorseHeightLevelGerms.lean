import TwoAxisHelicoid.CircleLiftNeighborhood

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- A definite two-dimensional Morse germ has an isolated point in
its own level of the original space. -/
theorem definite_morse_height_point_isolated {X : Type*} [TopologicalSpace X]
    {h : X → ℝ} {p : X} (e : OpenPartialHomeomorph X (ℝ×ℝ))
    (src : p∈e.source) (center : e p=0) {a : ℝ} (nz : a≠0)
    (model : ∀ᶠ w in 𝓝 p, h w=h p+a*(e w).1^2+a*(e w).2^2) :
    ∀ᶠ w in 𝓝 p, h w=h p → w=p := by
  filter_upwards [e.open_source.mem_nhds src,model] with w hw eq
  intro same
  have sum : a*((e w).1^2+(e w).2^2)=0 := by linarith only [same,eq,mul_add a ((e w).1^2) ((e w).2^2)]
  have squares := (mul_eq_zero.mp sum).resolve_left nz
  apply e.injOn hw src
  rw [center]
  exact Prod.ext (show (e w).1=0 from sq_eq_zero_iff.mp (by linarith [sq_nonneg (e w).1,sq_nonneg (e w).2]))
    (show (e w).2=0 from sq_eq_zero_iff.mp (by linarith [sq_nonneg (e w).1,sq_nonneg (e w).2]))

/-- The two marked phases lift on a connected level component containing
an isolated height point. This excludes both extrema from the obstruction
that detects odd ambient spin. -/
theorem marked_level_component_lifts_at_isolated_point {X : Type*} [TopologicalSpace X] [T1Space X]
    (H : X → Circle × Circle) {h : X → ℝ} {t : ℝ} (x y : h ⁻¹' {t})
    (same : y∈connectedComponent x) (isolated : ∀ᶠ w in 𝓝 y.1, h w=t → w=y.1) :
    ∃ u v : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
      normalizedPhase (u q)=(H q.1.1).1 ∧ normalizedPhase (v q)=(H q.1.1).2 := by
  have op : IsOpen ({y} : Set (h ⁻¹' {t})) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ rfl
    filter_upwards [continuous_subtype_val.continuousAt.eventually isolated] with w hw
    exact Subtype.ext (hw w.2)
  have sub : connectedComponent x⊆{y} := by
    rw [connectedComponent_eq same]
    exact (show IsClopen ({y} : Set (h ⁻¹' {t})) from ⟨isClosed_singleton,op⟩).connectedComponent_subset rfl
  let angle := fun q : Circle => (q:ℂ).arg/(2*Real.pi)
  have value (q : Circle) : normalizedPhase (angle q)=q := by
    change Circle.exp (2*Real.pi*((q:ℂ).arg/(2*Real.pi)))=q
    rw [show 2*Real.pi*((q:ℂ).arg/(2*Real.pi))=(q:ℂ).arg by field_simp,Circle.exp_arg]
  refine ⟨ContinuousMap.const _ (angle (H y.1).1),ContinuousMap.const _ (angle (H y.1).2),?_⟩
  intro q
  have eq : q.1=y := sub q.2
  change normalizedPhase (angle (H y.1).1)=(H q.1.1).1 ∧ normalizedPhase (angle (H y.1).2)=(H q.1.1).2
  rw [eq]
  exact ⟨value _,value _⟩

/-- In the indefinite Morse case one linear change of the two planar
coordinates realizes the critical level as two crossed coordinate
axes and both adjacent levels as hyperbolas in the same chart. -/
theorem saddle_morse_height_product_chart_with_coordinates {X : Type*} [TopologicalSpace X]
    {h : X → ℝ} {p : X} (e : OpenPartialHomeomorph X (ℝ×ℝ))
    (src : p∈e.source) (center : e p=0) {a : ℝ} (aa : a*a=1)
    (model : ∀ᶠ w in 𝓝 p, h w=h p+a*(e w).1^2+(-a)*(e w).2^2) :
    ∃ q : OpenPartialHomeomorph X (ℝ×ℝ), p∈q.source ∧ q p=0 ∧
      (∀ w, q w=((e w).1-(e w).2,a*((e w).1+(e w).2))) ∧
      ∀ᶠ w in 𝓝 p, h w=h p+(q w).1*(q w).2 := by
  let T : (ℝ×ℝ) ≃ₜ (ℝ×ℝ) := {
    toFun := fun v => (v.1-v.2,a*(v.1+v.2))
    invFun := fun v => ((v.1+a*v.2)/2,(a*v.2-v.1)/2)
    left_inv := by rintro ⟨r,s⟩; apply Prod.ext <;> dsimp <;> nlinarith [congrArg (·*r) aa,congrArg (·*s) aa]
    right_inv := by rintro ⟨r,s⟩; apply Prod.ext <;> dsimp <;> nlinarith [congrArg (·*s) aa]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let q := e.trans T.toOpenPartialHomeomorph
  have q0 : q p=0 := by change T (e p)=0; rw [center]; simp [T]
  refine ⟨q,⟨src,mem_univ _⟩,q0,fun _ => rfl,?_⟩
  filter_upwards [model] with w hw
  rw [hw]
  change h p+a*(e w).1^2+(-a)*(e w).2^2=h p+((e w).1-(e w).2)*(a*((e w).1+(e w).2))
  ring

theorem saddle_morse_height_product_chart {X : Type*} [TopologicalSpace X]
    {h : X → ℝ} {p : X} (e : OpenPartialHomeomorph X (ℝ×ℝ))
    (src : p∈e.source) (center : e p=0) {a : ℝ} (aa : a*a=1)
    (model : ∀ᶠ w in 𝓝 p, h w=h p+a*(e w).1^2+(-a)*(e w).2^2) :
    ∃ q : OpenPartialHomeomorph X (ℝ×ℝ), p∈q.source ∧ q p=0 ∧
      ∀ᶠ w in 𝓝 p, h w=h p+(q w).1*(q w).2 := by
  obtain ⟨q,qs,qz,_,germ⟩ := saddle_morse_height_product_chart_with_coordinates e src center aa model
  exact ⟨q,qs,qz,germ⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_level_component_lifts_at_isolated_point
#print axioms TwoAxisHelicoid.saddle_morse_height_product_chart
