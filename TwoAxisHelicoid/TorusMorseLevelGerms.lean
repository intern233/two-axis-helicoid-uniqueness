import TwoAxisHelicoid.TiltedHeightMorseCharts
import TwoAxisHelicoid.MorseHeightLevelGerms
import TwoAxisHelicoid.EquivariantTorusFrame

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology ContDiff

/-- A planar Morse germ of a genuinely periodic height descends to a
chart of the marked torus with the same physical height germ. -/
theorem torus_morse_height_chart_of_lift_with_germ (L : PeriodPair) (h : PeriodTorus L → ℝ) (z : ℂ)
    (e : OpenPartialHomeomorph ℂ (ℝ×ℝ)) (src : z∈e.source) (zero : e z=0) {a b : ℝ}
    (model : ∀ᶠ w in 𝓝 z, h (periodTorusProjection L w)=h (periodTorusProjection L z)+a*(e w).1^2+b*(e w).2^2) :
    ∃ k : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ), periodTorusProjection L z∈k.source ∧
      k (periodTorusProjection L z)=0 ∧
      (k ∘ periodTorusProjection L) =ᶠ[𝓝 z] e ∧ ∀ᶠ q in 𝓝 (periodTorusProjection L z),
        h q=h (periodTorusProjection L z)+a*(k q).1^2+b*(k q).2^2 := by
  let π := periodTorusProjection L
  obtain ⟨d,ds,repr⟩ := periodTorusProjection_isLocalHomeomorph L z
  have v : π z=d z := congrFun repr z
  have hit : π z∈d.target := v ▸ d.map_source ds
  have back : d.symm (π z)=z := by rw [v,d.left_inv ds]
  let k := d.symm.trans e
  have ks : π z∈k.source := ⟨hit,show d.symm (π z)∈e.source by rw [back]; exact src⟩
  have kz : k (π z)=0 := by change e (d.symm (π z))=0; rw [back,zero]
  have near : Tendsto d.symm (𝓝 (π z)) (𝓝 z) := by simpa only [back] using (d.continuousAt_symm hit).tendsto
  have pullback : (k ∘ π) =ᶠ[𝓝 z] e := by
    filter_upwards [d.open_source.mem_nhds ds] with w hw
    change e (d.symm (periodTorusProjection L w))=e w
    rw [congrFun repr w,d.left_inv hw]
  refine ⟨k,ks,kz,pullback,?_⟩
  filter_upwards [near.eventually model,d.open_target.mem_nhds hit] with q eq inside
  have left : π (d.symm q)=q := (congrFun repr _).trans (d.right_inv inside)
  change h (π (d.symm q))=h (π z)+a*(k q).1^2+b*(k q).2^2 at eq
  rwa [left] at eq

theorem torus_morse_height_chart_of_lift (L : PeriodPair) (h : PeriodTorus L → ℝ) (z : ℂ)
    (e : OpenPartialHomeomorph ℂ (ℝ×ℝ)) (src : z∈e.source) (zero : e z=0) {a b : ℝ}
    (model : ∀ᶠ w in 𝓝 z, h (periodTorusProjection L w)=h (periodTorusProjection L z)+a*(e w).1^2+b*(e w).2^2) :
    ∃ k : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ), periodTorusProjection L z∈k.source ∧
      k (periodTorusProjection L z)=0 ∧ ∀ᶠ q in 𝓝 (periodTorusProjection L z),
        h q=h (periodTorusProjection L z)+a*(k q).1^2+b*(k q).2^2 := by
  obtain ⟨k,ks,kz,_,model⟩ := torus_morse_height_chart_of_lift_with_germ L h z e src zero model
  exact ⟨k,ks,kz,model⟩

/-- On a lattice class the differential of a descended real height is
independent of the plane representative, including at a critical point. -/
theorem torus_height_derivative_eq_of_same_projection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : PeriodPair) (h : PeriodTorus L → E) {z w : ℂ}
    (same : periodTorusProjection L z=periodTorusProjection L w) :
    fderiv ℝ (h ∘ periodTorusProjection L) z=fderiv ℝ (h ∘ periodTorusProjection L) w := by
  let f := h ∘ periodTorusProjection L
  let k := w-z
  have member : k∈L.lattice := (periodTorusProjection_eq_iff L z w).mp same
  have per : (fun y => f (y+k))=f := funext fun y => congrArg h (periodTorusProjection_add_lattice L y k member)
  have derivative := (fderiv_comp_add_right (𝕜:=ℝ) (f:=f) (x:=z) k).symm.trans (congrArg (fun g => fderiv ℝ g z) per)
  have sum : z+k=w := by dsimp [k]; abel
  rw [sum] at derivative
  exact derivative.symm

/-- Smoothness of an actual torus coordinate lifted to the plane is
independent of the representative of a lattice class. -/
theorem torus_lift_contDiffAt_of_same_projection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : PeriodPair) (g : PeriodTorus L → E) {z w : ℂ} {n : WithTop ℕ∞}
    (same : periodTorusProjection L z=periodTorusProjection L w)
    (smooth : ContDiffAt ℝ n (g ∘ periodTorusProjection L) z) :
    ContDiffAt ℝ n (g ∘ periodTorusProjection L) w := by
  let k := z-w
  let f := g ∘ periodTorusProjection L
  have lat : k∈L.lattice := (periodTorusProjection_eq_iff L w z).mp same.symm
  have atZ : w+k=z := by dsimp [k]; abel
  have s : ContDiffAt ℝ n f (w+k) := atZ.symm ▸ smooth
  have composed := s.comp w (show ContDiffAt ℝ n (fun y : ℂ => y+k) w from contDiffAt_id.add contDiffAt_const)
  apply composed.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => (congrArg g (periodTorusProjection_add_lattice L y k lat)).symm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_morse_height_chart_of_lift
#print axioms TwoAxisHelicoid.torus_height_derivative_eq_of_same_projection
