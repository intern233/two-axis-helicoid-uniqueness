import TwoAxisHelicoid.OriginalUnmarkedCoreC1
import TwoAxisHelicoid.PeriodTorusComplexManifold

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff Manifold

/-- A marked punctured torus parametrization supplies genuine regular
surface charts around every specified lift. Their inverse always lifts
the original position by the same period projection. -/
theorem regular_chart_of_marked_covering {B : Type*} [TopologicalSpace B] {A : PeriodPair}
    (m : B ≃ₜ PuncturedPeriodTorus A) (X : B → Fin 3 → ℝ) (Y : PeriodTorus A → Fin 3 → ℝ)
    (pos : ∀ x, Y (m x).1=X x) (regular : ∀ z∉A.lattice,
      ContDiffAt ℝ ∞ (Y ∘ periodTorusProjection A) z ∧ Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection A) z))
    (z : ℂ) (nz : z∉A.lattice) :
    ∃ a : OpenPartialHomeomorph B ℂ, z∈a.target ∧ RegularImmersionChart X a ∧
      ∀ w∈a.target, (m (a.symm w)).1=periodTorusProjection A w := by
  let p := (Subtype.val : PuncturedPeriodTorus A → PeriodTorus A) ∘ m
  let π := periodTorusProjection A
  have off : π z≠0 := fun eq => nz ((periodTorusProjection_eq_zero A z).mp eq)
  let b := m.symm ⟨π z,off⟩
  let _ : Nonempty B := ⟨b⟩
  have op : IsOpenEmbedding p := isOpen_ne.isOpenEmbedding_subtypeVal.comp m.isOpenEmbedding
  let j := op.toOpenPartialHomeomorph p
  obtain ⟨e,ze,πe⟩ := periodTorusProjection_isLocalHomeomorph A z
  let a := j.trans e.symm
  have point : e z∈j.target := by
    rw [show j.target=range p from op.toOpenPartialHomeomorph_target]
    refine ⟨b,?_⟩
    exact (congrArg Subtype.val (m.apply_symm_apply ⟨π z,off⟩)).trans (congrFun πe z)
  have lift (w : ℂ) (hw : w∈a.target) : (m (a.symm w)).1=π w :=
    (j.right_inv (show e w∈j.target from hw.2)).trans (congrFun πe w).symm
  refine ⟨a,⟨ze,point⟩,?_,lift⟩
  intro w hw
  have non : w∉A.lattice := fun h => (m (a.symm w)).2 ((lift w hw).trans ((periodTorusProjection_eq_zero A w).mpr h))
  have germ : X ∘ a.symm=ᶠ[𝓝 w] Y ∘ π :=
    Filter.mem_of_superset (a.open_target.mem_nhds hw) (fun t ht => (pos _).symm.trans (congrArg Y (lift t ht)))
  refine ⟨(regular w non).1.congr_of_eventuallyEq germ,?_⟩
  rw [germ.fderiv_eq (𝕜 := ℝ)]
  exact (regular w non).2

/-- A whole open set of the universal covering plane can be checked
in different local lifts. The maps and all derivatives are the same
where two of these parametrizations overlap. -/
theorem covering_charts_glue_C1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} {Z : ℕ → ℂ → E} {Y : ℂ → E}
    (localData : ∀ z∈U, ∃ V : Set ℂ, IsOpen V ∧ z∈V ∧
      (∀ n w, w∈V → ContDiffAt ℝ 1 (Z n) w) ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ Y) atTop V) :
    (∀ n w, w∈U → ContDiffAt ℝ 1 (Z n) w) ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ Y) atTop U := by
  constructor
  · intro n w hw
    obtain ⟨_,_,h,s,_⟩ := localData w hw
    exact s n w h
  · intro entourage ent w hw
    obtain ⟨V,vo,v,_,conv⟩ := localData w hw
    obtain ⟨T,ht,uniform⟩ := conv entourage ent w v
    rw [vo.nhdsWithin_eq v] at ht
    exact ⟨T,mem_nhdsWithin_of_mem_nhds ht,uniform⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.regular_chart_of_marked_covering
#print axioms TwoAxisHelicoid.covering_charts_glue_C1
