import TwoAxisHelicoid.RawPublishedConformalPoleReduction

namespace TwoAxisHelicoid
open Complex Set Topology InnerProductSpace Matrix
open scoped Topology ContDiff Manifold

/-- Assemble the conformal compactification in the original Euclidean
frame. In this direction the actual torus marking and the two orders
supply the end theorem's conclusions. -/
theorem torus_end_pole_model {M : Type*} [TopologicalSpace M] {X : M → Fin 3 → ℝ}
    (L : PeriodPair) (f : M ≃ₜ PuncturedPeriodTorus L) (Y : PeriodTorus L → Fin 3 → ℝ)
    (pos : ∀ x, Y (f x).1=X x)
    (regular : ∀ z∉L.lattice, (∀ j, HarmonicAt (fun w => Y (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (Y ∘ periodTorusProjection L) z ∧ Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection L) z))
    (height : meromorphicOrderAt (fun w => immersionComplexCoefficient (Y ∘ periodTorusProjection L) w 2) 0=(-2:ℤ))
    (gauss : meromorphicOrderAt (immersionGaussLogDerivative (Y ∘ periodTorusProjection L)) 0=(-2:ℤ))
    {α : ℝ} (pitch : α≠0) (asymptote : ApproachesSetAtInfinity (range (axisRuledHelicoid I α 0)) (range X)) :
    Nonempty (PublishedConformalPoleModel X) := by
  let π := periodTorusProjection L
  obtain ⟨e,he,ev⟩ := periodTorusProjection_isLocalHomeomorph L 0
  have e0 : e 0=0 := (congrFun ev 0).symm.trans ((periodTorusProjection_eq_zero L 0).mpr L.lattice.zero_mem)
  have localChart : e.symm∈atlas ℂ (PeriodTorus L) := ev.symm
  have iso : IsothermalAwayFromPoint Y (0:PeriodTorus L) := by
    intro c hc w _ non
    change (c.symm : ℂ → PeriodTorus L)=π at hc
    rw [hc] at non ⊢
    obtain ⟨h,i,j⟩ := regular w (fun a => non ((periodTorusProjection_eq_zero L w).mpr a))
    exact ⟨(analyticAt_pi_iff.mpr fun k => _root_.HarmonicAt.analyticAt (h k)).contDiffAt,j,i⟩
  have frame : (fun q : PeriodTorus L => (0 : Fin 3 → ℝ)+(LinearEquiv.refl ℝ (Fin 3 → ℝ)) (Y q)) ∘ e=Y ∘ π := by
    funext z
    simp only [Function.comp_apply,LinearEquiv.refl_apply,zero_add]
    exact congrArg Y (congrFun ev z).symm
  refine ⟨{ model := PeriodTorus L, point := 0, marking := f, spatial := Y, agrees := pos, isothermal := iso,
            frame := LinearEquiv.refl ℝ _, orthogonal := fun _ _ => rfl, offset := 0,
            chart := e.symm, holomorphic := IsManifold.subset_maximalAtlas localChart,
            end_mem := e0 ▸ e.map_source he, centered := e0 ▸ e.left_inv he,
            height := ?_, heightOrder := ?_, gauss := ?_, gaussOrder := ?_, pitch := α, pitch_ne := pitch,
            asymptote := ?_ }⟩
  · rw [show (e.symm.symm : ℂ → PeriodTorus L)=e from rfl,frame]
    exact meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [height]; norm_num)
  · rw [show (e.symm.symm : ℂ → PeriodTorus L)=e from rfl,frame,height]
    norm_num
  · rw [show (e.symm.symm : ℂ → PeriodTorus L)=e from rfl,frame]
    exact meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [gauss]; norm_num)
  · rw [show (e.symm.symm : ℂ → PeriodTorus L)=e from rfl,frame,gauss]
    norm_num
  · simpa only [LinearEquiv.refl_apply,zero_add] using asymptote

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_end_pole_model
