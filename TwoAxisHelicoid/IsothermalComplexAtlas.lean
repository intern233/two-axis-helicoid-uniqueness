import TwoAxisHelicoid.OrientedIsothermalCoordinates
import TwoAxisHelicoid.ImmersionAtlas

namespace TwoAxisHelicoid
open Complex Matrix Filter Set
open scoped Topology ContDiff Manifold
set_option maxHeartbeats 1300000

noncomputable def surfaceTangentCross (X : ℂ → Fin 3 → ℝ) (z : ℂ) : Fin 3 → ℝ :=
  (fderiv ℝ X z 1) ⨯₃ (fderiv ℝ X z I)

noncomputable def planeRealJacobian (L : ℂ →L[ℝ] ℂ) : ℝ :=
  (L 1).re*(L I).im-(L 1).im*(L I).re

theorem surfaceTangentCross_coordinate_change {X Y : ℂ → Fin 3 → ℝ} {f : ℂ → ℂ} {z : ℂ}
    (h : X =ᶠ[𝓝 z] (Y ∘ f)) (hY : DifferentiableAt ℝ Y (f z)) (hf : DifferentiableAt ℝ f z) :
    surfaceTangentCross X z = (planeRealJacobian (fderiv ℝ f z)) • surfaceTangentCross Y (f z) := by
  let L := fderiv ℝ f z
  let D := fderiv ℝ Y (f z)
  have he (v : ℂ) : fderiv ℝ X z v = D (L v) := by
    rw [h.fderiv_eq,fderiv_comp z hY hf]
    rfl
  unfold surfaceTangentCross
  rw [he,he,real_linear_complex_expansion D (L 1),real_linear_complex_expansion D (L I)]
  exact cross_product_two_basis_changes _ _ _ _ _ _

variable {M : Type*} [TopologicalSpace M]

/-- A genuine real immersion chart orthogonal in equal scale, with its
orientation fixed by a transverse ambient vector field. -/
def OrientedIsothermalChart (F N : M → Fin 3 → ℝ) (e : OpenPartialHomeomorph M ℂ) : Prop :=
  RegularImmersionChart F e ∧ ∀ y ∈ e.target,
    (∃ a : ℝ, 0 < a ∧ ∀ v : ℂ, let L := fderiv ℝ (F ∘ e.symm) y
      L v ⬝ᵥ L v = a*normSq v) ∧ 0 < surfaceTangentCross (F ∘ e.symm) y ⬝ᵥ N (e.symm y)

theorem isothermalChart_holomorphic_transition {F N : M → Fin 3 → ℝ}
    {e e' : OpenPartialHomeomorph M ℂ} (he : OrientedIsothermalChart F N e)
    (he' : OrientedIsothermalChart F N e') {y : ℂ} (hy : y ∈ (e.symm.trans e').source) :
    DifferentiableAt ℂ (e.symm.trans e') y := by
  let f := e.symm.trans e'
  have hfy : f y ∈ e'.target := e'.map_source hy.2
  have hY := (he'.1 _ hfy).1.differentiableAt (by simp)
  have hf := (regularImmersionChart_transition he.1 he'.1 hy).differentiableAt (by simp)
  have h : (F ∘ e.symm) =ᶠ[𝓝 y] ((F ∘ e'.symm) ∘ f) := by
    filter_upwards [f.open_source.mem_nhds hy] with w hw
    exact congrArg F (e'.left_inv hw.2).symm
  obtain ⟨⟨a,ha,hx⟩,hu⟩ := he.2 y hy.1
  obtain ⟨⟨b,hb,hy'⟩,hv⟩ := he'.2 (f y) hfy
  apply oriented_isothermal_transition_differentiableAt h hY hf ha hb hx hy'
  let V := surfaceTangentCross (F ∘ e'.symm) (f y)
  let d := planeRealJacobian (fderiv ℝ f y)
  have hcross : surfaceTangentCross (F ∘ e.symm) y = d • V :=
    surfaceTangentCross_coordinate_change h hY hf
  have hV : 0 < V ⬝ᵥ N (e.symm y) := by
    change 0 < V ⬝ᵥ N (e'.symm (e' (e.symm y))) at hv
    have hsrc : e.symm y ∈ e'.source := hy.2
    rwa [e'.left_inv hsrc] at hv
  rw [hcross,smul_dotProduct,smul_eq_mul] at hu
  have hd : 0 < d := pos_of_mul_pos_left hu hV.le
  have hVV : 0 < V ⬝ᵥ V := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (V i)) (by
    intro hh
    have hw := dotProduct_self_eq_zero.mp hh.symm
    rw [hw,zero_dotProduct] at hV
    exact lt_irrefl _ hV)
  change 0 < surfaceTangentCross (F ∘ e.symm) y ⬝ᵥ V
  rw [hcross,smul_dotProduct,smul_eq_mul]
  exact mul_pos hd hVV

@[instance_reducible] noncomputable def isothermalComplexAtlas (F N : M → Fin 3 → ℝ)
    (hcover : ∀ x : M, ∃ e : OpenPartialHomeomorph M ℂ, OrientedIsothermalChart F N e ∧ x ∈ e.source) :
    ChartedSpace ℂ M where
  atlas := {e | OrientedIsothermalChart F N e}
  chartAt x := (hcover x).choose
  mem_chart_source x := (hcover x).choose_spec.2
  chart_mem_atlas x := (hcover x).choose_spec.1

/-- The induced oriented isothermal atlas is a complex analytic
one-dimensional manifold in mathlib's standard sense. -/
theorem isothermalComplexAtlas_isManifold (F N : M → Fin 3 → ℝ)
    (hcover : ∀ x : M, ∃ e : OpenPartialHomeomorph M ℂ, OrientedIsothermalChart F N e ∧ x ∈ e.source) :
    let _ := isothermalComplexAtlas F N hcover
    IsManifold 𝓘(ℂ,ℂ) ω M := by
  let _ := isothermalComplexAtlas F N hcover
  apply isManifold_of_contDiffOn
  intro e e' he he' y hy
  have hh : DifferentiableOn ℂ (e.symm.trans e') (e.symm.trans e').source :=
    fun w hw => (isothermalChart_holomorphic_transition he he' hw).differentiableWithinAt
  exact (hh.analyticAt ((e.symm.trans e').open_source.mem_nhds hy.1)).contDiffAt.contDiffWithinAt

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.isothermalComplexAtlas_isManifold
