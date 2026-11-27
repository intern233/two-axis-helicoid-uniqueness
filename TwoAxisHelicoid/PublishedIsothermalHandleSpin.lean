import TwoAxisHelicoid.TopologicalHandleIsothermalCover
import TwoAxisHelicoid.RealPeriodTorusRemarking

namespace TwoAxisHelicoid
open Complex Matrix Set Filter Topology
open scoped Topology Manifold ContDiff
universe u v

/-- The classical local isothermal coordinate theorem, expressed for smooth
positive metric coefficients on an open subset of the real plane. DeTurck
and Kazdan, Ann. Sci. ENS 14 (1981), Lemma 1.2 and the paragraph following
its proof on p. 251. This is a proposition used as an explicit premise. -/
def LocalSmoothMetricIsothermalCoordinates : Prop :=
  ∀ (U : Set ℂ), IsOpen U → ∀ E F G : ℂ → ℝ,
    (∀ z∈U, ContDiffAt ℝ ∞ E z ∧ ContDiffAt ℝ ∞ F z ∧ ContDiffAt ℝ ∞ G z ∧
      0<E z ∧ (F z)^2<E z*G z) →
    ∀ z∈U, ∃ k : OpenPartialHomeomorph ℂ ℂ, z∈k.source ∧ k.source⊆U ∧
      ∀ w∈k.target, ContDiffAt ℝ ∞ k.symm w ∧ ∃ a : ℝ, 0<a ∧ ∀ v : ℂ,
        let p := k.symm w
        let V := fderiv ℝ k.symm w v
        E p*V.re^2+2*F p*V.re*V.im+G p*V.im^2=a*normSq v

private noncomputable def inducedPlaneMetricCoeff (Y : ℂ → Fin 3 → ℝ) (v w : ℂ) (z : ℂ) : ℝ :=
  fderiv ℝ Y z v ⬝ᵥ fderiv ℝ Y z w

private theorem induced_metric_coeff_smooth {Y : ℂ → Fin 3 → ℝ} {z : ℂ}
    (smooth : ContDiffAt ℝ ∞ Y z) (v w : ℂ) :
    ContDiffAt ℝ ∞ (inducedPlaneMetricCoeff Y v w) z := by
  have deriv := smooth.fderiv_right (m:=∞) (by simp)
  have term (a : ℂ) (j : Fin 3) : ContDiffAt ℝ ∞ (fun p => fderiv ℝ Y p a j) z :=
    ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt).comp _ (deriv.clm_apply contDiffAt_const)
  unfold inducedPlaneMetricCoeff dotProduct
  simp only [Fin.sum_univ_three]
  exact (((term v 0).mul (term w 0)).add ((term v 1).mul (term w 1))).add ((term v 2).mul (term w 2))

private theorem physical_metric_form (D : ℂ →L[ℝ] (Fin 3 → ℝ)) (v : ℂ) :
    D v ⬝ᵥ D v=(D 1 ⬝ᵥ D 1)*v.re^2+2*(D 1 ⬝ᵥ D I)*v.re*v.im+(D I ⬝ᵥ D I)*v.im^2 := by
  rw [real_linear_complex_expansion D v]
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [dotProduct_comm (D I) (D 1)]
  ring

/-- Smoothness, positive definiteness of the induced metric, and transfer
of its local coordinates back to the very same position are checked here. -/
theorem local_metric_charts_of_published_isothermal (existsChart : LocalSmoothMetricIsothermalCoordinates)
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {X : M → Fin 3 → ℝ} (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (di : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x)) (x : M) :
    ∃ e : OpenPartialHomeomorph M ℂ, UnorientedLocalMetricChart X e ∧ x∈e.source := by
  let e := chartAt ℂ x
  let Y := X ∘ e.symm
  let E := inducedPlaneMetricCoeff Y 1 1
  let F := inducedPlaneMetricCoeff Y 1 I
  let G := inducedPlaneMetricCoeff Y I I
  have reg : RegularImmersionChart X e := smooth_surface_regular_manifold_chart sm di x
  have positive (v : Fin 3 → ℝ) (nz : v≠0) : 0<v ⬝ᵥ v :=
    lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => mul_self_nonneg _) (fun h => nz (dotProduct_self_eq_zero.mp h.symm))
  have metric (z : ℂ) (hz : z∈e.target) : ContDiffAt ℝ ∞ E z ∧ ContDiffAt ℝ ∞ F z ∧
      ContDiffAt ℝ ∞ G z ∧ 0<E z ∧ (F z)^2<E z*G z := by
    obtain ⟨smooth,inj⟩ := reg z hz
    let D := fderiv ℝ Y z
    have A : D 1≠0 := fun hh => one_ne_zero (inj (hh.trans D.map_zero.symm))
    have N : D 1 ⨯₃ D I≠0 := surfaceTangentCross_ne_zero_of_injective inj
    refine ⟨induced_metric_coeff_smooth smooth 1 1,induced_metric_coeff_smooth smooth 1 I,
      induced_metric_coeff_smooth smooth I I,positive _ A,?_⟩
    have h := positive _ N
    rw [cross_dot_cross,dotProduct_comm (D I) (D 1),← pow_two] at h
    exact sub_pos.mp h
  have ex : x∈e.source := mem_chart_source ℂ x
  obtain ⟨k,atx,sub,data⟩ := existsChart e.target e.open_target E F G metric (e x) (e.map_source ex)
  let d := e.trans k
  have patch (w : ℂ) (hw : w∈d.target) : ContDiffAt ℝ ∞ (X ∘ d.symm) w ∧
      ∃ a : ℝ, 0<a ∧ ∀ v : ℂ, fderiv ℝ (X ∘ d.symm) w v ⬝ᵥ fderiv ℝ (X ∘ d.symm) w v=a*normSq v := by
    obtain ⟨si,a,ap,eq⟩ := data w hw.1
    have sy := (reg (k.symm w) (sub (k.map_target hw.1))).1
    refine ⟨sy.comp w si,a,ap,?_⟩
    intro v
    change fderiv ℝ (Y ∘ k.symm) w v ⬝ᵥ fderiv ℝ (Y ∘ k.symm) w v=_
    rw [fderiv_comp w (sy.differentiableAt (by simp)) (si.differentiableAt (by simp))]
    exact (physical_metric_form (fderiv ℝ Y (k.symm w)) (fderiv ℝ k.symm w v)).trans (eq v)
  refine ⟨d,⟨?_,fun w hw => (patch w hw).2⟩,ex,atx⟩
  intro w hw
  obtain ⟨s,a,ap,conformal⟩ := patch w hw
  exact ⟨s,(conformal_immersion_of_metric_factor _ ap conformal).2.2⟩

/-- The prescribed topological target torus itself admits a smooth marking
for the original surface and the unique even spin extension. The only
geometric input from the literature is the local theorem for plane metrics. -/
theorem prescribed_handle_spin_of_local_isothermal_theorem (dk : LocalSmoothMetricIsothermalCoordinates)
    {M : Type v} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ,ℂ) ∞ M]
    {L : PeriodPair} (top : M ≃ₜ PuncturedPeriodTorus L) (X : M → Fin 3 → ℝ) (cl : IsClosedEmbedding X)
    (sm : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ X)
    (di : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) X x))
    (A : (Fin 3 → ℝ) ≃ₜ HelicoidTubeCoordinates) (sa : ContDiff ℝ ∞ A) (si : ContDiff ℝ ∞ A.symm)
    (height : HasHelicoidHeightEnd (A ∘ X)) :
    ∃ e : Diffeomorph 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) M (PuncturedPeriodTorus L) ∞, EvenSpinExtensionInMarking.{u} X e := by
  let _ : T2Space M := cl.isEmbedding.t2Space
  obtain ⟨L',⟨g⟩⟩ := smooth_marking_of_unoriented_local_metric_charts top sm di
    (local_metric_charts_of_published_isothermal dk sm di)
  obtain ⟨_,_,f,_⟩ := prescribed_punctured_period_torus_diffeomorphism L' L
  exact ⟨g.trans f,abstract_helicoidal_surface_even_in_smooth_marking X cl sm di A sa si height (g.trans f)⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.local_metric_charts_of_published_isothermal
#print axioms TwoAxisHelicoid.prescribed_handle_spin_of_local_isothermal_theorem

