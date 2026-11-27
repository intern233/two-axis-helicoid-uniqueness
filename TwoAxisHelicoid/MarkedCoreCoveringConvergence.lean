import TwoAxisHelicoid.RegularCoveringCoreCharts
import TwoAxisHelicoid.SpatialCoreTorusMarking

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff Manifold

theorem covering_marking_core_equiv {B : Type*} [TopologicalSpace B] {A : PeriodPair}
    (m : B ≃ₜ PuncturedPeriodTorus A) (C : TorusGeneratingCoreModel A) :
    let V := {b : B | (m b).1∈C.carrier}
    ∃ e : V ≃ₜ C.carrier, ∀ b, (e b).1=(m b.1).1 := by
  intro V
  let j := (Subtype.val : PuncturedPeriodTorus A → PeriodTorus A) ∘ m
  have embed : IsEmbedding j := IsEmbedding.subtypeVal.comp m.isEmbedding
  let f := fun q : V => (⟨j q.1,q.2⟩ : C.carrier)
  have emb : IsEmbedding f := (embed.comp IsEmbedding.subtypeVal).codRestrict C.carrier (fun q : V => q.2)
  have sur : Function.Surjective f := by
    intro y
    have ny : y.1≠0 := fun eq => C.closure_avoids (eq ▸ subset_closure y.2)
    let b := m.symm ⟨y.1,ny⟩
    have eq : j b=y.1 := congrArg Subtype.val (m.apply_symm_apply ⟨y.1,ny⟩)
    exact ⟨⟨b,by change j b∈C.carrier; rw [eq]; exact y.2⟩,Subtype.ext eq⟩
  exact ⟨emb.toHomeomorphOfSurjective sur,fun _ => rfl⟩

noncomputable def coveringCoreParameter {A : PeriodPair} (C : TorusGeneratingCoreModel A) (z : ℂ) : C.carrier := by
  classical
  exact if h : periodTorusProjection A z∈C.carrier then ⟨_,h⟩ else C.base

theorem coveringCoreParameter_val {A : PeriodPair} (C : TorusGeneratingCoreModel A) {z : ℂ}
    (hz : periodTorusProjection A z∈C.carrier) : (coveringCoreParameter C z).1=periodTorusProjection A z := by
  classical
  simp only [coveringCoreParameter,dite_eq_left hz]

/-- Local C¹ estimates in every regular physical chart give a single
locally uniformly converging derivative on the full covering plane
above the genus-one core with its actual periods. -/
theorem marked_core_covering_C1 {B : Type*} [TopologicalSpace B] {A : PeriodPair}
    (m : B ≃ₜ PuncturedPeriodTorus A) (C : TorusGeneratingCoreModel A)
    (X : B → Fin 3 → ℝ) (Y : PeriodTorus A → Fin 3 → ℝ) (pos : ∀ x, Y (m x).1=X x)
    (regular : ∀ z∉A.lattice, ContDiffAt ℝ ∞ (Y ∘ periodTorusProjection A) z ∧
      Function.Injective (fderiv ℝ (Y ∘ periodTorusProjection A) z)) :
    let V := {b : B | (m b).1∈C.carrier}
    ∀ (e : V ≃ₜ C.carrier) (_ : ∀ b, (e b).1=(m b.1).1) (b : V) (F : ℕ → V → SurfaceEuclideanSpace),
    (∀ a : OpenPartialHomeomorph B ℂ, RegularImmersionChart X a →
      let R := coreChartRegion V a
      let f := fun n => F n ∘ coreChartParameter V b a
      (∀ n z, z∈R → ContDiffAt ℝ 1 (f n) z) ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℝ (f n)) (fderiv ℝ (coordinateToEuclidean ∘ X ∘ a.symm)) atTop R) →
    let Z := fun n => F n ∘ e.symm ∘ coveringCoreParameter C
    let Z₀ := coordinateToEuclidean ∘ Y ∘ periodTorusProjection A
    let U := periodTorusProjection A ⁻¹' C.carrier
    (∀ n w, w∈U → ContDiffAt ℝ 1 (Z n) w) ∧
      TendstoLocallyUniformlyOn (fun n => fderiv ℝ (Z n)) (fderiv ℝ Z₀) atTop U := by
  intro V e eq b F input Z Z₀ U
  have vo : IsOpen V := C.isOpen_carrier.preimage (continuous_subtype_val.comp m.continuous)
  apply covering_charts_glue_C1
  intro z hz
  have nz : z∉A.lattice := fun l => C.closure_avoids ((periodTorusProjection_eq_zero A z).mpr l ▸ subset_closure hz)
  obtain ⟨a,az,reg,lift⟩ := regular_chart_of_marked_covering m X Y pos regular z nz
  let R := coreChartRegion V a
  have ro : IsOpen R := coreChartRegion_open vo a
  have chart (w : ℂ) (h : w∈R) : periodTorusProjection A w∈C.carrier := (lift w h.1) ▸ h.2
  have atz : z∈R := ⟨az,by change (m (a.symm z)).1∈C.carrier; rw [lift z az]; exact hz⟩
  let p := coreChartParameter V b a
  have mark (w : ℂ) (h : w∈R) : e.symm (coveringCoreParameter C w)=p w := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [coveringCoreParameter_val C (chart w h),eq,coreChartParameter_val b a h,lift w h.1]
  have moving (n : ℕ) (w : ℂ) (h : w∈R) : Z n=ᶠ[𝓝 w] F n ∘ p :=
    Filter.mem_of_superset (ro.mem_nhds h) (fun t ht => congrArg (F n) (mark t ht))
  have ref (w : ℂ) (h : w∈R) : Z₀=ᶠ[𝓝 w] coordinateToEuclidean ∘ X ∘ a.symm :=
    Filter.mem_of_superset (ro.mem_nhds h) (fun t ht => congrArg coordinateToEuclidean ((congrArg Y (lift t ht.1)).symm.trans (pos _)))
  obtain ⟨sm,con⟩ := input a reg
  refine ⟨R,ro,atz,fun n w h => (sm n w h).congr_of_eventuallyEq (moving n w h),?_⟩
  exact (con.congr (fun n w h => (moving n w h).fderiv_eq.symm)).congr_right (fun w h => (ref w h).fderiv_eq.symm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_core_covering_C1
