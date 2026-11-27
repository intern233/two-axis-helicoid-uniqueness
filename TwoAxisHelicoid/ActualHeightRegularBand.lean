import TwoAxisHelicoid.ExplicitEmbeddedAxes
import TwoAxisHelicoid.PeriodicRegularLevelGap
import TwoAxisHelicoid.SmoothReciprocalVectorField
import TwoAxisHelicoid.ActualHeightEndOrder
import TwoAxisHelicoid.CoordinateDataSymmetry

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology

theorem actual_height_coefficient_at_lattice {t a c : ℝ} (ht : 0<t) (hc : c≠0)
    (p : ℂ) (hp : p∈(rhombicPeriodPair t ht).lattice) :
    let f := fun z => coordinateData t a c ht z 2
    MeromorphicAt f p ∧ Tendsto f (𝓝[≠] p) (cobounded ℂ) := by
  let L := rhombicPeriodPair t ht
  let k : ℂ := I*(c:ℂ)
  let b : ℂ → ℂ := fun _ => -L.weierstrassP a
  have hk : k≠0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hc)
  have mer := (analyticAt_const (v := k) (x := p) (𝕜 := ℂ)).meromorphicAt.mul
    ((L.meromorphic_weierstrassP p).add (show MeromorphicAt b p from analyticAt_const.meromorphicAt))
  have order := L.order_weierstrassP p hp
  have less : meromorphicOrderAt L.weierstrassP p < meromorphicOrderAt b p := by
    apply lt_of_lt_of_le _ (show 0≤meromorphicOrderAt b p from analyticAt_const.meromorphicOrderAt_nonneg)
    rw [order]
    exact WithTop.coe_lt_coe.mpr (by decide : (-2:ℤ)<0)
  have low : meromorphicOrderAt ((fun _ : ℂ => k)*(L.weierstrassP+b)) p<0 := by
    rw [meromorphicOrderAt_mul analyticAt_const.meromorphicAt ((L.meromorphic_weierstrassP p).add
      (show MeromorphicAt b p from analyticAt_const.meromorphicAt)),meromorphicOrderAt_const,ite_eq_right hk,zero_add,
      meromorphicOrderAt_add_eq_left_of_lt (show MeromorphicAt b p from analyticAt_const.meromorphicAt) less,order]
    exact WithTop.coe_lt_coe.mpr (by decide : (-2:ℤ)<0)
  exact ⟨mer,tendsto_cobounded_of_meromorphicOrderAt_neg low⟩

/-- The actual closed height differential has a uniform positive
lower bound on every band separated from the height of the two saddles.
Its inverse there agrees with a bounded smooth periodic field which fixes
the punctures. No global embedding hypothesis is used. -/
theorem actual_height_regular_band_field {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (period : ∀ z w, w∈(rhombicPeriodPair t ht).lattice → X (z+w)=X z) {ε : ℝ} (positive : 0<ε) :
    let L := rhombicPeriodPair t ht
    let f := fun z => coordinateData t a c ht z 2
    ∃ δ>0, ∃ V : ℂ → ℂ, ContDiff ℝ 1 V ∧ (∀ z, ‖V z‖≤(δ/2)⁻¹) ∧
      (∀ z w, w∈L.lattice → V (z+w)=V z) ∧ (∀ z∈L.lattice,V z=0) ∧
      (∀ z∉L.lattice, ε≤|X z 2-X 1 2| → δ≤‖f z‖ ∧ V z=(f z)⁻¹) ∧
      ∀ z∉L.lattice, ∃ k∈Icc (0:ℝ) 1, V z*f z=(k:ℂ) := by
  let L := rhombicPeriodPair t ht
  let f := fun z => coordinateData t a c ht z 2
  let h := fun z => X z 2-X 1 2
  have an (z : ℂ) (hz : z∉L.lattice) : AnalyticAt ℂ f z :=
    ((ContinuousLinearMap.proj 2 : (Fin 3 → ℂ) →L[ℂ] ℂ).analyticAt _).comp (coordinateData_analyticAt ht hz)
  have pf (z w : ℂ) (hw : w∈L.lattice) : f (z+w)=f z :=
    congrFun (coordinateData_add_lattice ht z ⟨w,hw⟩) 2
  have pole (z : ℂ) (hz : z∈L.lattice) := actual_height_coefficient_at_lattice (a := a) ht hc z hz
  have crit (z : ℂ) (hz : z∉L.lattice) (zero : f z=0) : h z=0 := by
    have eq := (actual_coordinate_primitive_component ht diff hz 2).fderiv
    have cz : fderiv ℝ (fun w => X w 2) z=0 := by
      rw [eq,show coordinateData t a c ht z 2=0 from zero]
      ext w
      simp
    obtain ⟨x,hx,_,_,same⟩ := actual_height_saddle_axis_representative ht ha hc diff period hz cz
    exact sub_eq_zero.mpr ((congrFun same 2).trans (actual_primitive_horizontal_line ht diff hx).2)
  obtain ⟨δ,hδ,hbound⟩ := periodic_regular_level_gap L f h (fun z hz => (an z hz).continuousAt)
    (fun z hz => (actual_coordinate_primitive_component ht diff hz 2).continuousAt.sub continuousAt_const) pf
    (fun z w hw => congrArg (fun v => v 2-X 1 2) (period z w hw))
    (fun z hz => tendsto_norm_atTop_iff_cobounded.mpr (pole z hz).2) crit positive
  obtain ⟨V,sm,b,p,vanish,inv,fac⟩ := smooth_bounded_lattice_reciprocal L f an (fun z hz => (pole z hz).1)
    (fun z hz => (pole z hz).2) pf hδ
  exact ⟨δ,hδ,V,sm,b,p,vanish,fun z hz hi => ⟨hbound z hz hi,inv z hz (hbound z hz hi)⟩,fac⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_height_regular_band_field
