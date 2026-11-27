import TwoAxisHelicoid.CentralHalfPeriodSpatialSeparation
import TwoAxisHelicoid.ActualCentralHalfSlice
import TwoAxisHelicoid.QuarterRowSpatialVelocity

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The two Gauss signs on the open saddle-to-midpoint half-arc suffice
for the entire central level to be spatially embedded. The absolute
positions of the arc follow from its endpoint and reflection. -/
theorem central_level_injective_of_gauss_quadrant {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z)
    (mark : X 1 1<X ((1+I*t)/2) 1) :
    let L := rhombicPeriodPair t ht
    let Y := fun q : PuncturedPeriodTorus L => periodTorusLift L X per q.1
    (∀ y∈Ioo 0 (t/2), ∀ x∈Ioo (0:ℝ) 1, X ((x:ℂ)+I*y) 2=X 1 2 →
      (thetaGauss t a 1 ((x:ℂ)+I*y)).re<0 ∧ (thetaGauss t a 1 ((x:ℂ)+I*y)).im<0) →
    InjOn Y {q | Y q 2=X 1 2} := by
  intro L Y signs
  obtain ⟨r,spec,cr,near,test⟩ := actual_central_half_slice_test ht ha d per mark
  let Z := fun y : ℝ => (r y:ℂ)+I*y
  let A := fun y => X (Z y) 0-X 1 0
  let B := fun y => X (Z y) 1-X 1 1
  let J := Ioc (0:ℝ) (t/2)
  have sub : J⊆Ioo 0 t := fun _ hy => ⟨hy.1,hy.2.trans_lt (half_lt_self ht)⟩
  have openSub : Ioo 0 (t/2)⊆J := fun _ hy => ⟨hy.1,hy.2.le⟩
  have off (y : ℝ) (hy : y∈Ioo 0 t) : Z y∉L.lattice := rhombic_horizontal_strip_not_mem ht (by
    change (Z y).im∈Ioo 0 t
    simpa [Z] using hy)
  have cont (y : ℝ) (hy : y∈Ioo 0 t) : ContinuousAt Z y :=
    (continuous_ofReal.continuousAt.comp ((cr y hy).continuousAt (isOpen_Ioo.mem_nhds hy))).add (continuous_const.mul continuous_ofReal).continuousAt
  have cj (j : Fin 3) : ContinuousOn (fun y => X (Z y) j-X 1 j) J := fun y hy =>
    (((continuous_apply j).continuousAt.comp ((d _ (off y (sub hy))).continuousAt.comp (cont y (sub hy)))).sub continuousAt_const).continuousWithinAt
  have speeds (y : ℝ) (hy : y∈interior J) : deriv A y<0 ∧ 0<deriv B y := by
    change y∈interior (Ioc 0 (t/2)) at hy
    rw [interior_Ioc] at hy
    have i := sub (openSub hy)
    obtain ⟨gr,gi⟩ := signs _ hy _ (spec y i).1 (spec y i).2
    obtain ⟨k,kp,v⟩ := quarter_row_spatial_velocity ht ha d ((cr y i).continuousAt (isOpen_Ioo.mem_nhds i)) i (spec y i).1
      (s:=0) (by
        filter_upwards [isOpen_Ioo.mem_nhds i] with u hu
        rw [← actual_complex_height_centered_primitive ht d (off u hu),(spec u hu).2,sub_self])
    refine ⟨((hasDerivAt_pi.mp v 0).sub_const (X 1 0)).deriv.trans_lt (mul_neg_of_pos_of_neg kp gi),?_⟩
    exact ((hasDerivAt_pi.mp v 1).sub_const (X 1 1)).deriv.symm ▸ mul_pos_of_neg_of_neg (neg_lt_zero.mpr kp) gr
  have dec : StrictAntiOn A J := strictAntiOn_of_deriv_neg (convex_Ioc _ _) (cj 0) (fun y hy => (speeds y hy).1)
  have inc : StrictMonoOn B J := strictMonoOn_of_deriv_pos (convex_Ioc _ _) (cj 1) (fun y hy => (speeds y hy).2)
  have mid : t/2∈J := right_mem_Ioc.mpr (half_pos ht)
  obtain ⟨r₀,cs,_,_,_,_,rm⟩ := actual_central_height_arc ht ha d per
  have rr := ((cs _ (sub mid)).2 _ (spec _ (sub mid)).1).mp (spec _ (sub mid)).2
  have zr : Z (t/2)=(1+I*t)/2 := by dsimp [Z]; rw [rr,rm]; push_cast; ring
  have he := congrFun (central_half_period_spatial_test ht d per).2.2.2.1 0
  have zero : A (t/2)=0 := by dsimp [A]; rw [zr]; exact he
  apply test.mpr
  refine ⟨fun _ hu _ hv e => dec.injOn hu hv (congrArg Prod.fst e),fun y hy => zero ▸ dec (openSub hy) mid hy.2,?_⟩
  intro y hy
  have e : ∀ᶠ v : ℝ in 𝓝[>] 0, v∈Ioo 0 y ∧ 0<B v := by
    filter_upwards [Ioo_mem_nhdsGT hy.1,near] with v hv h using ⟨hv,h.2⟩
  obtain ⟨v,hv,b⟩ := e.exists
  exact b.trans (inc ⟨hv.1,hv.2.le.trans hy.2⟩ hy hv.2)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_level_injective_of_gauss_quadrant
