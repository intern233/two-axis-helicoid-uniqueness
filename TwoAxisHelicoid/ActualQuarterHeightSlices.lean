import TwoAxisHelicoid.RhombicQuarterHeight
import TwoAxisHelicoid.WeierstrassVerticalDomain
import TwoAxisHelicoid.ExplicitEmbeddedAxes
import TwoAxisHelicoid.RealDerivativeSign

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- Along every horizontal parameter row the actual height increases
through the entire closed width of the first rectangle. -/
theorem actual_quarter_height_row_strictMono {t a y : ℝ} (ht : 0<t) (hy : y∈Ioo 0 t)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht) :
    StrictMonoOn (fun x : ℝ => X ((x:ℂ)+I*y) 2) (Icc 0 1) := by
  let L := rhombicPeriodPair t ht
  let z := fun x : ℝ => (x:ℂ)+I*y
  have off (x : ℝ) : z x∉L.lattice := rhombic_horizontal_strip_not_mem ht
    (by change (z x).im∈Ioo 0 t; simpa [z] using hy)
  have der (x : ℝ) : HasDerivAt (fun u : ℝ => X (z u) 2) (-(L.weierstrassP (z x)).im) x := by
    have line := (hasDerivAt_id x).ofReal_comp.add_const (I*(y:ℂ))
    have h := (actual_coordinate_primitive_component ht d (off x) 2).comp_hasDerivAt x line
    change HasDerivAt _ (realCoefficientDerivative (I*(1:ℂ)*(L.weierstrassP (z x)-L.weierstrassP a)) (1:ℂ)) x at h
    simpa [z,Function.comp_def,realCoefficientDerivative_apply,Complex.mul_re,rhombic_weierstrassP_real ht a,L] using h
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun x _ => (der x).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  rw [(der x).deriv]
  exact neg_pos.mpr (rhombic_weierstrassP_quarter_im_neg ht hx hy)

/-- The physical height on the marked vertical axis has its natural
increasing orientation, including both sides of the axial crossing. -/
theorem actual_vertical_axis_height_strictMono {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht) :
    StrictMonoOn (fun y : ℝ => X (1+I*y) 2) (Ioo (-t) t) := by
  let V := fun y : ℝ => (I*coordinateData t a 1 ht (1+I*y) 2).re
  have der (y : ℝ) (hy : y∈Ioo (-t) t) := actual_primitive_vertical_hasDerivAt ht d hy 2
  have cd : ContinuousOn V (Ioo (-t) t) := by
    intro y hy
    have c := (coordinateData_analyticAt (a:=a) (c:=1) ht (rhombic_vertical_axis_not_mem ht hy)).continuousAt
    have line : ContinuousAt (fun s : ℝ => (1:ℂ)+I*s) y := by fun_prop
    exact (Complex.continuous_re.continuousAt.comp (continuousAt_const.mul ((continuous_apply 2).continuousAt.comp (c.comp (f:=fun s : ℝ => (1:ℂ)+I*s) line)))).continuousWithinAt
  have zero : (0:ℝ)∈Ioo (-t) t := ⟨neg_lt_zero.mpr ht,ht⟩
  have initial : 0<V 0 := by
    have h := rhombic_weierstrassP_strictAnti_to_one ht (show a∈Ioc (0:ℝ) 1 from ⟨ha.1,ha.2.le⟩)
      (show (1:ℝ)∈Ioc 0 1 by norm_num) ha.2
    change ((rhombicPeriodPair t ht).weierstrassP (1:ℝ)).re < ((rhombicPeriodPair t ht).weierstrassP a).re at h
    simpa [V,coordinateData,Complex.mul_re,Complex.mul_im] using sub_pos.mpr h
  have signs := continuous_nonzero_constant_sign isPreconnected_Ioo ⟨0,zero⟩ cd
    (fun y hy => coordinateData_vertical_axis_regular ht ha one_ne_zero hy)
  have pos := signs.resolve_right (fun all => initial.not_gt (all 0 zero))
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _) (fun y h => (der y h).continuousAt.continuousWithinAt)
  intro y hy
  rw [isOpen_Ioo.interior_eq] at hy
  exact (der y hy).deriv.symm ▸ pos y hy

/-- All physical heights occurring on a closed horizontal parameter row
are exactly the interval between its two points on the vertical axis.
Every such height has a unique preimage on that row. -/
theorem actual_quarter_row_level_iff {t a y H : ℝ} (ht : 0<t) (hy : y∈Ioo 0 t)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) :
    (∃! x : ℝ, x∈Icc (0:ℝ) 1 ∧ X ((x:ℂ)+I*y) 2=H) ↔
      H∈Icc (X (1+I*(y-t:ℝ)) 2) (X (1+I*y) 2) := by
  let f := fun x : ℝ => X ((x:ℂ)+I*y) 2
  have mono := actual_quarter_height_row_strictMono ht hy d
  have zero : (0:ℝ)∈Icc (0:ℝ) 1 := by norm_num
  have one : (1:ℝ)∈Icc (0:ℝ) 1 := by norm_num
  have period : (-1+I*(t:ℂ))∈(rhombicPeriodPair t ht).lattice := by
    apply (rhombic_mem_lattice_iff ht _).mpr
    exact ⟨-1,1,by norm_num,by simp⟩
  have edge : f 0=X (1+I*(y-t:ℝ)) 2 := by
    have e := congrFun (per (1+I*(y-t:ℝ)) _ period) 2
    rw [show (1:ℂ)+I*(y-t:ℝ)+(-1+I*t)=I*y by push_cast; ring] at e
    simpa only [f,ofReal_zero,zero_add] using e
  have right : f 1=X (1+I*y) 2 := by simp [f]
  rw [← edge,← right]
  constructor
  · rintro ⟨x,⟨hx,eq⟩,_⟩
    exact eq ▸ ⟨mono.monotoneOn zero hx hx.1,mono.monotoneOn hx one hx.2⟩
  · intro inside
    have cont : ContinuousOn f (Icc 0 1) := by
      intro x _
      have line : ContinuousAt (fun u : ℝ => (u:ℂ)+I*y) x := by fun_prop
      have off := rhombic_horizontal_strip_not_mem (z:=(x:ℂ)+I*y) ht (by change _∈Ioo 0 t; simpa using hy)
      exact ((actual_coordinate_primitive_component ht d off 2).continuousAt.comp (f:=fun u : ℝ => (u:ℂ)+I*y) line).continuousWithinAt
    obtain ⟨x,hx,eq⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num) cont inside
    exact ⟨x,⟨hx,eq⟩,fun u hu => mono.injOn hu.1 hx (hu.2.trans eq.symm)⟩

/-- In particular each open row crosses the central spatial plane
exactly once in the interior of the rectangle. -/
theorem actual_quarter_central_plane_unique {t a y : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hy : y∈Ioo 0 t)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) :
    ∃! x : ℝ, x∈Ioo (0:ℝ) 1 ∧ X ((x:ℂ)+I*y) 2=X 1 2 := by
  have mono := actual_vertical_axis_height_strictMono ht ha d
  have zero : (0:ℝ)∈Ioo (-t) t := ⟨neg_lt_zero.mpr ht,ht⟩
  have left := mono (show y-t∈Ioo (-t) t from ⟨by linarith [hy.1],by linarith [hy.2]⟩) zero (sub_neg.mpr hy.2)
  have right := mono zero (show y∈Ioo (-t) t from ⟨by linarith [hy.1],hy.2⟩) hy.1
  simp only [ofReal_zero,mul_zero,add_zero] at left right
  obtain ⟨x,⟨hx,eq⟩,unique⟩ := (actual_quarter_row_level_iff ht hy d per).mpr ⟨left.le,right.le⟩
  have p : (-1+I*(t:ℂ))∈(rhombicPeriodPair t ht).lattice := (rhombic_mem_lattice_iff ht _).mpr ⟨-1,1,by norm_num,by simp⟩
  have edge := per (1+I*(y-t:ℝ)) _ p
  rw [show (1:ℂ)+I*(y-t:ℝ)+(-1+I*t)=I*y by push_cast; ring] at edge
  refine ⟨x,⟨⟨lt_of_le_of_ne hx.1 ?_,lt_of_le_of_ne hx.2 ?_⟩,eq⟩,fun u hu => unique u ⟨⟨hu.1.1.le,hu.1.2.le⟩,hu.2⟩⟩
  · rintro rfl
    simp only [ofReal_zero,zero_add] at eq
    exact left.ne ((congrFun edge 2).symm.trans eq)
  · rintro rfl
    exact right.ne (by simpa using eq.symm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_quarter_row_level_iff
#print axioms TwoAxisHelicoid.actual_quarter_central_plane_unique
