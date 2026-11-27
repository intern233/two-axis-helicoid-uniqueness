import TwoAxisHelicoid.ActualQuarterHeightSlices
import TwoAxisHelicoid.RhombicCenteredRectangle
import TwoAxisHelicoid.HeightEndAxisCenter
import Mathlib.Topology.Maps.Proper.Basic

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- The positive horizontal level on the closed quarter of the fundamental
strip is a single continuous row graph. It starts on the vertical axis and
ends at the puncture, and its abscissa is interior on every intervening row. -/
theorem positive_quarter_height_ray {t a h : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hp : 0<h)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z) :
    let Z := fun (x y : ℝ) => (x:ℂ)+I*y
    ∃ b∈Ioo (0:ℝ) t, ∃ r : ℝ → ℝ, r b=1 ∧ ContinuousOn r (Ico b t) ∧ Tendsto r (𝓝[<] t) (𝓝 1) ∧
      (∀ y∈Ioo b t, r y∈Ioo (0:ℝ) 1) ∧
      ∀ y∈Ioo 0 t, ∀ x∈Icc (0:ℝ) 1, X (Z x y) 2=X 1 2+h ↔ b≤y ∧ x=r y := by
  classical
  intro Z
  let s := X 1 2+h
  let V := fun y : ℝ => X (1+I*y) 2
  let C := Icc (0:ℝ) 1
  have V0 : V 0=X 1 2 := by simp [V]
  have mono := actual_vertical_axis_height_strictMono ht ha d
  have hm : StrictMonoOn V (Ioo (-t) t) := mono
  have at0 : (0:ℝ)∈Ioo (-t) t := ⟨by linarith,ht⟩
  obtain ⟨b,bIn,eq⟩ := (actual_axes_coordinates_bijective ht ha one_ne_zero d).2.surjOn (mem_univ s)
  change V b=s at eq
  have above : V 0<s := by rw [V0]; dsimp [s]; linarith
  have bp : 0<b := (hm.lt_iff_lt at0 bIn).mp (above.trans_eq eq.symm)
  let J := Ico b t
  have within {y : ℝ} (hy : y∈J) : y∈Ioo 0 t := ⟨bp.trans_le hy.1,hy.2⟩
  have vmem {y : ℝ} (hy : y∈Ioo 0 t) : y∈Ioo (-t) t := ⟨by linarith [hy.1],hy.2⟩
  have lower {y : ℝ} (hy : y∈Ioo 0 t) : V (y-t)<s := by
    exact (hm (show y-t∈Ioo (-t) t from ⟨by linarith [hy.1],by linarith [hy.2]⟩) at0
      (sub_neg.mpr hy.2)).trans above
  have one (y : ℝ) (hy : y∈J) : ∃! x : ℝ, x∈C ∧ X (Z x y) 2=s :=
    (actual_quarter_row_level_iff ht (within hy) d per).mpr
      ⟨(lower (within hy)).le,eq ▸ hm.monotoneOn bIn (vmem (within hy)) hy.1⟩
  let r := fun y : ℝ => if e : y∈J then (one y e).choose else 1
  have root (y : ℝ) (hy : y∈J) : r y∈C ∧ X (Z (r y) y) 2=s := by
    simpa only [r,dite_eq_left hy] using (one y hy).choose_spec.1
  have unique (y : ℝ) (hy : y∈J) {x : ℝ} (hx : x∈C) (e : X (Z x y) 2=s) : x=r y :=
    (actual_quarter_height_row_strictMono ht (within hy) d).injOn hx (root y hy).1 (e.trans (root y hy).2.symm)
  have weight : (-1+I*(t:ℂ))∈(rhombicPeriodPair t ht).lattice :=
    (rhombic_mem_lattice_iff ht _).mpr ⟨-1,1,by norm_num,by simp⟩
  have left (y : ℝ) : X (Z 0 y) 2=V (y-t) := by
    have e := congrFun (per (1+I*(y-t:ℝ)) _ weight) 2
    rw [show (1:ℂ)+I*(y-t:ℝ)+(-1+I*t)=Z 0 y by dsimp [Z]; push_cast; ring] at e
    exact e
  have right (y : ℝ) : X (Z 1 y) 2=V y := by simp [Z,V]
  have cont : ContinuousOn r J := by
    let g : J → C := fun z => ⟨r z.1,(root _ z.2).1⟩
    have closedGraph : g.graph={v : J × C | X (Z v.2.1 v.1.1) 2=s} := by
      ext ⟨y,x⟩
      change g y=x ↔ X (Z x.1 y.1) 2=s
      exact ⟨fun a => a ▸ (show X (Z (g y).1 y.1) 2=s from (root _ y.2).2),fun e => Subtype.ext (unique _ y.2 x.2 e).symm⟩
    have F : Continuous (fun v : J × C => X (Z v.2.1 v.1.1) 2) := by
      apply continuous_iff_continuousAt.mpr
      intro v
      have off := rhombic_horizontal_strip_not_mem (z:=Z v.2.1 v.1.1) ht
        (by change (Z _ _).im∈Ioo 0 t; simpa [Z] using within v.1.2)
      have line : Continuous (fun v : J × C => Z v.2.1 v.1.1) := by dsimp [Z]; fun_prop
      exact ((actual_coordinate_primitive_component ht d off 2).continuousAt.comp (f:=fun v : J × C => Z v.2.1 v.1.1)
        (line.continuousAt (x:=v)))
    let _ : CompactSpace C := isCompact_iff_compactSpace.mp isCompact_Icc
    have cg : Continuous g := continuous_of_isClosed_graph (closedGraph ▸ isClosed_eq F continuous_const)
    exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp cg)
  have near : Tendsto r (𝓝[<] t) (𝓝 1) := by
    apply tendsto_order.mpr
    constructor
    · intro x hx
      obtain ⟨u,below,lt⟩ := exists_between (max_lt hx zero_lt_one)
      have up : 0<u := (le_max_right x 0).trans_lt below
      have real : u+1∈Ioo (0:ℝ) 2 := ⟨by linarith,by linarith⟩
      have ou := real_not_mem_rhombic_lattice_of_pos ht real.1 real.2
      have pos : Z u t=((u+1:ℝ):ℂ)+(-1+I*t) := by dsimp [Z]; push_cast; ring
      have off : Z u t∉(rhombicPeriodPair t ht).lattice := by
        rw [pos]
        exact fun m => ou (by simpa using (rhombicPeriodPair t ht).lattice.sub_mem m weight)
      have cv : ContinuousAt (fun y => X (Z u y) 2) t :=
        (actual_coordinate_primitive_component ht d off 2).continuousAt.comp (f:=Z u) (by dsimp [Z]; fun_prop)
      have v : X (Z u t) 2<s := by
        rw [pos,per _ _ weight,(actual_primitive_horizontal_line ht d real).2]
        exact V0 ▸ above
      filter_upwards [Ioo_mem_nhdsLT bIn.2,(cv.eventually (Iio_mem_nhds v)).filter_mono nhdsWithin_le_nhds] with y hy hy'
      have inJ : y∈J := ⟨hy.1.le,hy.2⟩
      have lowerR := (actual_quarter_height_row_strictMono ht (within inJ) d).lt_iff_lt
        (show u∈C from ⟨up.le,lt.le⟩) (root y inJ).1
      exact (le_max_left x 0).trans_lt (below.trans (lowerR.mp (hy'.trans_eq (root y inJ).2.symm)))
    · intro v hv
      filter_upwards [Ioo_mem_nhdsLT bIn.2] with y hy using ((root y ⟨hy.1.le,hy.2⟩).1.2.trans_lt hv)
  have atB : b∈J := ⟨le_rfl,bIn.2⟩
  refine ⟨b,⟨bp,bIn.2⟩,r,(unique b atB (by norm_num [C]) ((right b).trans eq)).symm,cont,near,?_,?_⟩
  · intro y hy
    have inJ : y∈J := ⟨hy.1.le,hy.2⟩
    have hrow := actual_quarter_height_row_strictMono ht (within inJ) d
    have v : s<V y := eq ▸ hm bIn (vmem (within inJ)) hy.1
    exact ⟨(hrow.lt_iff_lt (by norm_num : (0:ℝ)∈Icc 0 1) (root y inJ).1).mp
        (((left y).trans_lt (lower (within inJ))).trans_eq (root y inJ).2.symm),
      (hrow.lt_iff_lt (root y inJ).1 (by norm_num : (1:ℝ)∈Icc 0 1)).mp
        (((root y inJ).2.trans_lt v).trans_eq (right y).symm)⟩
  · intro y hy x hx
    constructor
    · intro hit
      have le := (actual_quarter_height_row_strictMono ht hy d).monotoneOn hx (by norm_num) hx.2
      change X (Z x y) 2=s at hit
      have by' : b≤y := (hm.le_iff_le bIn (vmem hy)).mp (eq.trans_le (hit.symm.trans_le (le.trans_eq (right y))))
      exact ⟨by',unique y ⟨by',hy.2⟩ hx hit⟩
    · rintro ⟨by',rfl⟩
      exact (root y ⟨by',hy.2⟩).2

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.positive_quarter_height_ray
