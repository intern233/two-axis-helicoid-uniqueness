import TwoAxisHelicoid.ActualQuarterHeightSlices
import TwoAxisHelicoid.ExplicitMarkedReflections

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

private theorem middle_limit_from_brackets {α : Type*} {l : Filter α} {r : α → ℝ} {a : ℝ}
    (ha : a∈Ioo (0:ℝ) 1) (low : ∀ b∈Ioo 0 a, ∀ᶠ s in l, b<r s)
    (high : ∀ b∈Ioo a 1, ∀ᶠ s in l, r s<b) : Tendsto r l (𝓝 a) := by
  apply tendsto_order.mpr
  constructor
  · intro x hx
    obtain ⟨b,bd,ba⟩ := exists_between (max_lt hx ha.1)
    exact (low b ⟨(le_max_right _ _).trans_lt bd,ba⟩).mono fun _ h => ((le_max_left _ _).trans_lt bd).trans h
  · intro x hx
    obtain ⟨b,ab,bd⟩ := exists_between (lt_min hx ha.2)
    exact (high b ⟨ab,bd.trans_le (min_le_right _ _)⟩).mono fun _ h => h.trans (bd.trans_le (min_le_left _ _))

/-- The normal derivative of the centered physical height on the
horizontal axis changes sign precisely at its saddle abscissa. -/
theorem centered_height_axis_normal_derivative {t a x : ℝ} (ht : 0<t) (hx : x∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht) :
    let W := (rhombicPeriodPair t ht).weierstrassP
    HasDerivAt (fun y : ℝ => X ((x:ℂ)+I*y) 2-X 1 2) ((W a).re-(W x).re) 0 := by
  let L := rhombicPeriodPair t ht
  have reg : (x:ℂ)∉L.lattice := real_not_mem_rhombic_lattice_of_pos ht hx.1 (hx.2.trans (by norm_num))
  have line : HasDerivAt (fun y : ℝ => (x:ℂ)+I*y) I 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp.const_mul I).const_add (x:ℂ))
  have step := (actual_coordinate_primitive_component ht d reg 2).comp_hasDerivAt_of_eq 0 line (by simp)
  convert step.sub_const (X 1 2) using 1
  · rfl
  · change _=(I*(I*(1:ℂ)*(L.weierstrassP x-L.weierstrassP a))).re
    simp [L,Complex.mul_re,Complex.mul_im]

private theorem sign_right_of_zero {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (h : f 0=0) (p : 0<d) : ∀ᶠ y in 𝓝[>] (0:ℝ), 0<f y := by
  have hq : ∀ᶠ y in 𝓝[>] (0:ℝ), 0<y⁻¹*f y := by
    simpa only [zero_add,h,sub_zero,smul_eq_mul] using hf.tendsto_slope_zero_right.eventually (Ioi_mem_nhds p)
  filter_upwards [self_mem_nhdsWithin,hq] with y hy hxy
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hy)).mp hxy

/-- The central horizontal section of the ordinary parameter rectangle
is a single continuous arc. Its endpoints are the two actual saddles,
it contains the half-period, and the half-turn reverses its parameter. -/
theorem actual_central_height_arc {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) :
    ∃ r : ℝ → ℝ, (∀ y∈Ioo 0 t, r y∈Ioo (0:ℝ) 1 ∧
      ∀ x∈Ioo (0:ℝ) 1, X ((x:ℂ)+I*y) 2=X 1 2 ↔ x=r y) ∧
      ContinuousOn r (Ioo 0 t) ∧ Tendsto r (𝓝[>] 0) (𝓝 a) ∧
      Tendsto r (𝓝[<] t) (𝓝 (1-a)) ∧ (∀ y∈Ioo 0 t, r (t-y)=1-r y) ∧ r (t/2)=1/2 := by
  classical
  let F := fun (x y : ℝ) => X ((x:ℂ)+I*y) 2-X 1 2
  let r := fun y : ℝ => if h : y∈Ioo 0 t then (actual_quarter_central_plane_unique ht ha h d per).choose else 0
  have spec (y : ℝ) (hy : y∈Ioo 0 t) : r y∈Ioo (0:ℝ) 1 ∧ ∀ x∈Ioo (0:ℝ) 1, X ((x:ℂ)+I*y) 2=X 1 2 ↔ x=r y := by
    simp only [r,dite_eq_left hy]
    obtain ⟨h,u⟩ := (actual_quarter_central_plane_unique ht ha hy d per).choose_spec
    exact ⟨h.1,fun x hx => ⟨fun e => u x ⟨hx,e⟩,fun e => e.symm ▸ h.2⟩⟩
  have zero (y : ℝ) (hy : y∈Ioo 0 t) : F (r y) y=0 := sub_eq_zero.mpr (((spec y hy).2 _ (spec y hy).1).mpr rfl)
  have mono (y : ℝ) (hy : y∈Ioo 0 t) : StrictMonoOn (fun x => F x y) (Ioo (0:ℝ) 1) :=
    fun _ hx _ hu hxu => sub_lt_sub_right ((actual_quarter_height_row_strictMono ht hy d) (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hu) hxu) _
  have lower (b : ℝ) (hb : b∈Ioo (0:ℝ) 1) (y : ℝ) (hy : y∈Ioo 0 t) (h : F b y<0) : b<r y := by
    exact (mono y hy).lt_iff_lt hb (spec y hy).1 |>.mp (by rwa [zero])
  have upper (b : ℝ) (hb : b∈Ioo (0:ℝ) 1) (y : ℝ) (hy : y∈Ioo 0 t) (h : 0<F b y) : r y<b := by
    exact (mono y hy).lt_iff_lt (spec y hy).1 hb |>.mp (by rwa [zero])
  have cy (x y : ℝ) (hy : y∈Ioo 0 t) : ContinuousAt (F x) y := by
    have off := rhombic_horizontal_strip_not_mem (z:=(x:ℂ)+I*y) ht (by change _∈Ioo 0 t; simpa using hy)
    exact ((actual_coordinate_primitive_component ht d off 2).continuousAt.comp
      (f:=fun s : ℝ => (x:ℂ)+I*s) (by fun_prop)).sub continuousAt_const
  have cr (s : ℝ) (hs : s∈Ioo 0 t) : ContinuousAt r s := by
    apply middle_limit_from_brackets (spec s hs).1
    · intro b hb
      have unit : b∈Ioo (0:ℝ) 1 := ⟨hb.1,hb.2.trans (spec s hs).1.2⟩
      have neg := mono s hs unit (spec s hs).1 hb.2
      change F b s<F (r s) s at neg
      rw [zero s hs] at neg
      filter_upwards [isOpen_Ioo.mem_nhds hs,(cy b s hs).eventually (Iio_mem_nhds neg)] with y hy h using lower b unit y hy h
    · intro b hb
      have unit : b∈Ioo (0:ℝ) 1 := ⟨(spec s hs).1.1.trans hb.1,hb.2⟩
      have pos := mono s hs (spec s hs).1 unit hb.1
      change F (r s) s<F b s at pos
      rw [zero s hs] at pos
      filter_upwards [isOpen_Ioo.mem_nhds hs,(cy b s hs).eventually (Ioi_mem_nhds pos)] with y hy h using upper b unit y hy h
  have base (b : ℝ) (hb : b∈Ioo (0:ℝ) 1) : F b 0=0 := by
    simp only [F,ofReal_zero,mul_zero,add_zero,sub_eq_zero]
    exact (actual_primitive_horizontal_line ht d ⟨hb.1,hb.2.trans (by norm_num)⟩).2
  have left : Tendsto r (𝓝[>] 0) (𝓝 a) := by
    apply middle_limit_from_brackets ha
    · intro b hb
      have unit : b∈Ioo (0:ℝ) 1 := ⟨hb.1,hb.2.trans ha.2⟩
      have order := rhombic_weierstrassP_strictAnti_of_pos ht ht unit ha hb.2
      have neg := sign_right_of_zero (centered_height_axis_normal_derivative ht unit d (a:=a)).neg
        (by change -F b 0=0; rw [base b unit,neg_zero]) (by dsimp only at order ⊢; linarith)
      filter_upwards [Ioo_mem_nhdsGT ht,neg] with y hy h using lower b unit y hy (neg_pos.mp h)
    · intro b hb
      have unit : b∈Ioo (0:ℝ) 1 := ⟨ha.1.trans hb.1,hb.2⟩
      have order := rhombic_weierstrassP_strictAnti_of_pos ht ht ha unit hb.1
      have pos := sign_right_of_zero (centered_height_axis_normal_derivative ht unit d (a:=a)) (base b unit) (sub_pos.mpr order)
      filter_upwards [Ioo_mem_nhdsGT ht,pos] with y hy h using upper b unit y hy h
  have sym (y : ℝ) (hy : y∈Ioo 0 t) : r (t-y)=1-r y := by
    have other : t-y∈Ioo 0 t := ⟨sub_pos.mpr hy.2,by linarith [hy.1]⟩
    have u := (spec y hy).1
    have rc : 1-r y∈Ioo (0:ℝ) 1 := ⟨sub_pos.mpr u.2,by linarith [u.1]⟩
    apply Eq.symm
    apply ((spec _ other).2 _ rc).mp
    let z := (r y:ℂ)+I*y
    have off : z∉(rhombicPeriodPair t ht).lattice := rhombic_horizontal_strip_not_mem ht
      (by change z.im∈Ioo 0 t; simpa [z] using hy)
    have n := congrFun ((explicit_centered_primitive_reflections ht d per z off).1) 2
    change X (-z) 2-X 1 2= -F (r y) y at n
    rw [zero y hy,neg_zero] at n
    have e := congrFun (per (-z) (1+I*t) (rhombicPeriodPair t ht).ω₂_mem_lattice) 2
    have alg : ((1-r y:ℝ):ℂ)+I*(t-y:ℝ)= -z+(1+I*t) := by dsimp [z]; push_cast; ring
    rw [alg,e]
    exact sub_eq_zero.mp n
  have right : Tendsto r (𝓝[<] t) (𝓝 (1-a)) := by
    have line : Tendsto (fun y : ℝ => t-y) (𝓝[<] t) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using! ((continuous_const.sub continuous_id : Continuous (fun y : ℝ => t-y)).continuousAt.tendsto (x:=t)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy using (show 0<t-y from sub_pos.mpr (show y<t from hy))
    apply (tendsto_const_nhds.sub (left.comp line)).congr'
    filter_upwards [Ioo_mem_nhdsLT ht] with y hy
    change 1-r (t-y)=r y
    rw [sym y hy]
    ring
  have half := sym (t/2) ⟨by linarith,by linarith⟩
  rw [show t-t/2=t/2 by ring] at half
  exact ⟨r,spec,fun y hy => (cr y hy).continuousWithinAt,left,right,sym,by linarith⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_central_height_arc
