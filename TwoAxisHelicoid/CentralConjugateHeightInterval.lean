import TwoAxisHelicoid.CentralHeightArc
import TwoAxisHelicoid.UnivalentQuarterHeightCoordinate
import TwoAxisHelicoid.HeightEndAxisCenter

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

/-- On a common physical height in the open rectangle, the parameter
height strictly orders the conjugate heights. -/
theorem actual_equal_height_im_strict {t a : ℝ} (ht : 0<t) {z w : ℂ}
    (hz : z∈complexOpenRect 0 1 0 t) (hw : w∈complexOpenRect 0 1 0 t)
    (order : z.im<w.im) (eq : (actualComplexHeight t a 1 ht z).re=(actualComplexHeight t a 1 ht w).re) :
    (actualComplexHeight t a 1 ht z).im<(actualComplexHeight t a 1 ht w).im := by
  let f := actualComplexHeight t a 1 ht
  have ne : w≠z := fun e => order.ne (congrArg im e.symm)
  have sec := (actual_complex_height_univalent_quarter (a:=a) ht).2.1 z hz w hw ne
  change 0<((f w-f z)/(w-z)).re at sec
  change (f z).re=(f w).re at eq
  rw [div_eq_mul_inv,Complex.mul_re,Complex.sub_re,← eq,sub_self,zero_mul,zero_sub,
    Complex.sub_im,Complex.inv_im,Complex.sub_im] at sec
  have neg : -(w.im-z.im)/normSq (w-z)<0 := div_neg_of_neg_of_pos
    (neg_lt_zero.mpr (sub_pos.mpr order)) (normSq_pos.mpr (sub_ne_zero.mpr ne))
  exact sub_pos.mp (pos_of_mul_neg_left (neg_pos.mp sec) neg.le)

/-- The conjugate height gives a strictly increasing coordinate along
the entire central arc. Its image is exactly the open interval between
the conjugate heights of the two lifted saddles. -/
theorem actual_central_conjugate_height_interval {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z p, p∈(rhombicPeriodPair t ht).lattice → X (z+p)=X z) :
    let H := actualComplexHeight t a 1 ht
    let lo := (H a).im
    let hi := (H (((1-a:ℝ):ℂ)+I*t)).im
    ∃ r : ℝ → ℝ, (∀ y∈Ioo 0 t, r y∈Ioo (0:ℝ) 1 ∧ X ((r y:ℂ)+I*y) 2=X 1 2) ∧
      let f := fun y : ℝ => (H ((r y:ℂ)+I*y)).im
      StrictMonoOn f (Ioo 0 t) ∧ ContinuousOn f (Ioo 0 t) ∧
      Tendsto f (𝓝[>] 0) (𝓝 lo) ∧ Tendsto f (𝓝[<] t) (𝓝 hi) ∧
      lo<hi ∧ f '' Ioo 0 t=Ioo lo hi := by
  intro H lo hi
  obtain ⟨r,spec,cr,pl,pr,_⟩ := actual_central_height_arc ht ha d per
  let z := fun y : ℝ => (r y:ℂ)+I*y
  let f := fun y => (H (z y)).im
  have arc (y : ℝ) (hy : y∈Ioo 0 t) := ((spec y hy).2 _ (spec y hy).1).mpr rfl
  have iz (y : ℝ) : (z y).im=y := by simp [z]
  have inside (y : ℝ) (hy : y∈Ioo 0 t) : z y∈complexOpenRect 0 1 0 t := by
    exact ⟨by simpa [z] using (spec y hy).1,by simpa [iz] using hy⟩
  have real0 (y : ℝ) (hy : y∈Ioo 0 t) : (H (z y)).re=0 := by
    have h := actual_complex_height_centered_primitive ht d (rhombic_horizontal_strip_not_mem ht (inside y hy).2)
    rw [show X (z y) 2=X 1 2 from arc y hy,sub_self] at h
    exact h.symm
  have mono : StrictMonoOn f (Ioo 0 t) := by
    intro u hu v hv uv
    exact actual_equal_height_im_strict ht (inside u hu) (inside v hv)
      (by simpa only [iz] using uv) ((real0 u hu).trans (real0 v hv).symm)
  have c : ContinuousOn f (Ioo 0 t) := by
    intro y hy
    have cz : ContinuousWithinAt z (Ioo 0 t) y := (continuous_ofReal.continuousAt.comp_continuousWithinAt
      (cr y hy)).add (continuous_const.mul continuous_ofReal).continuousAt.continuousWithinAt
    exact continuous_im.continuousAt.comp_continuousWithinAt
      ((actualComplexHeight_hasDerivAt (a:=a) (c:=1) ht (rhombic_horizontal_strip_not_mem ht (inside y hy).2)).continuousAt.comp_continuousWithinAt cz)
  have leftZ : Tendsto z (𝓝[>] 0) (𝓝 (a:ℂ)) := by
    simpa [z] using (continuous_ofReal.continuousAt.tendsto.comp pl).add
      (((continuous_const.mul continuous_ofReal : Continuous (fun y : ℝ => I*(y:ℂ))).continuousAt.tendsto (x:=0)).mono_left nhdsWithin_le_nhds)
  have rightZ : Tendsto z (𝓝[<] t) (𝓝 (((1-a:ℝ):ℂ)+I*t)) :=
    (continuous_ofReal.continuousAt.tendsto.comp pr).add
      (((continuous_const.mul continuous_ofReal : Continuous (fun y : ℝ => I*(y:ℂ))).continuousAt.tendsto (x:=t)).mono_left nhdsWithin_le_nhds)
  have areg : (a:ℂ)∉(rhombicPeriodPair t ht).lattice := real_not_mem_rhombic_lattice_of_pos ht ha.1 (ha.2.trans (by norm_num))
  have breg : ((1-a:ℝ):ℂ)+I*t∉(rhombicPeriodPair t ht).lattice := by
    intro h
    have k := (rhombicPeriodPair t ht).lattice.sub_mem (rhombicPeriodPair t ht).ω₂_mem_lattice h
    apply areg
    convert k using 1
    change (a:ℂ)=1+I*t-(_+_)
    push_cast
    ring
  have left : Tendsto f (𝓝[>] 0) (𝓝 lo) := continuous_im.continuousAt.tendsto.comp
    ((actualComplexHeight_hasDerivAt (a:=a) (c:=1) ht areg).continuousAt.tendsto.comp leftZ)
  have right : Tendsto f (𝓝[<] t) (𝓝 hi) := continuous_im.continuousAt.tendsto.comp
    ((actualComplexHeight_hasDerivAt (a:=a) (c:=1) ht breg).continuousAt.tendsto.comp rightZ)
  have bounds (y : ℝ) (hy : y∈Ioo 0 t) : f y∈Ioo lo hi := by
    obtain ⟨u,up,uy⟩ := exists_between hy.1
    obtain ⟨v,yv,vt⟩ := exists_between hy.2
    have hu : u∈Ioo 0 t := ⟨up,uy.trans hy.2⟩
    have hv : v∈Ioo 0 t := ⟨hy.1.trans yv,vt⟩
    constructor
    · apply lt_of_le_of_lt _ (mono hu hy uy)
      apply le_of_tendsto left
      filter_upwards [Ioo_mem_nhdsGT up] with x hx using (mono ⟨hx.1,hx.2.trans hu.2⟩ hu hx.2).le
    · apply lt_of_lt_of_le (mono hy hv yv)
      apply ge_of_tendsto right
      filter_upwards [Ioo_mem_nhdsLT vt] with x hx using (mono hv ⟨hv.1.trans hx.1,hx.2⟩ hx.1).le
  obtain ⟨y,hy⟩ := Set.nonempty_Ioo.mpr ht
  refine ⟨r,fun u hu => ⟨(spec u hu).1,arc u hu⟩,mono,c,left,right,(bounds y hy).1.trans (bounds y hy).2,?_⟩
  apply Subset.antisymm (image_subset_iff.mpr (by intro u hu; exact bounds u hu))
  intro b hb
  have nl : ∀ᶠ u in 𝓝[>] (0:ℝ), u∈Ioo 0 t := Ioo_mem_nhdsGT ht
  have nr : ∀ᶠ u in 𝓝[<] t, u∈Ioo 0 t := Ioo_mem_nhdsLT ht
  obtain ⟨u,hu,ub⟩ := (nl.and (left.eventually (Iio_mem_nhds hb.1))).exists
  obtain ⟨v,hv,bv⟩ := (nr.and (right.eventually (Ioi_mem_nhds hb.2))).exists
  exact (isPreconnected_Ioo.image f c).ordConnected.out (mem_image_of_mem f hu)
    (mem_image_of_mem f hv) ⟨ub.le,bv.le⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_central_conjugate_height_interval
