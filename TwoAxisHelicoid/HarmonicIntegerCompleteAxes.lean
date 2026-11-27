import TwoAxisHelicoid.AxisHelicoidCalibration
import TwoAxisHelicoid.IntegerEndProperEmbedding

namespace TwoAxisHelicoid
open Complex Set Filter Bornology
open scoped Topology ComplexConjugate

private theorem surjOn_of_antipodal_escape {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo 0 r)) (hneg : ∀ x ∈ Ioo 0 r, f (r-x) = -f x)
    (hescape : Tendsto (fun x => |f x|) (𝓝[>] 0) atTop) : SurjOn f (Ioo 0 r) univ := by
  intro v _
  have hi : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 r := Ioo_mem_nhdsGT hr
  obtain ⟨x,hx,hv⟩ := (hi.and ((tendsto_atTop.mp hescape) (|v|+1))).exists
  have hx' : r-x ∈ Ioo 0 r := ⟨sub_pos.mpr hx.2,sub_lt_self _ hx.1⟩
  have hn := hneg x hx
  rcases le_total 0 (f x) with hs | hs
  · rw [abs_of_nonneg hs] at hv
    exact isPreconnected_Ioo.intermediate_value₂ hx' hx hf (continuousOn_const (c := v))
      (by rw [hn]; linarith [neg_abs_le v]) (by linarith [le_abs_self v])
  · rw [abs_of_nonpos hs] at hv
    exact isPreconnected_Ioo.intermediate_value₂ hx hx' hf (continuousOn_const (c := v))
      (by linarith [neg_abs_le v]) (by rw [hn]; linarith [le_abs_self v])

private theorem escaping_line_coordinate {X : ℂ → Fin 3 → ℝ}
    (he : Tendsto X (𝓝[≠] (0 : ℂ)) (cobounded (Fin 3 → ℝ))) {r : ℝ} (hr : 0 < r)
    (d : ℂ) (hd : d ≠ 0) (j : Fin 3)
    (hline : ∀ x ∈ Ioo 0 r, ∀ k ≠ j, X (d*x) k = 0) :
    Tendsto (fun x : ℝ => |X (d*x) j|) (𝓝[>] 0) atTop := by
  have hpath : Tendsto (fun x : ℝ => d*x) (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh : Continuous (fun x : ℝ => d*x) := by fun_prop
      simpa only [Complex.ofReal_zero,mul_zero] using (hh.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_ne_zero hd (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))
  apply (tendsto_norm_atTop_iff_cobounded.mpr (he.comp hpath)).congr'
  filter_upwards [Ioo_mem_nhdsGT hr] with x hx
  change ‖X (d*x)‖ = |X (d*x) j|
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro k
    by_cases h : k = j
    · subst k
      exact le_of_eq (Real.norm_eq_abs _)
    · rw [hline x hx k h,norm_zero]
      exact abs_nonneg _
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm (X (d*x)) j

/-- Finite symmetry and proper escape imply that both straight axes
are covered in full for every integer branch of the actual immersion. -/
theorem harmonic_escaping_immersion_contains_axes {t : ℝ} (ht : 0 < t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hescape : Tendsto X (𝓝[≠] (0 : ℂ)) (cobounded (Fin 3 → ℝ))) :
    (∀ r : ℝ, ∃ z ∉ (rhombicPeriodPair t ht).lattice, X z = ![r,0,0]) ∧
    (∀ r : ℝ, ∃ z ∉ (rhombicPeriodPair t ht).lattice, X z = ![0,0,r]) := by
  let L := rhombicPeriodPair t ht
  have hreal (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 2) : (x : ℂ) ∉ L.lattice :=
    real_not_mem_rhombic_lattice_of_pos ht hx.1 hx.2
  have him (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (2*t)) : I*(x : ℂ) ∉ L.lattice := by
    simpa only [Complex.ofReal_zero,zero_add] using rhombic_vertical_strip_not_mem ht
      (by norm_num : (0 : ℝ) ∈ Ioo (-1) 1) hx
  have hr (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 2) : X x 1 = 0 ∧ X x 2 = 0 := by
    have hc := hX.conjugation x (hreal x hx)
    rw [Complex.conj_ofReal] at hc
    have h1 := congrFun hc 1
    have h2 := congrFun hc 2
    change X x 1 = -X x 1 at h1
    change X x 2 = -X x 2 at h2
    constructor <;> linarith
  have hv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (2*t)) : X (I*x) 0 = 0 ∧ X (I*x) 1 = 0 :=
    hX.vertical_axis_zero (him x hx) (by simp [Complex.mul_re])
  constructor
  · intro v
    have hsur : SurjOn (fun x : ℝ => X x 0) (Ioo (0 : ℝ) 2) univ := by
      apply surjOn_of_antipodal_escape (by norm_num)
      · intro x hx
        exact ((continuous_apply 0).continuousAt.comp ((hX.differentiable _ (hreal x hx)).continuousAt.comp
          Complex.continuous_ofReal.continuousAt)).continuousWithinAt
      · intro x hx
        have hn : -(x : ℂ) ∉ L.lattice := by simpa using hreal x hx
        have he := hX.periodic _ hn 2 (rhombicPeriodPair t ht).ω₁_mem_lattice
        rw [hX.neg _ (hreal x hx)] at he
        rw [show ((2-x : ℝ) : ℂ) = -(x : ℂ)+2 by push_cast; ring]
        exact congrFun he 0
      · have he := escaping_line_coordinate hescape (by norm_num : (0 : ℝ)<2) 1 one_ne_zero 0 (by
          intro x hx j hj
          simp only [one_mul]
          fin_cases j
          · exact (hj rfl).elim
          · exact (hr x hx).1
          · exact (hr x hx).2)
        simpa only [one_mul] using he
    obtain ⟨x,hx,he⟩ := hsur (mem_univ v)
    refine ⟨x,hreal x hx,?_⟩
    funext j
    fin_cases j
    · exact he
    · exact (hr x hx).1
    · exact (hr x hx).2
  · intro v
    have hsur : SurjOn (fun x : ℝ => X (I*x) 2) (Ioo (0 : ℝ) (2*t)) univ := by
      apply surjOn_of_antipodal_escape (by linarith)
      · intro x hx
        exact ((continuous_apply 2).continuousAt.comp ((hX.differentiable _ (him x hx)).continuousAt.comp (f := fun s : ℝ => I*s)
          (by fun_prop : ContinuousAt (fun s : ℝ => I*s) x))).continuousWithinAt
      · intro x hx
        have hω : 2*I*t ∈ L.lattice := by
          apply (rhombic_mem_lattice_iff ht _).mpr
          refine ⟨-1,2,?_,?_⟩ <;> simp [Complex.mul_re,Complex.mul_im]
        have hn : -(I*(x : ℂ)) ∉ L.lattice := by simpa using him x hx
        have he := hX.periodic _ hn _ hω
        rw [hX.neg _ (him x hx)] at he
        rw [show I*((2*t-x : ℝ) : ℂ) = -(I*(x : ℂ))+2*I*t by push_cast; ring]
        exact congrFun he 2
      · exact escaping_line_coordinate hescape (r := 2*t) (by linarith) I I_ne_zero 2 (by
          intro x hx j hj
          fin_cases j
          · exact (hv x hx).1
          · exact (hv x hx).2
          · exact (hj rfl).elim)
    obtain ⟨x,hx,he⟩ := hsur (mem_univ v)
    refine ⟨I*x,him x hx,?_⟩
    funext j
    fin_cases j
    · exact (hv x hx).1
    · exact (hv x hx).2
    · exact he

theorem harmonic_integer_data_contains_complete_axes {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 = coordinateData t a c ht z 2)
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    (∀ r : ℝ, ∃ z ∉ (rhombicPeriodPair t ht).lattice, X z = ![r,0,0]) ∧
    (∀ r : ℝ, ∃ z ∉ (rhombicPeriodPair t ht).lattice, X z = ![0,0,r]) :=
  harmonic_escaping_immersion_contains_axes ht hX (integer_primitive_end_escape_and_embedding m ht ha hc
    (harmonic_integer_gauss_data_has_coordinate_differential ht ha hc m hX hh hg)).1

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.harmonic_integer_data_contains_complete_axes
