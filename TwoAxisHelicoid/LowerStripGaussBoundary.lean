import TwoAxisHelicoid.QuarterGaussMirror
import TwoAxisHelicoid.SaddleGaussOrientation
import Mathlib.Analysis.Complex.Harmonic.Analytic

namespace TwoAxisHelicoid
open Complex Set Filter Metric InnerProductSpace
open scoped Topology ComplexConjugate

/-- The real Gauss component has the required one-sided limit along
the doubled real boundary. At the reflected saddle the Gauss map has
a pole, whose sign follows from the simple zero on the other side. -/
theorem lower_strip_real_gauss_boundary {t a : ℝ} (ht : 0<t) (lower : 43/50≤t) (ha : a∈Ioo (0:ℝ) 1)
    {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z) :
    ∀ x∈Icc (1/2:ℝ) (3/2), ∀ e : ℝ, 0<e →
      ∀ᶠ z in 𝓝[{z : ℂ | z.im∈Ioo (0:ℝ) t}] (x:ℂ), -e≤ -(thetaGauss t a 1 z).re := by
  intro x hx e ep
  let G := thetaGauss t a 1
  let V := {z : ℂ | z.im∈Ioo (0:ℝ) t}
  let L := rhombicPeriodPair t ht
  by_cases pole : x=2-a
  · obtain ⟨δ,dp,upper⟩ := saddle_upper_gauss_real_negative lower ha
    have near : ∀ᶠ z in 𝓝 (x:ℂ), |2-z.re-a|<δ := by
      have atx : |2-(x:ℂ).re-a|<δ := by simp [pole,dp]
      have c : ContinuousAt (fun z : ℂ => |2-z.re-a|) (x:ℂ) := by fun_prop
      exact c.eventually (Iio_mem_nhds atx)
    have nearY : ∀ᶠ z in 𝓝 (x:ℂ), z.im<δ := continuous_im.continuousAt.eventually (Iio_mem_nhds (by simpa using dp))
    have dom : ∀ᶠ z in 𝓝[V] (x:ℂ), z∈V := self_mem_nhdsWithin
    filter_upwards [near.filter_mono nhdsWithin_le_nhds,nearY.filter_mono nhdsWithin_le_nhds,dom] with z xx yy zz
    have pos := upper (2-z.re) z.im xx ⟨zz.1,yy⟩
    have ident : ((2-z.re:ℝ):ℂ)+I*z.im=2-conj z := by apply Complex.ext <;> simp
    rw [ident] at pos
    have v := (quarter_gauss_vertical_mirror ht d per zz).2.mp pos
    linarith
  · have cont : ContinuousAt G (x:ℂ) := by
      by_cases saddle : x=a
      · rw [saddle]; exact (saddle_gauss_first_jet lower ha).1.continuousAt
      have off := real_not_mem_rhombic_lattice_of_pos ht (show 0<x by linarith [hx.1]) (show x<2 by linarith [hx.2])
      have m : (x:ℂ)-a∉L.lattice := by
        rcases lt_or_gt_of_ne saddle with lt|lt
        · have n := real_not_mem_rhombic_lattice_of_pos ht (sub_pos.mpr lt) (show a-x<2 by linarith [hx.1,ha.2])
          intro k
          apply n
          rw [ofReal_sub,← neg_sub]
          exact L.lattice.neg_mem k
        · rw [← ofReal_sub]
          exact real_not_mem_rhombic_lattice_of_pos ht (sub_pos.mpr lt) (by linarith [hx.2,ha.1])
      have p : (x:ℂ)+a∉L.lattice := by
        rcases lt_or_gt_of_ne (show x+a≠2 by intro eq; exact pole (by linarith)) with lt|lt
        · rw [← ofReal_add]
          exact real_not_mem_rhombic_lattice_of_pos ht (by linarith [ha.1,hx.1]) lt
        · intro member
          have k := L.lattice.sub_mem member L.ω₁_mem_lattice
          have n := real_not_mem_rhombic_lattice_of_pos ht (sub_pos.mpr lt) (show x+a-2<2 by linarith [hx.2,ha.2])
          change (x:ℂ)+a-2∈L.lattice at k
          exact n (by simpa only [ofReal_sub,ofReal_add,ofReal_ofNat] using k)
      exact (thetaGauss_hasDerivAt ht a 1 off m p).continuousAt
    have zero : (G (x:ℂ)).re=0 := by
      have s := congrArg re (thetaGauss_conj t a 1 (x:ℂ))
      simp only [conj_ofReal,neg_re,conj_re] at s
      change (thetaGauss t a 1 (x:ℂ)).re=0
      linarith
    have order := (continuous_re.continuousAt.comp cont).eventually (Iio_mem_nhds (zero.trans_lt ep))
    exact (order.filter_mono nhdsWithin_le_nhds).mono fun z h => neg_le_neg h.le

theorem gauss_real_harmonic_on_upper_strip {t a : ℝ} (ht : 0<t) {z : ℂ} (hy : z.im∈Ioo (0:ℝ) t) :
    HarmonicAt (fun w => -(thetaGauss t a 1 w).re) z := by
  have an : AnalyticAt ℂ (thetaGauss t a 1) z := analyticAt_iff_eventually_differentiableAt.mpr (by
    filter_upwards [continuous_im.continuousAt.eventually (isOpen_Ioo.mem_nhds hy)] with w hw
    apply (thetaGauss_hasDerivAt ht a 1 (rhombic_horizontal_strip_not_mem ht hw) _ _).differentiableAt
    · exact rhombic_horizontal_strip_not_mem ht (by change (w-a).im∈Ioo 0 t; simpa using hw)
    · exact rhombic_horizontal_strip_not_mem ht (by change (w+a).im∈Ioo 0 t; simpa using hw))
  exact an.harmonicAt_re.neg

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.lower_strip_real_gauss_boundary
#print axioms TwoAxisHelicoid.gauss_real_harmonic_on_upper_strip
