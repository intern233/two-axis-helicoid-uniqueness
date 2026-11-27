import TwoAxisHelicoid.PlanePolygonPrimitive
import TwoAxisHelicoid.PrimitiveDoublePoleExpansion
import TwoAxisHelicoid.TorusDoublePoleResidue
import TwoAxisHelicoid.RealPrimitivePeriods

namespace TwoAxisHelicoid
open Complex Set Filter
open scoped Topology

theorem PlanePolygon.real_integral_eq_height_difference {Ω : Set ℂ}
    {H : ℂ → ℝ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    (hH : ∀ z ∈ Ω, HasFDerivAt H (realCoefficientDerivative (f z)) z)
    {x y : ℂ} (p : PlanePolygon Ω x y) : (p.integral f).re = H y-H x := by
  induction p with
  | refl => simp [PlanePolygon.integral]
  | trans p q hp hq => simp only [PlanePolygon.integral,add_re,hp,hq]; ring
  | step a b h =>
    have he := real_primitive_path_integral_eq_sub (path := AffineMap.lineMap (k := ℝ) a b)
      (F := H) (f := f) (a := 0) (b := 1) (fun _ _ => AffineMap.hasDerivAt_lineMap)
      (fun s hs => hH _ (h s (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hs)))
      ((show ContinuousOn (fun s : ℝ => f (AffineMap.lineMap (k := ℝ) a b s)) (Icc 0 1)
        from fun s hs => ((hf _ (h s hs)).continuousAt.comp
          AffineMap.lineMap_continuous.continuousAt).continuousWithinAt).intervalIntegrable_of_Icc (by norm_num))
    simpa only [PlanePolygon.integral,AffineMap.lineMap_apply_one,AffineMap.lineMap_apply_zero] using he

/-- A height differential with its sole pole of order two on any marked torus
has a nonzero imaginary period. All periods here are integrals of the given
coefficient along actual polygon edges avoiding the lattice. -/
theorem torus_height_exists_nonzero_imaginary_period (L : PeriodPair) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (L.lattice : Set ℂ)ᶜ)
    (hp : ∀ z ω, ω ∈ L.lattice → f (z+ω) = f z)
    (hm : MeromorphicAt f 0) (ho : meromorphicOrderAt f 0 = (-2 : ℤ))
    (hreal : ∀ {x y : ℂ} (p : PlanePolygon (L.lattice : Set ℂ)ᶜ x y),
      y-x ∈ L.lattice → (p.integral f).re = 0) :
    ∃ (x y : ℂ) (p : PlanePolygon (L.lattice : Set ℂ)ᶜ x y),
      y-x ∈ L.lattice ∧ (p.integral f).im ≠ 0 := by
  by_contra hn
  have hzero {x y : ℂ} (p : PlanePolygon (L.lattice : Set ℂ)ᶜ x y)
      (hw : y-x ∈ L.lattice) : p.integral f = 0 := by
    apply Complex.ext (hreal p hw)
    by_contra hne
    exact hn ⟨x,y,p,hw,hne⟩
  obtain ⟨F,hFp,hFd⟩ := periodic_primitive_of_zero_polygon_periods L hf hzero
  obtain ⟨A,g,hA,hg,hgerm⟩ := torus_double_pole_has_zero_residue L hf hp hm ho
  have hFa : AnalyticOnNhd ℂ F (L.lattice : Set ℂ)ᶜ :=
    (show DifferentiableOn ℂ F (L.lattice : Set ℂ)ᶜ from
      fun z hz => (hFd z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
        L.isClosed_lattice.isOpen_compl
  obtain ⟨G,hG,hFloc⟩ := primitive_of_double_pole_expansion hg (F := F) (A := A) (by
    filter_upwards [hgerm,L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ)] with z hz hL hnz
    rw [← hz hnz]
    exact hFd _ (fun hl => hL ⟨hl,hnz⟩))
  exact neg_ne_zero.mpr hA (elliptic_single_simple_pole_coefficient_zero L hFa hFp hG hFloc)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_height_exists_nonzero_imaginary_period
