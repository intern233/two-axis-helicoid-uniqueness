import TwoAxisHelicoid.ChartCutoffStokes
import TwoAxisHelicoid.LocalizedComplexChartIntegrals

namespace TwoAxisHelicoid
open Complex Set MeasureTheory Filter Topology Function
open scoped Topology ContDiff

/-- A finite sum of differentiable one-form coefficients can be
differentiated coefficient by coefficient in an oriented complex chart. -/
theorem complex_form_exterior_finset {ι : Type*} [Fintype ι] (a : ι → ℂ → ℂ) {z : ℂ}
    (reg : ∀ i, DifferentiableAt ℝ (a i) z) :
    complexFormExteriorCoefficient (fun w => ∑ i, a i w) z=∑ i, complexFormExteriorCoefficient (a i) z := by
  classical
  unfold complexFormExteriorCoefficient
  rw [fderiv_fun_sum (fun i _ => reg i)]
  simp only [sum_apply,Finset.mul_sum,Finset.sum_sub_distrib]

/-- Stokes on a finite coordinate cover. The coefficient of a complex
one-form may be an arbitrary real C¹ function in each chart. Its
holomorphic transition law is the only compatibility imposed. -/
theorem finite_chart_partition_stokes {M ι : Type*} [TopologicalSpace M] [Fintype ι]
    (e : ι → OpenPartialHomeomorph M ℂ) (ρ : ι → M → ℝ) (a : ι → ℂ → ℂ)
    (unity : ∀ x, ∑ i, ρ i x=1) (cρ : ∀ i, Continuous (ρ i))
    (compact : ∀ i, IsCompact (tsupport (ρ i))) (inside : ∀ i, tsupport (ρ i)⊆(e i).source)
    (cut : ∀ i j z, z∈(e i).target → ContDiffAt ℝ 1 (fun w => (ρ j ((e i).symm w):ℂ)) z)
    (reg : ∀ i z, z∈(e i).target → ContDiffAt ℝ 1 (a i) z)
    (hol : ∀ i j z, z∈((e i).symm.trans (e j)).source → AnalyticAt ℂ ((e i).symm.trans (e j)) z)
    (coeff : ∀ i j z, z∈((e i).symm.trans (e j)).source →
      a i z=a j (((e i).symm.trans (e j)) z)*deriv ((e i).symm.trans (e j)) z) :
    (∑ i, ∫ z in (e i).target, ρ i ((e i).symm z) • complexFormExteriorCoefficient (a i) z)=0 := by
  classical
  let B := fun i j w => (ρ j ((e i).symm w):ℂ)*a i w
  let E := fun i j z => complexFormExteriorCoefficient (B i j) z
  let W := fun i j k z => ρ k ((e i).symm z) • E i j z
  have smooth (i j z) (hz : z∈(e i).target) : ContDiffAt ℝ 1 (B i j) z :=
    (cut i j z hz).mul (reg i z hz)
  have sumA (i : ι) : (fun w => ∑ j, B i j w)=a i := by
    funext w
    simp only [B,← Finset.sum_mul,← Complex.ofReal_sum,unity,Complex.ofReal_one,one_mul]
  have split (i z) (hz : z∈(e i).target) : complexFormExteriorCoefficient (a i) z=∑ j, E i j z := by
    exact (congrArg (fun h => complexFormExteriorCoefficient h z) (sumA i).symm).trans
      (complex_form_exterior_finset _ (fun j => (smooth i j z hz).differentiableAt one_ne_zero))
  have same (i j : ι) : (∫ z in (e i).target, W i j i z)=∫ z in (e j).target, W j j i z :=
    localized_form_chart_integrals (e i) (e j) (a i) (a j) (ρ i) (ρ j) (inside i) (inside j)
      (hol i j) (coeff i j) (fun z hz => (reg j z hz).differentiableAt one_ne_zero)
      (fun z hz => (cut j j z hz).differentiableAt one_ne_zero)
  have intLeft (i j : ι) : IntegrableOn (W i j i) (e i).target :=
    chart_weighted_density_integrable _ (cρ i) (compact i) (inside i)
      (complexFormExteriorCoefficient_continuousOn (smooth i j))
  have intRight (j i : ι) : IntegrableOn (W j j i) (e j).target := by
    let K := e j '' tsupport (ρ j)
    have ck : IsCompact K := (compact j).image_of_continuousOn ((e j).continuousOn.mono (inside j))
    have sub : K⊆(e j).target := by
      rintro _ ⟨x,hx,rfl⟩
      exact (e j).map_source (inside j hx)
    have cont : ContinuousOn (W j j i) (e j).target :=
      ((cρ i).comp_continuousOn (e j).continuousOn_symm).smul (complexFormExteriorCoefficient_continuousOn (smooth j j))
    apply ((cont.mono sub).integrableOn_compact ck).of_forall_sdiff_eq_zero (e j).open_target.measurableSet
    intro z hz
    have absent : (e j).symm z∉tsupport (ρ j) := fun h => hz.2 ⟨_,h,(e j).right_inv hz.1⟩
    have germ : B j j =ᶠ[𝓝 z] 0 := by
      filter_upwards [((e j).continuousAt_symm hz.1).eventually (notMem_tsupport_iff_eventuallyEq.mp absent)] with w hw
      dsimp only [B]
      rw [show ρ j ((e j).symm w)=0 from hw,Complex.ofReal_zero,zero_mul]
      rfl
    simp [W,E,complexFormExteriorCoefficient,germ.fderiv_eq]
  calc
    _=∑ i, ∑ j, ∫ z in (e i).target, W i j i z := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← integral_finsetSum _ (fun j _ => intLeft i j)]
      apply setIntegral_congr_fun (e i).open_target.measurableSet
      intro z hz
      change ρ i ((e i).symm z) • complexFormExteriorCoefficient (a i) z=∑ j, W i j i z
      rw [split i z hz,Finset.smul_sum]
    _=∑ i, ∑ j, ∫ z in (e j).target, W j j i z := Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => same i j))
    _=∑ j, ∑ i, ∫ z in (e j).target, W j j i z := Finset.sum_comm
    _=∑ j, ∫ z in (e j).target, E j j z := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← integral_finsetSum _ (fun i _ => intRight j i)]
      apply setIntegral_congr_fun (e j).open_target.measurableSet
      intro z _
      simp only [W,← Finset.sum_smul,unity,one_smul]
    _=0 := Finset.sum_eq_zero (fun j _ => chart_cutoff_stokes _ (compact j) (inside j) (smooth j j))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.complex_form_exterior_finset
#print axioms TwoAxisHelicoid.finite_chart_partition_stokes
