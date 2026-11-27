import TwoAxisHelicoid.RegionChartFormIntegrals
import TwoAxisHelicoid.FiniteChartPartitionStokes

namespace TwoAxisHelicoid
open Complex MeasureTheory Filter Set Topology Function
open scoped Topology ContDiff

/-- Localize the exterior integral on a physical open region. All
terms are actual area integrals in its charts. The finite partition
need only sum to one on the region itself, and the differentiated
cutoffs cancel before the individual boundary patches are evaluated. -/
theorem finite_region_exterior_localization {M ι : Type*} [TopologicalSpace M] [Fintype ι]
    {Ω : Set M} (op : IsOpen Ω) (e : ι → OpenPartialHomeomorph M ℂ) (ρ : ι → M → ℝ) (a : ι → ℂ → ℂ)
    (unity : ∀ x∈Ω, ∑ i, ρ i x=1) (cρ : ∀ i, Continuous (ρ i))
    (compact : ∀ i, IsCompact (tsupport (ρ i))) (inside : ∀ i, tsupport (ρ i)⊆(e i).source)
    (cut : ∀ i j z, z∈(e i).target → ContDiffAt ℝ 1 (fun w => (ρ j ((e i).symm w):ℂ)) z)
    (reg : ∀ i z, z∈(e i).target → ContDiffAt ℝ 1 (a i) z)
    (hol : ∀ i j z, z∈((e i).symm.trans (e j)).source → AnalyticAt ℂ ((e i).symm.trans (e j)) z)
    (coeff : ∀ i j z, z∈((e i).symm.trans (e j)).source →
      a i z=a j (((e i).symm.trans (e j)) z)*deriv ((e i).symm.trans (e j)) z) :
    (∑ i, ∫ z in curveChartRegion (e i) Ω, ρ i ((e i).symm z) • complexFormExteriorCoefficient (a i) z)=
      ∑ j, ∫ z in curveChartRegion (e j) Ω,
        complexFormExteriorCoefficient (fun w => (ρ j ((e j).symm w):ℂ)*a j w) z := by
  classical
  let D := fun i => curveChartRegion (e i) Ω
  let B := fun i j w => (ρ j ((e i).symm w):ℂ)*a i w
  let E := fun i j z => complexFormExteriorCoefficient (B i j) z
  let W := fun i j k z => ρ k ((e i).symm z) • E i j z
  have smooth (i j z) (hz : z∈(e i).target) : ContDiffAt ℝ 1 (B i j) z :=
    (cut i j z hz).mul (reg i z hz)
  have region (i) : IsOpen (D i) := isOpen_curveChartRegion (e i) op
  have split (i z) (hz : z∈D i) : complexFormExteriorCoefficient (a i) z=∑ j, E i j z := by
    have germ : (fun w => ∑ j, B i j w) =ᶠ[𝓝 z] a i := by
      filter_upwards [(region i).mem_nhds hz] with w hw
      simp only [B,← Finset.sum_mul,← Complex.ofReal_sum,unity _ hw.2,Complex.ofReal_one,one_mul]
    have eq : complexFormExteriorCoefficient (fun w => ∑ j, B i j w) z=complexFormExteriorCoefficient (a i) z := by
      simp only [complexFormExteriorCoefficient,germ.fderiv_eq]
    exact eq.symm.trans (complex_form_exterior_finset _ (fun j => (smooth i j z hz.1).differentiableAt one_ne_zero))
  have same (i j : ι) : (∫ z in D i, W i j i z)=∫ z in D j, W j j i z :=
    localized_form_region_integrals (e i) (e j) op (a i) (a j) (ρ i) (ρ j) (inside i) (inside j)
      (hol i j) (coeff i j) (fun z hz => (reg j z hz).differentiableAt one_ne_zero)
      (fun z hz => (cut j j z hz).differentiableAt one_ne_zero)
  have intLeft (i j : ι) : IntegrableOn (W i j i) (D i) :=
    (chart_weighted_density_integrable (e i) (cρ i) (compact i) (inside i)
      (complexFormExteriorCoefficient_continuousOn (smooth i j))).mono_set inter_subset_left
  have intRight (j i : ι) : IntegrableOn (W j j i) (D j) :=
    (chart_cutoff_exterior_weight_integrable (e j) (ρ i) (ρ j) (cρ i) (compact j) (inside j)
      (a j) (smooth j j)).mono_set inter_subset_left
  calc
    _=∑ i, ∑ j, ∫ z in D i, W i j i z := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← integral_finsetSum _ (fun j _ => intLeft i j)]
      apply setIntegral_congr_fun (region i).measurableSet
      intro z hz
      change ρ i ((e i).symm z) • complexFormExteriorCoefficient (a i) z=∑ j, W i j i z
      rw [split i z hz,Finset.smul_sum]
    _=∑ i, ∑ j, ∫ z in D j, W j j i z := Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => same i j))
    _=∑ j, ∑ i, ∫ z in D j, W j j i z := Finset.sum_comm
    _=_ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← integral_finsetSum _ (fun i _ => intRight j i)]
      apply setIntegral_congr_fun (region j).measurableSet
      intro z hz
      simp only [W,← Finset.sum_smul,unity _ hz.2,one_smul]
      rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.finite_region_exterior_localization
