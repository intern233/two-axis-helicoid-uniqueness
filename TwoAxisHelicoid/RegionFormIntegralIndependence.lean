import TwoAxisHelicoid.SmoothRegionStokes

namespace TwoAxisHelicoid
open Complex MeasureTheory Set Filter Function Topology
open scoped Topology Manifold ContDiff

/-- The product of two physical chart weights is supported on the
overlap. The area integral on the physical region can thus be computed
in either of its two oriented charts. -/
theorem two_weight_exterior_region_swap {M : Type*} [TopologicalSpace M]
    (e d : OpenPartialHomeomorph M ℂ) {Ω : Set M} (op : IsOpen Ω)
    (ρ σ : M → ℝ) (he : tsupport ρ⊆e.source) (hd : tsupport σ⊆d.source)
    (a b : ℂ → ℂ) (hol : ∀ z∈(e.symm.trans d).source, AnalyticAt ℂ (e.symm.trans d) z)
    (coeff : ∀ z∈(e.symm.trans d).source, a z=b ((e.symm.trans d) z)*deriv (e.symm.trans d) z)
    (reg : ∀ z∈d.target, DifferentiableAt ℝ b z) :
    (∫ z in curveChartRegion e Ω, (ρ (e.symm z)*σ (e.symm z)) • complexFormExteriorCoefficient a z)=
      ∫ z in curveChartRegion d Ω, (ρ (d.symm z)*σ (d.symm z)) • complexFormExteriorCoefficient b z := by
  classical
  let t := e.symm.trans d
  let w := fun x => ρ x*σ x
  let W := Ω.indicator w
  have middle := complex_form_integral_on_overlap e d a b W t.open_source.measurableSet (Subset.rfl : t.source⊆t.source)
    hol coeff (fun z hz => reg _ (d.map_source hz.2))
  rw [show (e.symm.trans d) '' t.source=t.target from t.image_source_eq_target] at middle
  have neE (x : M) (absent : x∉e.source) : W x=0 := by
    by_cases hx : x∈Ω
    · simp only [W,indicator_of_mem hx,w,image_eq_zero_of_notMem_tsupport (fun h => absent (he h)),zero_mul]
    · exact indicator_of_notMem hx w
  have neD (x : M) (absent : x∉d.source) : W x=0 := by
    by_cases hx : x∈Ω
    · simp only [W,indicator_of_mem hx,w,image_eq_zero_of_notMem_tsupport (fun h => absent (hd h)),mul_zero]
    · exact indicator_of_notMem hx w
  rw [← indicator_weight_chart_integral e op w,← indicator_weight_chart_integral d op w]
  calc
    _=(∫ z in t.source, W (e.symm z) • complexFormExteriorCoefficient a z) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero e.open_target.measurableSet (fun z hz => hz.1)
      intro z hz
      change W (e.symm z) • _=0
      rw [neD (e.symm z) (fun h => hz.2 ⟨hz.1,h⟩),zero_smul]
    _=(∫ z in t.target, W (d.symm z) • complexFormExteriorCoefficient b z) := middle.symm
    _=_ := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero d.open_target.measurableSet (fun z hz => hz.1)
      intro z hz
      change W (d.symm z) • _=0
      rw [neE (d.symm z) (fun h => hz.2 ⟨hz.1,h⟩),zero_smul]

/-- Multiply a one-form's exterior density by a partition in a
different chart cover. This changes neither its value nor
integrability on the specified region. -/
theorem split_chart_exterior_by_partition {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {Ω : Set M}
    (op : IsOpen Ω) (Q : CurveRegionPartition Ω) (e : OpenPartialHomeomorph M ℂ) {ρ : M → ℝ}
    (cρ : Continuous ρ) (compact : IsCompact (tsupport ρ)) (support : tsupport ρ⊆e.source)
    (a : ℂ → ℂ) (smooth : ∀ z∈e.target, ContDiffAt ℝ 1 a z) :
    (∫ z in curveChartRegion e Ω, ρ (e.symm z) • complexFormExteriorCoefficient a z)=
      ∑ j, ∫ z in curveChartRegion e Ω, (ρ (e.symm z)*Q.weight j (e.symm z)) • complexFormExteriorCoefficient a z := by
  classical
  have integ (j : Q.indices) : IntegrableOn (fun z =>
      (ρ (e.symm z)*Q.weight j (e.symm z)) • complexFormExteriorCoefficient a z) (curveChartRegion e Ω) := by
    simp_rw [mul_smul]
    apply IntegrableOn.mono_set _ (show curveChartRegion e Ω⊆e.target from inter_subset_left)
    exact chart_weighted_density_integrable e cρ compact support
      (((Q.smooth j).continuous.comp_continuousOn e.continuousOn_symm).smul (complexFormExteriorCoefficient_continuousOn smooth))
  rw [← integral_finsetSum _ (fun j _ => integ j)]
  apply setIntegral_congr_fun (isOpen_curveChartRegion e op).measurableSet
  intro z hz
  simp only [← Finset.sum_smul,← Finset.mul_sum,Q.unity _ (subset_closure hz.2),mul_one]

/-- Independence of the physical region integral from both the
chosen finite chart cover and the chosen partition. -/
theorem region_exterior_integral_independent {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ,ℂ) ω M] {Ω : Set M} (op : IsOpen Ω) (P Q : CurveRegionPartition Ω)
    (a : OpenPartialHomeomorph M ℂ → ℂ → ℂ)
    (reg : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ z∈e.target, ContDiffAt ℝ 1 (a e) z)
    (coeff : ∀ e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M, ∀ d∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M,
      ∀ z∈(e.symm.trans d).source, a e z=a d ((e.symm.trans d) z)*deriv (e.symm.trans d) z) :
    (∑ i, ∫ z in curveChartRegion (P.chart i) Ω,
      P.weight i ((P.chart i).symm z) • complexFormExteriorCoefficient (a (P.chart i)) z)=
    ∑ j, ∫ z in curveChartRegion (Q.chart j) Ω,
      Q.weight j ((Q.chart j).symm z) • complexFormExteriorCoefficient (a (Q.chart j)) z := by
  classical
  let localInt := fun (e : OpenPartialHomeomorph M ℂ) (w : M → ℝ) =>
    ∫ z in curveChartRegion e Ω, w (e.symm z) • complexFormExteriorCoefficient (a e) z
  have split (A B : CurveRegionPartition Ω) (i : A.indices) :
      localInt (A.chart i) (A.weight i)=∑ j, localInt (A.chart i) (fun x => A.weight i x*B.weight j x) :=
    split_chart_exterior_by_partition op B (A.chart i) (A.smooth i).continuous (A.compact i)
      ((A.supported i).trans (A.patch i).carrier_subset_source) _ (reg _ (A.member i))
  have swap (i : P.indices) (j : Q.indices) :
      localInt (P.chart i) (fun x => P.weight i x*Q.weight j x)=localInt (Q.chart j) (fun x => Q.weight j x*P.weight i x) := by
    have h := two_weight_exterior_region_swap (P.chart i) (Q.chart j) op (P.weight i) (Q.weight j)
      ((P.supported i).trans (P.patch i).carrier_subset_source) ((Q.supported j).trans (Q.patch j).carrier_subset_source)
      (a _) (a _) (fun z hz => (complexAtlas_realized_transition (P.member i) (Q.member j) hz).analyticAt)
      (coeff _ (P.member i) _ (Q.member j)) (fun z hz => (reg _ (Q.member j) z hz).differentiableAt one_ne_zero)
    exact h.trans (by apply setIntegral_congr_fun (isOpen_curveChartRegion _ op).measurableSet; intro z _; exact congrArg (fun v : ℝ => v • complexFormExteriorCoefficient (a (Q.chart j)) z) (mul_comm _ _))
  change (∑ i, localInt (P.chart i) (P.weight i))=∑ j, localInt (Q.chart j) (Q.weight j)
  simp_rw [split P Q,swap]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => (split Q P j).symm)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.region_exterior_integral_independent

