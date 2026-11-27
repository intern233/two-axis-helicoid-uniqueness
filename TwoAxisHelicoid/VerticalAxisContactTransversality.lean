import TwoAxisHelicoid.MinimalContactOnOneLine
import TwoAxisHelicoid.ComparisonHelicoidAtPitch
import TwoAxisHelicoid.HelicoidLocalCoincidence
import TwoAxisHelicoid.RhombicPhysicalAxisPreimages

namespace TwoAxisHelicoid
open Complex Set Filter Topology Function InnerProductSpace
open scoped Topology ContDiff

/-- On a closed embedded marked torus, an axes-only intersection with
the comparison helicoid is transverse at every vertical point of
nonzero height. The local alternate case of identical sheets is
excluded by analytic continuation and the topology of the torus. -/
theorem vertical_axis_transverse_away_from_crossing {L : PeriodPair}
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion L X)
    (embedded : IsClosedEmbedding (harmonicTorusImmersion hX))
    {g : ℂ} (hg : normSq g=1) {α : ℝ} (ha : α≠0) (b : ℝ)
    (intersection : ∀ z∉L.lattice, X z∈range (axisRuledHelicoid g α b) →
      (X z 1=0 ∧ X z 2=0) ∨ (X z 0=0 ∧ X z 1=0))
    {a : ℂ} (regular : a∉L.lattice) (axis : X a 0=0 ∧ X a 1=0) (height : X a 2≠0) :
    range (fderiv ℝ X a)≠range (fderiv ℝ (axisRuledHelicoid g α b) (I*(X a 2))) := by
  let Y := conformalComparisonHelicoid g α b
  let h := X a 2
  let v := I*(α*(h-b):ℝ)
  let line : Set (Fin 3 → ℝ) := {p | p 0=0 ∧ p 1=0}
  have nh : ∀ᶠ z in 𝓝 a, z∉L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds regular
  have hx := nh.mono (fun z hz => And.intro (hX.harmonic z hz) (hX.conformal z hz))
  have hy (w : ℂ) := conformalComparisonHelicoid_regular hg ha b w
  have meet : X a=Y v := by
    change X a=axisRuledHelicoid g α b (helicoidRulingParameter α b (I*(α*(h-b):ℝ)))
    rw [helicoidRulingParameter_at_axis ha]
    ext j
    fin_cases j
    · simpa [axisRuledHelicoid] using axis.1
    · simpa [axisRuledHelicoid] using axis.2
    · simp [axisRuledHelicoid,h]
  have inRuled {p : Fin 3 → ℝ} (mem : p∈range Y) : p∈range (axisRuledHelicoid g α b) := by
    obtain ⟨z,rfl⟩ := mem
    exact ⟨helicoidRulingParameter α b z,rfl⟩
  have separate : ¬ ∀ᶠ z in 𝓝 a, X z∈range Y := fun all =>
    marked_torus_not_locally_contained_in_helicoid hX embedded hg α b regular (all.mono (fun _ p => inRuled p))
  have unique : InjOn (fun P : Fin 3 → ℝ => P 2) line := by
    intro P hp Q hq eq
    ext j
    fin_cases j
    · exact hp.1.trans hq.1.symm
    · exact hp.2.trans hq.2.symm
    · exact eq
  have nz : ∀ᶠ z in 𝓝 a, X z 2≠0 :=
    (differentiableAt_pi.mp (hX.differentiable _ regular) 2).continuousAt.eventually_ne height
  have loc : ∀ᶠ z in 𝓝 a, X z∈Y '' univ → X z∈line := by
    filter_upwards [nh,nz] with z hz hn hit
    exact (intersection z hz (inRuled (image_subset_range _ _ hit))).resolve_left (fun e => hn e.2)
  have distinct := distinct_minimal_sheets_transverse_on_line hx (Eventually.of_forall fun w => ⟨(hy w).1,(hy w).2.1⟩)
    (hX.immersion a regular) (hy v).2.2 meet separate univ_mem line (fun P => P 2) (continuous_apply _) unique loc
  intro eq
  apply distinct
  apply SetLike.coe_injective
  exact eq.trans (conformalComparisonHelicoid_axis_tangent hg ha b h).symm

/-- Proposition 4.2 by the manuscript's local intersection argument.
No transverse-intersection assumption is made along the marked axis. -/
theorem harmonic_integer_axis_parameter_by_equal_angle_contact
    {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0) (hG : thetaG t a=0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (embedded : IsClosedEmbedding (harmonicTorusImmersion hX))
    (hh : ∀ z∉(rhombicPeriodPair t ht).lattice, puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2=
      coordinateData t a c ht z 2)
    (hg : ∀ z∉gaussLogPoleSet (rhombicPeriodPair t ht) a, nullGauss
      (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z)=thetaGauss t a m z)
    (intersection : ∀ z∉(rhombicPeriodPair t ht).lattice,
      X z∈range (axisRuledHelicoid (thetaGauss t a m (I*t)) (2*(a-m)/c) (X (I*t) 2)) →
      (X z 1=0 ∧ X z 2=0) ∨ (X z 0=0 ∧ X z 1=0)) :
    m=0 ∨ m=1 := by
  apply harmonic_integer_axis_parameter_of_distinct_tangent_planes ht ha hc hG m hX hh hg
  intro y hy off
  have reg := (integerAxis_regular_points ht ha hy).1
  have eqs := rhombic_physical_axes_preimages ht hX embedded.injective reg
  have axis : X (I*y) 0=0 ∧ X (I*y) 1=0 := eqs.1.mpr ⟨0,by simp⟩
  apply vertical_axis_transverse_away_from_crossing hX embedded
    (thetaGauss_axis_normSq ht ha m ⟨ht,by linarith⟩) (integer_helicoidal_pitch_ne_zero ha hc m) _ intersection reg axis
  intro zero
  obtain ⟨n,hn⟩ := eqs.2.mp ⟨axis.2,zero⟩
  have eq : y=(n:ℝ)*t := by simpa using hn
  have pos : 0<(n:ℝ) := by
    by_contra! small
    exact hy.1.not_ge (eq.trans_le (mul_nonpos_of_nonpos_of_nonneg small ht.le))
  have lt : (n:ℝ)<2 := by
    by_contra! large
    exact hy.2.not_ge ((mul_le_mul_of_nonneg_right large ht.le).trans_eq eq.symm)
  have intpos : (0:ℤ)<n := by exact_mod_cast pos
  have intlt : n<(2:ℤ) := by exact_mod_cast lt
  have one : n=1 := by omega
  exact off (by simpa [one] using eq)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.vertical_axis_transverse_away_from_crossing
#print axioms TwoAxisHelicoid.harmonic_integer_axis_parameter_by_equal_angle_contact
