import TwoAxisHelicoid.AnalyticSpinArfIdentity
import TwoAxisHelicoid.HarmonicIntegerCapAtlas
import TwoAxisHelicoid.HarmonicTorusC1Normalization

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ContDiff Manifold

/-- The actual embedded punctured integer branch has a closed regular cap
whose spatial Arf invariant is computed in every symplectic basis. The
cap fixes a neighborhood of the two genuine generators. The spinor
constant is constructed and only punctured periodicity is used, so even
arbitrary values of a total representative at lattice points are allowed. -/
theorem actual_embedded_integer_branch_cap_arf
    {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0) (m : ℤ)
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hXi : Function.Injective (harmonicTorusImmersion hX))
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z) :
    let L := rhombicPeriodPair t ht
    ∃ (F : PeriodTorus L → Fin 3 → ℝ) (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus L))
      (U : Set (PeriodTorus L)), let _ := cs
      IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus L) ∧
      IsClosedEmbedding F ∧ ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F ∧
      (∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F q)) ∧
      IsOpen U ∧ 0 ∉ U ∧ Subtype.val '' puncturedGeneratorCore L ⊆ U ∧
      (∀ q : PuncturedPeriodTorus L, q.1 ∈ U → F q.1 = harmonicTorusImmersion hX q) ∧
      (∀ q ≠ 0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℝ × ℝ) ∞ (@id (PeriodTorus L)) q ∧
        ContMDiffAt 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,ℂ) ∞ (@id (PeriodTorus L)) q) ∧
      ∀ v w, torusIntersectionModTwo v w = 1 →
        capAmbientSpinQuadratic L F v * capAmbientSpinQuadratic L F w = (if Even m then 1 else 0) := by
  let L := rhombicPeriodPair t ht
  let Y := punctureFilledMap L X
  let hY := hX.punctureFilled (fun _ hz => rhombic_conj_mem ht hz)
  have hper := punctureFilledMap_periodic hX.periodic
  have hhY (z : ℂ) (hz : z ∉ L.lattice) :
      puncturedImmersionCoefficient L Y z 2 = I*c*(L.weierstrassP z-L.weierstrassP a) := by
    rw [show Y = punctureFilledMap L X from rfl,punctureFilledMap_coefficient hz]
    exact hh z hz
  have hgY (z : ℂ) (hz : z ∉ gaussLogPoleSet L a) :
      nullGauss (puncturedImmersionCoefficient L Y z) = thetaGauss t a m z := by
    rw [show Y = punctureFilledMap L X from rfl,punctureFilledMap_coefficient ((not_mem_gaussLogPoleSet _ _ _).mp hz).1]
    exact hg z hz
  obtain ⟨F,cs,U,hm,he,hs,hi,hU,h0,hcore,hfix,hcompat⟩ :=
    harmonic_integer_embedded_cap_with_compatible_atlas ht ha hc m hY hper hhY hgY hXi
      (puncturedGeneratorCore_isCompact L)
  obtain ⟨C,hC0,hC⟩ := exists_spinor_normalizing_constant ht
    (real_not_mem_rhombic_lattice_of_pos ht ha.1 (ha.2.trans (by norm_num))) hc
  refine ⟨F,cs,U,hm,he,hs,hi,hU,h0,hcore,fun q hq => hfix q.1 hq,fun q hq => (hcompat q hq).2.2,?_⟩
  intro v w hvw
  rw [ambient_cap_arf_eq_standard_analytic_spin_sections ht ha hc m hC0 hC hY hper hhY hgY hU hfix hcore hvw,
    analytic_integer_spin_section_finrank ht m]
  split <;> norm_num

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_embedded_integer_branch_cap_arf
