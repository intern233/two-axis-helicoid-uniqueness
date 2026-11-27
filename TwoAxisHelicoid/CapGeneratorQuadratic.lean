import TwoAxisHelicoid.GenusOneSpinQuadratic
import TwoAxisHelicoid.HarmonicIntegerCoreCap

namespace TwoAxisHelicoid
open Complex Set Matrix
open scoped Matrix ContDiff Manifold

theorem positive_scaled_orthonormal_pair_unique
    (p q : OrthonormalTangentPair) (A B : Fin 3 → ℝ) {k s : ℝ} (hk : 0 < k) (hs : 0 < s)
    (hp : p.1 = (k • A,k • B)) (hq : q.1 = (s • A,s • B)) : p = q := by
  have hA : A ⬝ᵥ A ≠ 0 := by
    intro hz
    have h := p.2.1
    rw [hp] at h
    simp only [smul_dotProduct,dotProduct_smul,hz,smul_zero] at h
    exact zero_ne_one h
  have hk2 : k*k*(A ⬝ᵥ A) = 1 := by
    have h := p.2.1
    rw [hp] at h
    simpa only [smul_dotProduct,dotProduct_smul,smul_eq_mul,mul_assoc] using h
  have hs2 : s*s*(A ⬝ᵥ A) = 1 := by
    have h := q.2.1
    rw [hq] at h
    simpa only [smul_dotProduct,dotProduct_smul,smul_eq_mul,mul_assoc] using h
  have he := mul_right_cancel₀ hA (hk2.trans hs2.symm)
  have hks : k = s := by nlinarith
  apply Subtype.ext
  rw [hp,hq,hks]

/-- The closed-lift test is phrased solely in terms of the cap's actual
differential along its marked, tangent-adapted frame curve. -/
def CapGeneratorHasClosedSpinLift (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ) (i : Fin 2) : Prop :=
  ∃ q : C(unitInterval,UnitQuaternion), q 1 = q 0 ∧ ∀ r : unitInterval,
    ∃ k : ℝ, 0 < k ∧ (unitQuaternionFrame (q r)).1 =
      (k • fderiv ℝ (F ∘ periodTorusProjection L) (periodBasisLine L i r) (L.basis i),
       k • fderiv ℝ (F ∘ periodTorusProjection L) (periodBasisLine L i r) (I*L.basis i))

variable {t a c : ℝ} (ht : 0 < t) (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    (m : ℤ) {C : ℂ} (hC0 : C ≠ 0) (hC : (C : ℂ)^2 = (c : ℂ)/(2*thetaSigma t a^2))
    {X : ℂ → Fin 3 → ℝ} (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hp : ∀ z ω₀, ω₀ ∈ (rhombicPeriodPair t ht).lattice → X (z+ω₀) = X z)
    (hh : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z 2 =
        I*c*((rhombicPeriodPair t ht).weierstrassP z-(rhombicPeriodPair t ht).weierstrassP a))
    (hg : ∀ z ∉ gaussLogPoleSet (rhombicPeriodPair t ht) a,
      nullGauss (puncturedImmersionCoefficient (rhombicPeriodPair t ht) X z) = thetaGauss t a m z)
    {F : PeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ}
    {U : Set (PeriodTorus (rhombicPeriodPair t ht))} (hU : IsOpen U)
    (hfix : ∀ q ∈ U, F q = periodTorusLift (rhombicPeriodPair t ht) X hp q)
    (hcore : Subtype.val '' puncturedGeneratorCore (rhombicPeriodPair t ht) ⊆ U)

include ht ha hc m hC0 hC hX hp hh hg hU hfix hcore in
theorem cap_generator_closed_lift_iff (i : Fin 2) :
    CapGeneratorHasClosedSpinLift (rhombicPeriodPair t ht) F i ↔ i = 0 ∨ Even m := by
  let L := rhombicPeriodPair t ht
  let e : C(unitInterval,UnitQuaternion) := ⟨fun r => adaptedWeierstrassGeneratorLift ht ha m hC0 i r,
    (adaptedWeierstrassGeneratorLift_continuous ht ha m hC0 i).comp continuous_subtype_val⟩
  have he (s : unitInterval) := harmonic_integer_cap_adapted_generator_frame ht ha hc m hC0 hC
    hX hp hh hg hU hfix hcore i s
  have hclosure : e 1 = e 0 ↔ i = 0 ∨ Even m := by
    fin_cases i
    · exact ⟨fun _ => Or.inl rfl,fun _ => (adaptedWeierstrassGeneratorLift_endpoints ht ha m hC0).1⟩
    · change e 1 = e 0 ↔ (1 : Fin 2) = 0 ∨ Even m
      rw [or_iff_right (by decide : (1 : Fin 2) ≠ 0)]
      exact adapted_second_generator_any_lift_closed_iff ht ha m hC0 e.continuous (fun _ => rfl)
  constructor
  · rintro ⟨q,hqc,hq⟩
    have hqe : unitQuaternionFrame ∘ q = unitQuaternionFrame ∘ e := by
      funext s
      obtain ⟨k,hk,hs⟩ := hq s
      exact positive_scaled_orthonormal_pair_unique _ _ _ _ hk
        (generator_spin_normalization_positive ht ha m hC0 i s) hs (he s)
    exact hclosure.mp ((quaternion_frame_lifts_closed_iff q.continuous e.continuous hqe 0 1).mp hqc)
  · intro hi
    exact ⟨e,hclosure.mpr hi,fun s =>
      ⟨_,generator_spin_normalization_positive ht ha m hC0 i s,he s⟩⟩

noncomputable def capGeneratorQuadratic (L : PeriodPair) (F : PeriodTorus L → Fin 3 → ℝ) :
    ZMod 2 × ZMod 2 → ZMod 2 := by
  classical
  exact torusQuadratic (if CapGeneratorHasClosedSpinLift L F 0 then 1 else 0)
    (if CapGeneratorHasClosedSpinLift L F 1 then 1 else 0)

include ht ha hc m hC0 hC hX hp hh hg hU hfix hcore in
theorem capGeneratorQuadratic_eq_integer :
    capGeneratorQuadratic (rhombicPeriodPair t ht) F = integerGeneratorQuadratic m := by
  classical
  unfold capGeneratorQuadratic integerGeneratorQuadratic
  rw [cap_generator_closed_lift_iff ht ha hc m hC0 hC hX hp hh hg hU hfix hcore,
    cap_generator_closed_lift_iff ht ha hc m hC0 hC hX hp hh hg hU hfix hcore]
  by_cases hm : Even m
  · simp [hm,hm.intCast_zmod_two]
  · have h1 : (m : ZMod 2) = 1 := (zmod_two_cases _).resolve_left
        (fun h0 => hm (ZMod.intCast_eq_zero_iff_even.mp h0))
    simp [hm,h1,show (1 : ZMod 2)+1 = 0 from by decide]

include ht ha hc m hC0 hC hX hp hh hg in
/-- An embedded branch supplies an actual smooth closed embedded cap
whose generator quadratic product is identified with the dimension
parity of the analytic multiplier spinor sections. -/
theorem harmonic_embedded_cap_generator_arf
    (hXi : Function.Injective (fun q : PuncturedPeriodTorus (rhombicPeriodPair t ht) =>
      periodTorusLift (rhombicPeriodPair t ht) X hp q.1)) :
    ∃ (F : PeriodTorus (rhombicPeriodPair t ht) → Fin 3 → ℝ)
      (cs : ChartedSpace (ℝ × ℝ) (PeriodTorus (rhombicPeriodPair t ht))), let _ := cs
      IsManifold 𝓘(ℝ,ℝ × ℝ) ∞ (PeriodTorus (rhombicPeriodPair t ht)) ∧
      Topology.IsClosedEmbedding F ∧ ContMDiff 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F ∧
      (∀ q, Function.Injective (mfderiv 𝓘(ℝ,ℝ × ℝ) 𝓘(ℝ,Fin 3 → ℝ) F q)) ∧
      ∀ v w, torusIntersectionModTwo v w = 1 →
        capGeneratorQuadratic (rhombicPeriodPair t ht) F v *
          capGeneratorQuadratic (rhombicPeriodPair t ht) F w =
        (Module.finrank ℂ (flatHolomorphicSections t 1 ((-1 : ℂ)^m)) : ZMod 2) := by
  obtain ⟨G,cs,V,hm,hclosed,hs,hi,hV,_,hCV,hfixV,_⟩ :=
    harmonic_integer_embedded_core_cap ht ha hc m hX hp hh hg hXi (puncturedGeneratorCore_isCompact _)
  refine ⟨G,cs,hm,hclosed,hs,hi,?_⟩
  intro v w hvw
  rw [capGeneratorQuadratic_eq_integer ht ha hc m hC0 hC hX hp hh hg hV hfixV hCV]
  exact integerGeneratorQuadratic_arf_eq_section_parity ht m hvw

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.cap_generator_closed_lift_iff
#print axioms TwoAxisHelicoid.capGeneratorQuadratic_eq_integer

#print axioms TwoAxisHelicoid.harmonic_embedded_cap_generator_arf
