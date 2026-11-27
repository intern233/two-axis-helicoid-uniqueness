import TwoAxisHelicoid.PhasedPrimitivePeriods
import TwoAxisHelicoid.GlobalDataRigidity
import TwoAxisHelicoid.CertifiedGlobalImmersion

namespace TwoAxisHelicoid
open Complex Set

/-- Global rigidity for arbitrary actual periodic primitives in the full
explicit family. Their scalar closing equations are derived from the maps;
neither closing equations nor parameter equality are assumed. -/
theorem periodic_explicit_immersions_global_similarity
    {t₁ a₁ c₁ t₂ a₂ c₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (ha₁ : a₁ ∈ Ioo (0 : ℝ) 1) (ha₂ : a₂ ∈ Ioo (0 : ℝ) 1)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) {q₁ q₂ : ℂ} (hq₁ : ‖q₁‖ = 1) (hq₂ : ‖q₂‖ = 1)
    {X Y : ℂ → Fin 3 → ℝ}
    (hX : ∀ z ∉ (rhombicPeriodPair t₁ ht₁).lattice,
      HasFDerivAt X (nullRealDerivative (phasedCoordinateData t₁ a₁ c₁ ht₁ q₁ z)) z)
    (hY : ∀ z ∉ (rhombicPeriodPair t₂ ht₂).lattice,
      HasFDerivAt Y (nullRealDerivative (phasedCoordinateData t₂ a₂ c₂ ht₂ q₂ z)) z)
    (hPX : ∀ z ∉ (rhombicPeriodPair t₁ ht₁).lattice,
      ∀ ω ∈ (rhombicPeriodPair t₁ ht₁).lattice, X (z+ω) = X z)
    (hPY : ∀ z ∉ (rhombicPeriodPair t₂ ht₂).lattice,
      ∀ ω ∈ (rhombicPeriodPair t₂ ht₂).lattice, Y (z+ω) = Y z) :
    t₁ = t₂ ∧ a₁ = a₂ ∧
    ∃ (scale : ℝ) (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3)), 0 < scale ∧
      ∀ z ∉ (rhombicPeriodPair t₁ ht₁).lattice,
        WithLp.toLp 2 (Y z) = scale • R (WithLp.toLp 2 (X z))+b := by
  have h₁ := periodic_phased_coordinate_primitive_period_equations ht₁ ha₁ hc₁ hq₁ hX hPX
  have h₂ := periodic_phased_coordinate_primitive_period_equations ht₂ ha₂ hc₂ hq₂ hY hPY
  have he : (t₁,a₁) = (t₂,a₂) := existsUnique_actual_common_period_full_domain.unique
    ⟨ht₁,ha₁,h₁⟩ ⟨ht₂,ha₂,h₂⟩
  have het : t₁ = t₂ := congrArg Prod.fst he
  have hea : a₁ = a₂ := congrArg Prod.snd he
  subst t₂
  subst a₂
  refine ⟨rfl,rfl,?_⟩
  exact actual_two_coordinate_primitives_similarity
    (rhombicPeriodPair t₁ ht₁).isClosed_lattice.isOpen_compl
    (rhombic_punctured_plane_isConnected ht₁).2 ht₁ hc₁ hc₂ hq₁ hq₂ hX hY

theorem periodic_actual_primitive_parameters_certified {t a c : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hc : c ≠ 0)
    {X : ℂ → Fin 3 → ℝ} (hX : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (hp : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      ∀ ω ∈ (rhombicPeriodPair t ht).lattice, X (z+ω) = X z) :
    t = certifiedClosedParameters.t ∧ a = certifiedClosedParameters.a := by
  have h := periodic_actual_primitive_period_equations ht ha hc hX hp
  have he : (t,a) = (certifiedClosedParameters.t,certifiedClosedParameters.a) :=
    existsUnique_actual_common_period_full_domain.unique ⟨ht,ha,h⟩
      ⟨certifiedClosedParameters.height_pos,certifiedClosedParameters.abscissa_mem,
        certifiedClosedParameters.vertical_closed,certifiedClosedParameters.horizontal_closed⟩
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodic_explicit_immersions_global_similarity
