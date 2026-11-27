import TwoAxisHelicoid.RhombicAxisComponents
import TwoAxisHelicoid.HarmonicTorusC1Normalization

namespace TwoAxisHelicoid
open Complex Set Topology
open scoped ComplexConjugate

/-- For the actual embedded immersion, equality of spatial positions
is equivalent to equality of regular parameters in the torus. -/
theorem marked_torus_spatial_eq_iff_projection_eq {L : PeriodPair} {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion L X) (hi : Function.Injective (harmonicTorusImmersion hX))
    {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    X z=X w ↔ periodTorusProjection L z=periodTorusProjection L w := by
  constructor
  · intro e
    exact congrArg Subtype.val (hi ((harmonicTorusImmersion_projection hX hz).trans (e.trans (harmonicTorusImmersion_projection hX hw).symm)))
  · intro e
    exact (harmonicTorusImmersion_projection hX hz).symm.trans
      ((congrArg (harmonicTorusImmersion hX) (Subtype.ext e)).trans (harmonicTorusImmersion_projection hX hw))

/-- In the marked parameter plane the preimage of the entire physical
vertical axis is the union of its integral vertical lines, and the
preimage of the horizontal axis is the union of the lattice-height
horizontal lines, with all lattice punctures removed. -/
theorem rhombic_physical_axes_preimages {t : ℝ} (ht : 0<t) {X : ℂ → Fin 3 → ℝ}
    (hX : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) X)
    (hi : Function.Injective (harmonicTorusImmersion hX)) {z : ℂ} (hz : z ∉ (rhombicPeriodPair t ht).lattice) :
    ((X z 0=0 ∧ X z 1=0) ↔ ∃ n : ℤ, z.re=n) ∧ ((X z 1=0 ∧ X z 2=0) ↔ ∃ n : ℤ, z.im=n*t) := by
  let L := rhombicPeriodPair t ht
  have hc : conj z ∉ L.lattice := fun h => hz (by simpa using rhombic_conj_mem ht h)
  have hm : -conj z ∉ L.lattice := fun h => hc (by simpa using L.lattice.neg_mem h)
  have v := (marked_torus_spatial_eq_iff_projection_eq hX hi hm hz).trans (rhombic_vertical_fixed_projection_iff ht z)
  have h := (marked_torus_spatial_eq_iff_projection_eq hX hi hc hz).trans (rhombic_horizontal_fixed_projection_height ht z)
  rw [hX.neg _ hc,hX.conjugation z hz] at v
  rw [hX.conjugation z hz] at h
  constructor
  · rw [← v]
    constructor
    · rintro ⟨e₀,e₁⟩
      ext i
      fin_cases i <;> simp [e₀,e₁]
    · intro e
      have e0 := congrFun e 0
      have e1 := congrFun e 1
      change -X z 0=X z 0 at e0
      change -X z 1=X z 1 at e1
      constructor <;> linarith
  · rw [← h]
    constructor
    · rintro ⟨e₁,e₂⟩
      ext i
      fin_cases i <;> simp [e₁,e₂]
    · intro e
      have e1 := congrFun e 1
      have e2 := congrFun e 2
      change -X z 1=X z 1 at e1
      change -X z 2=X z 2 at e2
      constructor <;> linarith

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.rhombic_physical_axes_preimages
