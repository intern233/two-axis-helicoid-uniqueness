import TwoAxisHelicoid.TorusAntiholomorphicInvolution
import TwoAxisHelicoid.ConjugateLatticeNormalization
import TwoAxisHelicoid.RhombicFixedLoci

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- Every actual antiholomorphic involution fixing zero and having connected
fixed locus admits a rhombic complex-linear normalization. This proves the
complex-torus classification step without presupposing a lift or a real basis. -/
theorem torus_real_structure_rhombic_normalization (L : PeriodPair)
    {f : PeriodTorus L → PeriodTorus L} (hf : TorusAntiholomorphic L L f)
    (h0 : f 0 = 0) (hinv : Function.Involutive f)
    (hconn : IsPreconnected {q : PeriodTorus L | f q = q}) :
    ∃ (s : ℂ) (t : ℝ) (hs : s ≠ 0) (ht : 0 < t)
      (hp : ∀ z : ℂ, z ∈ L.lattice ↔ s*z ∈ (rhombicPeriodPair t ht).lattice),
      ∀ q : PeriodTorus L,
        periodTorusScalingHomeomorph L (rhombicPeriodPair t ht) s hs hp (f q) =
          rhombicHorizontalReflection ht
            (periodTorusScalingHomeomorph L (rhombicPeriodPair t ht) s hs hp q) := by
  obtain ⟨c,hcc,hcL,hc⟩ := torus_antiholomorphic_involution_multiplier L hf h0 hinv
  obtain ⟨d,hd,hrot⟩ := antilinear_multiplier_rotation hcc
  let M := scaledPeriodPair L d hd
  have hM : ConjugationInvariantLattice M := antilinear_lattice_rotation_conjugation L hcL hd hrot
  let e := periodTorusScalingHomeomorph L M d hd (scaledPeriodPair_mem_iff L d hd)
  have hconnM : IsPreconnected {q : PeriodTorus M | periodTorusConjugation M hM q = q} :=
    homeomorph_fixed_locus_preconnected e
      (antilinear_reflection_scaling_commute L hc hd hrot hM) hconn
  obtain ⟨r,t,hr,ht,hrp⟩ := conjugation_connected_torus_rhombic_normalization M hM hconnM
  let s : ℂ := (r : ℂ)*d
  have hs : s ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hd
  have hp (z : ℂ) : z ∈ L.lattice ↔ s*z ∈ (rhombicPeriodPair t ht).lattice := by
    rw [scaledPeriodPair_mem_iff L d hd,hrp]
    simp only [s,mul_assoc]
  refine ⟨s,t,hs,ht,hp,?_⟩
  intro q
  obtain ⟨z,rfl⟩ := Quotient.exists_rep q
  change periodTorusScalingHomeomorph L (rhombicPeriodPair t ht) s hs hp
      (f (periodTorusProjection L z)) = _
  rw [hc]
  change periodTorusProjection (rhombicPeriodPair t ht) (s*(c*conj z)) =
    periodTorusProjection (rhombicPeriodPair t ht) (conj (s*z))
  have hsc : s*c = conj s := by
    dsimp only [s]
    rw [mul_assoc,hrot,map_mul,Complex.conj_ofReal]
  rw [← mul_assoc,hsc]
  exact congrArg (periodTorusProjection (rhombicPeriodPair t ht)) (map_mul conj s z).symm

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_real_structure_rhombic_normalization
