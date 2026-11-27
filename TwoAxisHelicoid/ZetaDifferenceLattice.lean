import TwoAxisHelicoid.LatticePoleSets
import TwoAxisHelicoid.GaussDifferential

namespace TwoAxisHelicoid
open Complex Set
attribute [local irreducible] thetaZeta thetaSigma thetaEtaExpression

noncomputable def zetaDifferenceRegularized (t : ℝ) (ht : 0 < t) (a z : ℂ) : ℂ := by
  classical
  exact if z ∈ latticePoleSet (rhombicPeriodPair t ht) {a,-a} then 0
    else thetaZeta t (z-a)-thetaZeta t (z+a)

theorem zetaDifferenceRegularized_eq {t : ℝ} (ht : 0 < t) {a z : ℂ}
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    zetaDifferenceRegularized t ht a z = thetaZeta t (z-a)-thetaZeta t (z+a) := by
  apply ite_eq_right
  rintro ⟨b,hb,h⟩
  have hb' : b = a ∨ b = -a := by simpa only [mem_insert_iff,mem_singleton_iff] using hb
  rcases hb' with rfl | rfl
  · exact hm h
  · exact hp (by simpa only [sub_neg_eq_add] using h)

theorem zetaDifferenceRegularized_period {t : ℝ} (ht : 0 < t) (a w k : ℂ)
    (hw : w ∈ (rhombicPeriodPair t ht).lattice)
    (hq : ∀ z ∉ (rhombicPeriodPair t ht).lattice, thetaZeta t (z+w) = thetaZeta t z+k) :
    Function.Periodic (zetaDifferenceRegularized t ht a) w := by
  intro z
  have hmem := latticePoleSet_add_iff (rhombicPeriodPair t ht) {a,-a} z w hw
  by_cases hz : z ∈ latticePoleSet (rhombicPeriodPair t ht) {a,-a}
  · simp only [zetaDifferenceRegularized,ite_eq_left hz,ite_eq_left (hmem.mpr hz)]
  · have hm : z-a ∉ (rhombicPeriodPair t ht).lattice :=
      fun h => hz ⟨a,by simp,h⟩
    have hp : z+a ∉ (rhombicPeriodPair t ht).lattice :=
      fun h => hz ⟨-a,by simp,by simpa only [sub_neg_eq_add] using h⟩
    simp only [zetaDifferenceRegularized,ite_eq_right hz,ite_eq_right (hmem.not.mpr hz)]
    rw [show z+w-a = (z-a)+w by ring,show z+w+a = (z+a)+w by ring,hq _ hm,hq _ hp]
    ring

theorem zetaDifferenceRegularized_add_lattice {t : ℝ} (ht : 0 < t) (a z ω : ℂ)
    (hω : ω ∈ (rhombicPeriodPair t ht).lattice) :
    zetaDifferenceRegularized t ht a (z+ω) = zetaDifferenceRegularized t ht a z := by
  have htwo : Function.Periodic (zetaDifferenceRegularized t ht a) 2 :=
    zetaDifferenceRegularized_period ht a 2 (2*thetaEtaExpression t)
      (rhombicPeriodPair t ht).ω₁_mem_lattice (fun z _ => thetaZeta_add_two t z)
  have hhalf : Function.Periodic (zetaDifferenceRegularized t ht a) (1+I*t) :=
    zetaDifferenceRegularized_period ht a (1+I*t)
      (thetaEtaExpression t*(1+I*t)-Real.pi*I) (rhombicPeriodPair t ht).ω₂_mem_lattice
      (fun z hz => by simpa only [add_sub_assoc] using thetaZeta_add_half_of_pos ht ht hz)
  obtain ⟨m,n,he⟩ := PeriodPair.mem_lattice.mp hω
  rw [← he]
  change zetaDifferenceRegularized t ht a (z+((m:ℂ)*2+(n:ℂ)*(1+I*t))) = _
  have h1 := htwo.zsmul m z
  have h2 := hhalf.zsmul n (z+(m:ℂ)*2)
  simp only [zsmul_eq_mul] at h1 h2
  rw [← add_assoc,h2,h1]

theorem zetaDifference_add_lattice {t : ℝ} (ht : 0 < t) {a z ω : ℂ}
    (hω : ω ∈ (rhombicPeriodPair t ht).lattice)
    (hm : z-a ∉ (rhombicPeriodPair t ht).lattice)
    (hp : z+a ∉ (rhombicPeriodPair t ht).lattice) :
    thetaZeta t (z+ω-a)-thetaZeta t (z+ω+a) = thetaZeta t (z-a)-thetaZeta t (z+a) := by
  have hsm : z+ω-a ∉ (rhombicPeriodPair t ht).lattice := by
    intro h
    apply hm
    have he : (z+ω-a)-ω = z-a := by ring
    exact he ▸ (rhombicPeriodPair t ht).lattice.sub_mem h hω
  have hsp : z+ω+a ∉ (rhombicPeriodPair t ht).lattice := by
    intro h
    apply hp
    have he : (z+ω+a)-ω = z+a := by ring
    exact he ▸ (rhombicPeriodPair t ht).lattice.sub_mem h hω
  rw [← zetaDifferenceRegularized_eq ht hsm hsp,← zetaDifferenceRegularized_eq ht hm hp]
  exact zetaDifferenceRegularized_add_lattice ht a z ω hω

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.zetaDifference_add_lattice
