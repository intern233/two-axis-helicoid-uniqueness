import TwoAxisHelicoid.ManuscriptMarkedSphereDivisor

namespace TwoAxisHelicoid
open Complex Set
open scoped OnePoint Topology

/-- The zero and infinity fibers of the physical Gauss map in this fixed marking. -/
def PhysicalSphericalGaussDivisor (t a : ℝ) (ht : 0 < t) (Z : ℂ → Fin 3 → ℝ) : Prop :=
  let G := fun z => sphericalNullGauss (immersionComplexCoefficient Z z)
  let L := rhombicPeriodPair t ht
  G (a:ℂ) = (↑(0:ℂ) : OnePoint ℂ) ∧ G (-(a:ℂ)) = ∞ ∧
    ∀ z ∉ L.lattice, (G z = (↑(0:ℂ) : OnePoint ℂ) ↔ z-a ∈ L.lattice) ∧
      (G z = ∞ ↔ z+a ∈ L.lattice)

theorem manuscript_physical_spherical_gauss_fibers {t a : ℝ} (ht : 0<t) (ha : a ∈ Ioo (0:ℝ) 1)
    {Z : ℂ → Fin 3 → ℝ} (hZ : TwoAxisHarmonicConformalImmersion (rhombicPeriodPair t ht) Z)
    (divisor : GaussZeroPoleData t a ht (immersionGaussMap Z)) :
    PhysicalSphericalGaussDivisor t a ht Z := by
  classical
  let L := rhombicPeriodPair t ht
  let G := fun z => sphericalNullGauss (immersionComplexCoefficient Z z)
  have pair := manuscript_physical_spherical_gauss_divisor ht ha hZ divisor
  refine ⟨pair.1,pair.2,?_⟩
  intro z hz
  have shift (w : ℂ) (hw : w ∉ L.lattice) (period : z-w ∈ L.lattice) : G z = G w := by
    have h := puncturedImmersionCoefficient_periodic hZ w (z-w) period
    rw [show w+(z-w)=z by ring,puncturedImmersionCoefficient_eq hz,puncturedImmersionCoefficient_eq hw] at h
    exact congrArg sphericalNullGauss h
  have off : (a:ℂ) ∉ L.lattice :=
    real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have zeroAt (p : z-a ∈ L.lattice) : G z = (↑(0:ℂ) : OnePoint ℂ) := (shift _ off p).trans pair.1
  have poleAt (p : z+a ∈ L.lattice) : G z = ∞ :=
    (shift (-(a:ℂ)) (by simpa only [neg_mem_iff] using off) (by simpa only [sub_neg_eq_add] using p)).trans pair.2
  have ordinary (p : z-a ∉ L.lattice) (q : z+a ∉ L.lattice) :
      G z ≠ (↑(0:ℂ) : OnePoint ℂ) ∧ G z ≠ ∞ := by
    have val := divisor.nonzero z ((not_mem_gaussLogPoleSet _ _ _).mpr ⟨hz,p,q⟩)
    have den : nullHorizontalMinus (immersionComplexCoefficient Z z) ≠ 0 := by
      intro h
      exact val (by simp [immersionGaussMap,nullGauss,h])
    have chart : G z = (↑(immersionGaussMap Z z) : OnePoint ℂ) := by
      simp only [G,sphericalNullGauss,ite_eq_right den,immersionGaussMap]
    rw [chart]
    exact ⟨fun h => val (OnePoint.coe_injective h),OnePoint.coe_ne_infty _⟩
  constructor
  · refine ⟨fun h => ?_,zeroAt⟩
    by_contra p
    by_cases q : z+a ∈ L.lattice
    · exact OnePoint.coe_ne_infty (0:ℂ) (h.symm.trans (poleAt q))
    · exact (ordinary p q).1 h
  · refine ⟨fun h => ?_,poleAt⟩
    by_contra q
    by_cases p : z-a ∈ L.lattice
    · exact OnePoint.coe_ne_infty (0:ℂ) ((zeroAt p).symm.trans h)
    · exact (ordinary p q).2 h

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_physical_spherical_gauss_fibers
