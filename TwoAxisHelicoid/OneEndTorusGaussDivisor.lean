import TwoAxisHelicoid.HelicoidalEndHorizontalZeros
import TwoAxisHelicoid.MarkedWeierstrassFibers
import TwoAxisHelicoid.TorusDoublePoleResidue
import TwoAxisHelicoid.NullGaussLocal

namespace TwoAxisHelicoid
open Complex Set Filter Topology
open scoped Topology

/-- Interior divisor of an actual null differential before choosing any
reflection axes. The two points are distinct on the quotient torus. -/
structure OneEndInteriorGaussDivisor (L : PeriodPair) (p : ℂ → Fin 3 → ℂ) (a b : ℂ) : Prop where
  zero_regular : a ∉ L.lattice
  pole_regular : b ∉ L.lattice
  distinct : b-a ∉ L.lattice
  opposite : b+a ∈ L.lattice
  height_zero : p a 2 = 0
  height_pole_point : p b 2 = 0
  minus_nonzero : nullHorizontalMinus (p a) ≠ 0
  plus_nonzero : nullHorizontalPlus (p b) ≠ 0
  simple_height_zero : deriv (fun w => p w 2) a ≠ 0
  simple_height_pole_point : deriv (fun w => p w 2) b ≠ 0
  height_fiber : ∀ z ∉ L.lattice, p z 2 = 0 ↔ z-a ∈ L.lattice ∨ z-b ∈ L.lattice
  gauss_zero : AnalyticAt ℂ (nullGauss ∘ p) a ∧ nullGauss (p a) = 0 ∧ deriv (nullGauss ∘ p) a ≠ 0
  gauss_pole : AnalyticAt ℂ (fun w => (nullGauss (p w))⁻¹) b ∧
    (nullGauss (p b))⁻¹ = 0 ∧ deriv (fun w => (nullGauss (p w))⁻¹) b ≠ 0
  gauss_ordinary : ∀ z ∉ L.lattice, z-a ∉ L.lattice → z-b ∉ L.lattice →
    AnalyticAt ℂ (nullGauss ∘ p) z ∧ nullGauss (p z) ≠ 0

/-- For any period pair, end orders and the vanishing residue of dg/g
force exactly one simple Gauss zero and one simple Gauss pole. There is
no hypothesis on the symmetry, finite divisor, or vertical flux. -/
theorem one_end_torus_has_simple_gauss_divisor (L : PeriodPair) (p : ℂ → Fin 3 → ℂ)
    (hhol : ∀ z ∉ L.lattice, ∀ j, AnalyticAt ℂ (fun w => p w j) z)
    (hper : ∀ z ω, ω ∈ L.lattice → p (z+ω) = p z)
    (hnull : ∀ z ∉ L.lattice, ComplexNull (p z)) (hnz : ∀ z ∉ L.lattice, p z ≠ 0)
    (hh : meromorphicOrderAt (fun z => p z 2) 0 = (-2 : ℤ))
    {κ : ℂ} {R : ℂ → ℂ} (hR : AnalyticAt ℂ R 0)
    (hend : ∀ᶠ z in 𝓝[≠] (0:ℂ), logDeriv (nullGauss ∘ p) z = κ/z^2+R z) :
    ∃ a b, OneEndInteriorGaussDivisor L p a b := by
  let H := fun z => p z 2
  have ho : meromorphicOrderAt H 0 = ((-2:ℤ):WithTop ℤ) := hh
  have hm : MeromorphicAt H 0 := meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [ho]; decide)
  have periodic (z ω : ℂ) (hω : ω ∈ L.lattice) : H (z+ω) = H z := congrFun (hper z ω hω) 2
  obtain ⟨A,g,hA,hg,he⟩ := torus_double_pole_has_zero_residue L (fun z hz => hhol z hz 2) periodic hm ho
  let B := g 0
  have eq : ∀ z ∉ L.lattice, H z=A*L.weierstrassP z+B := elliptic_double_pole_classification L A
    (fun z hz => (hhol z hz 2).differentiableAt) periodic hg he
  obtain ⟨⟨b,hb,bm⟩,⟨a,ha,ap⟩⟩ := helicoidal_end_both_horizontal_characteristics_vanish L p hhol hper hnull hh hR hend
  have am := (null_horizontal_not_both_zero (hnull a ha) (hnz a ha)).resolve_right (not_not.mpr ap)
  have bp := (null_horizontal_not_both_zero (hnull b hb) (hnz b hb)).resolve_left (not_not.mpr bm)
  have ah : H a=0 := by
    have e := null_horizontal_product (hnull a ha)
    by_contra h
    apply pow_ne_zero 2 h
    change (p a 2)^2 = 0
    simpa only [ap,mul_zero,neg_eq_zero] using e.symm
  have bh : H b=0 := by
    have e := null_horizontal_product (hnull b hb)
    by_contra h
    apply pow_ne_zero 2 h
    change (p b 2)^2 = 0
    simpa only [bm,zero_mul,neg_eq_zero] using e.symm
  have ab : b-a ∉ L.lattice := by
    intro hd
    have e := hper a (b-a) hd
    rw [show a+(b-a) = b by abel] at e
    exact am ((congrArg nullHorizontalMinus e).symm.trans bm)
  have fiber (z w : ℂ) (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
      H z = H w ↔ L.weierstrassP z = L.weierstrassP w := by
    rw [eq z hz,eq w hw]
    simp [hA]
  have pv := (fiber a b ha hb).mp (ah.trans bh.symm)
  have opposite := ((marked_weierstrass_fiber_iff L ha hb).mp pv).resolve_left ab
  have derivH (z : ℂ) (hz : z ∉ L.lattice) : deriv H z = A*L.derivWeierstrassP z := by
    have germ : H =ᶠ[𝓝 z] fun w => A*L.weierstrassP w+B := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw using eq w hw
    have hd := (((L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt.const_mul A).add_const B).deriv
    exact germ.deriv_eq.trans (by simpa only [L.deriv_weierstrassP] using hd)
  have da : deriv H a ≠ 0 := (derivH a ha).trans_ne (mul_ne_zero hA (marked_weierstrass_regular_of_distinct_fiber_points L ha hb pv ab))
  have db : deriv H b ≠ 0 := (derivH b hb).trans_ne (mul_ne_zero hA
    (marked_weierstrass_regular_of_distinct_fiber_points L hb ha pv.symm (fun h => ab (by simpa using L.lattice.neg_mem h))))
  have ef (z : ℂ) (hz : z ∉ L.lattice) : H z=0 ↔ z-a ∈ L.lattice ∨ z-b ∈ L.lattice := by
    rw [← ah,fiber z a hz ha,eq_comm (a := L.weierstrassP z),marked_weierstrass_fiber_iff L ha hz]
    have add : z+a ∈ L.lattice ↔ z-b ∈ L.lattice := by
      constructor
      · intro h
        convert L.lattice.sub_mem h opposite using 1
        abel
      · intro h
        convert L.lattice.add_mem h opposite using 1
        abel
    rw [add]
  refine ⟨a,b,ha,hb,ab,opposite,ah,bh,am,bp,da,db,ef,
    null_gauss_simple_zero (hhol a ha) am ah da,
    null_gauss_simple_pole (hhol b hb) (eventually_of_mem (L.isClosed_lattice.isOpen_compl.mem_nhds hb) (fun z hz => hnull z hz))
      bp bh db,?_⟩
  intro z hz h₁ h₂
  have nz : H z ≠ 0 := fun h => ((ef z hz).mp h).elim h₁ h₂
  have minus := (null_horizontal_nonzero_of_height (hnull z hz) nz).1
  exact ⟨(hhol z hz 2).div (null_horizontal_minus_analyticAt (hhol z hz)) minus,div_ne_zero nz minus⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.one_end_torus_has_simple_gauss_divisor
