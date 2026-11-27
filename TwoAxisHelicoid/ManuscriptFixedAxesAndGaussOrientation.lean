import TwoAxisHelicoid.TorusVerticalSchwarzSymmetry
import TwoAxisHelicoid.SphericalNullGauss
import TwoAxisHelicoid.SymmetricHeightRoot
import TwoAxisHelicoid.NullGaussSymmetry
import TwoAxisHelicoid.TorusTwoReflections

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology OnePoint ComplexConjugate

private theorem image_of_schwarz_fixed_set {D V : Type*} {X : D → V}
    (injective : Function.Injective X) (f : D → D) (R : V → V) (axis : ℝ → V)
    (action : ∀ q, X (f q) = R (X q)) (fixed : ∀ v, R v = v ↔ v ∈ range axis)
    (contained : ∀ r, axis r ∈ range X) :
    X '' {q | f q = q} = range axis := by
  ext v
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (fixed _).mp ((action q).symm.trans (congrArg X hq))
  · rintro ⟨r,rfl⟩
    obtain ⟨q,hq⟩ := contained r
    refine ⟨q,injective ((action q).trans ((fixed _).mpr ⟨r,hq.symm⟩)),hq⟩

/-- Both finite Schwarz fixed sets of the actual embedded punctured torus
have precisely the spatial images printed in Section 3.1. -/
theorem manuscript_punctured_schwarz_axes (L : PeriodPair) (X : PeriodTorus L → Fin 3 → ℝ)
    (embedded : IsClosedEmbedding (fun q : PuncturedPeriodTorus L => X q.1))
    (horizontal : ∀ r : ℝ, (![r,0,0] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (vertical : ∀ r : ℝ, (![0,0,r] : Fin 3 → ℝ) ∈ range (fun q : PuncturedPeriodTorus L => X q.1))
    (regular : ∀ z ∉ L.lattice, (∀ j, HarmonicAt (fun w => X (periodTorusProjection L w) j) z) ∧
      ConformalCoordinateDerivatives (X ∘ periodTorusProjection L) z ∧
      Function.Injective (fderiv ℝ (X ∘ periodTorusProjection L) z)) :
    ∃ f g : PuncturedPeriodTorus L ≃ₜ PuncturedPeriodTorus L,
      PuncturedTorusAntiholomorphic L L f ∧ PuncturedTorusAntiholomorphic L L g ∧
      (∀ q, X (f q).1 = halfTurnX (X q.1)) ∧ (∀ q, X (g q).1 = halfTurnZ (X q.1)) ∧
      (fun q : PuncturedPeriodTorus L => X q.1) '' {q | f q = q} = range (fun r : ℝ => ![r,0,0]) ∧
      (fun q : PuncturedPeriodTorus L => X q.1) '' {q | g q = q} = range (fun r : ℝ => ![0,0,r]) := by
  obtain ⟨f,hf,af⟩ := closed_embedded_torus_horizontal_schwarz L X embedded horizontal regular
  obtain ⟨g,hg,ag⟩ := closed_embedded_torus_vertical_schwarz L X embedded vertical regular
  refine ⟨f,g,hf,hg,af,ag,
    image_of_schwarz_fixed_set embedded.injective f halfTurnX _ af halfTurnX_fixed_iff horizontal,
    image_of_schwarz_fixed_set embedded.injective g halfTurnZ _ ag ?_ vertical⟩
  intro v
  constructor
  · intro h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    change -v 0 = v 0 at h₀
    change -v 1 = v 1 at h₁
    have e₀ : v 0 = 0 := by linarith
    have e₁ : v 1 = 0 := by linarith
    refine ⟨v 2,?_⟩
    ext j
    fin_cases j <;> simp [e₀,e₁]
  · rintro ⟨r,rfl⟩
    simp [halfTurnZ]

/-- A signed change of parameter on the marked torus itself preserves the
end, the finite axial point and both antiholomorphic involutions. -/
private theorem marked_signed_coordinate {t : ℝ} (ht : 0 < t) {k : ℝ} (sign : k = 1 ∨ k = -1) :
    let L := rhombicPeriodPair t ht
    let π := periodTorusProjection L
    ∃ e : PeriodTorus L ≃ₜ PeriodTorus L, TorusHolomorphic L L e ∧
      (∀ z : ℂ, e (π z) = π ((k:ℂ)*z)) ∧ e (π 0) = π 0 ∧ e (π 1) = π 1 ∧
      Function.Commute e (rhombicHorizontalReflection ht) ∧
      Function.Commute e (rhombicVerticalReflection ht) := by
  intro L π
  have kn : (k:ℂ) ≠ 0 := by rcases sign with h | h <;> simp [h]
  have stable (z : ℂ) : z ∈ L.lattice ↔ (k:ℂ)*z ∈ L.lattice := by
    rcases sign with h | h <;> simp [h]
  let e := periodTorusScalingHomeomorph L L (k:ℂ) kn stable
  have coord (z : ℂ) : e (π z) = π ((k:ℂ)*z) := rfl
  have halfPeriod : π (-1) = π 1 := by
    have two : (2:ℂ) ∈ L.lattice := L.ω₁_mem_lattice
    have h := periodTorusProjection_add_lattice L (-1) 2 two
    norm_num at h
    exact h.symm
  refine ⟨e,?_,coord,?_,?_,?_,?_⟩
  · exact fun z => ⟨fun w : ℂ => (k:ℂ)*w,analyticAt_const.mul analyticAt_id,
      Filter.Eventually.of_forall fun w => (coord w).symm⟩
  · rw [coord,mul_zero]
  · rw [coord,mul_one]
    rcases sign with h | h
    · simp [h]
    · simpa [h] using halfPeriod
  · intro q
    obtain ⟨z,rfl⟩ := Quotient.exists_rep q
    change π ((k:ℂ)*conj z) = π (conj ((k:ℂ)*z))
    rw [map_mul,Complex.conj_ofReal]
  · intro q
    obtain ⟨z,rfl⟩ := Quotient.exists_rep q
    change π ((k:ℂ)*(-conj z)) = π (-conj ((k:ℂ)*z))
    rw [map_mul,Complex.conj_ofReal,mul_neg]

/-- The coordinate choice in the order of Section 3.2. A zero on the real
fixed circle away from the two marked points and its opposite pole determine
the sign of the coordinate without using a formula for the height form. -/
theorem manuscript_real_fixed_divisor_orientation {t : ℝ} (ht : 0 < t)
    (G : PeriodTorus (rhombicPeriodPair t ht) → OnePoint ℂ)
    (q : PeriodTorus (rhombicPeriodPair t ht)) (realPoint : rhombicHorizontalReflection ht q = q)
    (finite : q ≠ 0) (offCross : q ≠ periodTorusProjection (rhombicPeriodPair t ht) 1)
    (zeroAt : G q = (↑(0:ℂ) : OnePoint ℂ)) (poleAt : G (-q) = ∞) :
    let L := rhombicPeriodPair t ht
    let π := periodTorusProjection L
    ∃ (a k : ℝ) (e : PeriodTorus L ≃ₜ PeriodTorus L), a ∈ Ioo (0:ℝ) 1 ∧
      (k = 1 ∨ k = -1) ∧ TorusHolomorphic L L e ∧
      (∀ z : ℂ, e (π z) = π ((k:ℂ)*z)) ∧ e (π 0) = π 0 ∧ e (π 1) = π 1 ∧
      Function.Commute e (rhombicHorizontalReflection ht) ∧ Function.Commute e (rhombicVerticalReflection ht) ∧
      e (π a) = q ∧ e (π (-(a:ℂ))) = -q ∧
      G (e (π a)) = (↑(0:ℂ) : OnePoint ℂ) ∧ G (e (π (-(a:ℂ)))) = ∞ := by
  intro L π
  obtain ⟨x,hx⟩ := (rhombic_horizontal_fixed_iff_real ht q).mp realPoint
  let n : ℤ := ⌊x/2⌋
  let r : ℝ := x-2*(n:ℝ)
  have nonneg : 0 ≤ r := by dsimp [r,n]; linarith [Int.floor_le (x/2)]
  have small : r < 2 := by dsimp [r,n]; linarith [Int.lt_floor_add_one (x/2)]
  have period : (2:ℂ)*(n:ℂ) ∈ L.lattice := by
    apply PeriodPair.mem_lattice.mpr
    exact ⟨n,0,by simp [L,rhombicPeriodPair,mul_comm]⟩
  have split : (r:ℂ)+(2:ℂ)*(n:ℂ) = (x:ℂ) := by dsimp [r]; push_cast; ring
  have hrq : π r = q := by
    have h := periodTorusProjection_add_lattice L (r:ℂ) _ period
    rw [split] at h
    exact h.symm.trans hx
  have nz : r ≠ 0 := by
    intro eq
    apply finite
    simpa [π,eq,periodTorusProjection] using hrq.symm
  have no : r ≠ 1 := by
    intro eq
    apply offCross
    simpa [π,eq] using hrq.symm
  have chooseSign : ∃ a k : ℝ, a ∈ Ioo (0:ℝ) 1 ∧ (k = 1 ∨ k = -1) ∧ π ((k:ℂ)*a) = q := by
    by_cases smallR : r < 1
    · exact ⟨r,1,⟨lt_of_le_of_ne nonneg nz.symm,smallR⟩,Or.inl rfl,by simpa using hrq⟩
    · have above : 1 < r := lt_of_le_of_ne (le_of_not_gt smallR) no.symm
      refine ⟨2-r,-1,⟨by linarith,by linarith⟩,Or.inr rfl,?_⟩
      have two : (2:ℂ) ∈ L.lattice := L.ω₁_mem_lattice
      calc
        π (((-1:ℝ):ℂ)*((2-r:ℝ):ℂ)) = π ((r:ℂ)-2) := congrArg π (by push_cast; ring)
        _ = π (((r:ℂ)-2)+2) := (periodTorusProjection_add_lattice L _ _ two).symm
        _ = q := by rw [sub_add_cancel]; exact hrq
  obtain ⟨a,k,ha,sign,atPoint⟩ := chooseSign
  obtain ⟨e,holo,coord,origin,cross,commH,commV⟩ := marked_signed_coordinate ht sign
  have image := (coord (a:ℂ)).trans atPoint
  have negImage : e (π (-(a:ℂ))) = -q := by
    rw [coord,mul_neg]
    exact congrArg Neg.neg atPoint
  exact ⟨a,k,e,ha,sign,holo,coord,origin,cross,commH,commV,image,negImage,
    (congrArg G image).trans zeroAt,(congrArg G negImage).trans poleAt⟩

/-- Formula (unnumbered, Section 3.2) as equalities on the Riemann sphere.
The map being evaluated is the descended original Gauss map. Only its
domain marking changes by the identity or complex negation. -/
theorem manuscript_signed_torus_gauss_points {t : ℝ} (ht : 0 < t)
    {p : ℂ → Fin 3 → ℂ} (hp : TwoAxisNullDifferential (rhombicPeriodPair t ht) p)
    {K u : ℂ} (hK : K ≠ 0)
    (height : ∀ z ∉ (rhombicPeriodPair t ht).lattice,
      p z 2 = K*((rhombicPeriodPair t ht).weierstrassP z-u)) :
    let L := rhombicPeriodPair t ht
    let π := periodTorusProjection L
    let G := periodTorusLift L (sphericalNullGauss ∘ p)
      (fun z ω hω => congrArg sphericalNullGauss (hp.periodic z ω hω))
    ∃ (a k : ℝ) (e : PeriodTorus L ≃ₜ PeriodTorus L), a ∈ Ioo (0:ℝ) 1 ∧
      (k = 1 ∨ k = -1) ∧ TorusHolomorphic L L e ∧
      (∀ z : ℂ, e (π z) = π ((k:ℂ)*z)) ∧ e (π 0) = π 0 ∧ e (π 1) = π 1 ∧
      Function.Commute e (rhombicHorizontalReflection ht) ∧
      Function.Commute e (rhombicVerticalReflection ht) ∧
      G (e (π a)) = (↑(0:ℂ) : OnePoint ℂ) ∧ G (e (π (-(a:ℂ)))) = ∞ := by
  intro L π G
  obtain ⟨a,ha,hzero⟩ := symmetric_height_has_normalized_real_zero ht hp hK height
  have han : (a:ℂ) ∉ L.lattice := real_not_mem_rhombic_lattice_of_pos ht ha.1 (by linarith [ha.2])
  have zeroNeg : p (-(a:ℂ)) 2 = 0 := (congrFun (hp.neg a han) 2).trans hzero
  have swap := null_horizontal_minus_neg hp han
  have values : ∃ k : ℝ, (k = 1 ∨ k = -1) ∧
      sphericalNullGauss (p ((k:ℂ)*a)) = (↑(0:ℂ) : OnePoint ℂ) ∧
      sphericalNullGauss (p ((k:ℂ)*(-(a:ℂ)))) = ∞ := by
    rcases null_horizontal_not_both_zero (hp.null a han) (hp.regular a han) with hm | hp'
    · have product := null_horizontal_product (hp.null a han)
      rw [hzero,zero_pow (by decide : 2 ≠ 0),neg_zero] at product
      have plusZero := (mul_eq_zero.mp product).resolve_left hm
      exact ⟨1,Or.inl rfl,by simp [sphericalNullGauss,hm,nullGauss,hzero],
        by simp [sphericalNullGauss,swap,plusZero]⟩
    · have product := null_horizontal_product (hp.null a han)
      rw [hzero,zero_pow (by decide : 2 ≠ 0),neg_zero] at product
      have minusZero := (mul_eq_zero.mp product).resolve_right hp'
      exact ⟨-1,Or.inr rfl,by simp [sphericalNullGauss,swap,hp',nullGauss,zeroNeg],
        by simp [sphericalNullGauss,minusZero]⟩
  obtain ⟨k,sign,hpos,hneg⟩ := values
  obtain ⟨e,holo,coord,origin,cross,commH,commV⟩ := marked_signed_coordinate ht sign
  refine ⟨a,k,e,ha,sign,holo,coord,origin,cross,commH,commV,?_,?_⟩
  · rw [coord]
    exact hpos
  · rw [coord]
    exact hneg

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.manuscript_punctured_schwarz_axes
#print axioms TwoAxisHelicoid.manuscript_real_fixed_divisor_orientation
#print axioms TwoAxisHelicoid.manuscript_signed_torus_gauss_points
