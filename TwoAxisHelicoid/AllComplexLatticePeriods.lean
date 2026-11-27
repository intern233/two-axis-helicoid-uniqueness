import TwoAxisHelicoid.LatticeComplexPeriodCharacter
import TwoAxisHelicoid.TorusIntegralCoherentLift
import TwoAxisHelicoid.LopezRosVerticalFluxPrimitives
import TwoAxisHelicoid.CoordinateDataSymmetry

namespace TwoAxisHelicoid
open Complex Set

theorem PiecewiseComplexPath.integral_eq_primitive_sub {Ω : Set ℂ} {x y : ℂ}
    (p : PiecewiseComplexPath Ω x y) {f F : ℂ → ℂ} (hf : ContinuousOn f Ω)
    (d : ∀ z∈Ω, HasDerivAt F (f z) z) : p.integral f=F y-F x := by
  induction p with
  | refl => simp [PiecewiseComplexPath.integral]
  | arc a => exact a.integral_eq_primitive_sub hf d
  | trans p q hp hq => simp only [PiecewiseComplexPath.integral,hp,hq]; abel

/-- At each base point, the complete set of complex path periods is
exactly the image of the primitive's translation character. Both
inclusions use actual piecewise smooth paths on the punctured torus. -/
theorem torus_complex_loop_integral_iff_character {t : ℝ} (ht : 0<t) {f F : ℂ → ℂ}
    (an : ∀ z∉(rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (d : ∀ z∉(rhombicPeriodPair t ht).lattice, HasDerivAt F (f z) z)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → f (z+ω)=f z)
    {χ : (rhombicPeriodPair t ht).lattice →+ ℂ}
    (mon : ∀ z∉(rhombicPeriodPair t ht).lattice, ∀ w : (rhombicPeriodPair t ht).lattice, F (z+w)-F z=χ w)
    (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) (v : ℂ) :
    (∃ γ : Path q q, TorusPathIntegral (rhombicPeriodPair t ht) f γ v) ↔ v∈range χ := by
  let L := rhombicPeriodPair t ht
  obtain ⟨x,hx⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) q.1
  have off : x∉L.lattice := fun h => q.2 (hx.symm.trans ((periodTorusProjection_eq_zero L x).mpr h))
  have cf : ContinuousOn f (L.lattice : Set ℂ)ᶜ := fun z hz => (an _ hz).continuousAt.continuousWithinAt
  constructor
  · rintro ⟨γ,h⟩
    obtain ⟨y,hy,p,value⟩ := h.coherent_lift per x hx
    let w : L.lattice := ⟨y-x,(periodTorusProjection_eq_iff L x y).mp (hx.trans hy.symm)⟩
    have shifted : x+(w:ℂ)=y := by change x+(y-x)=y; ring
    refine ⟨w,?_⟩
    rw [← mon x off w,shifted,← p.integral_eq_primitive_sub cf d,value]
  · rintro ⟨w,rfl⟩
    have regular : x+(w:ℂ)∉L.lattice := fun h => off (by simpa using L.lattice.sub_mem h w.2)
    obtain ⟨polygon⟩ := planePolygon_exists L.isClosed_lattice.isOpen_compl
      (rhombic_punctured_plane_isConnected ht).2 off regular
    obtain ⟨p,_⟩ := polygon.exists_piecewise_integral
    obtain ⟨ha,hb,γ,hγ⟩ := p.projected_hasIntegral f
    have fromQ : q=puncturedPlaneProjection L ⟨x,ha⟩ := Subtype.ext hx.symm
    have toQ : q=puncturedPlaneProjection L ⟨x+w,hb⟩ :=
      Subtype.ext ((periodTorusProjection_add_lattice L x w w.2).trans hx).symm
    refine ⟨γ.cast fromQ toQ,?_⟩
    rw [← mon x off w,← p.integral_eq_primitive_sub cf d]
    exact hγ.cast fromQ toQ

/-- The two primitive sloping periods generate the complete complex
period group, without requiring the real or vertical periods to close. -/
theorem periodic_coefficient_all_complex_loop_integrals {t : ℝ} (ht : 0<t) {f : ℂ → ℂ}
    (an : ∀ z∉(rhombicPeriodPair t ht).lattice, AnalyticAt ℂ f z)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → f (z+ω)=f z)
    (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) (v : ℂ) :
    (∃ γ : Path q q, TorusPathIntegral (rhombicPeriodPair t ht) f γ v) ↔
      ∃ m n : ℤ, v=(m:ℂ)*rhombicDownPeriod t f+(n:ℂ)*rhombicUpPeriod t f := by
  let L := rhombicPeriodPair t ht
  obtain ⟨F,d⟩ := periodic_coefficient_unrestricted_complex_primitive ht an per
  obtain ⟨χ,mon⟩ := complex_primitive_lattice_character ht d per
  obtain ⟨down,up,ed,eu,cd,cu⟩ := complex_character_generator_values ht an d mon
  rw [torus_complex_loop_integral_iff_character ht an d per mon q v]
  have eval (m n : ℤ) : χ (m • down+n • up)=(m:ℂ)*rhombicDownPeriod t f+(n:ℂ)*rhombicUpPeriod t f := by
    rw [map_add,map_zsmul,map_zsmul,cd,cu,zsmul_eq_mul,zsmul_eq_mul]
  constructor
  · rintro ⟨w,rfl⟩
    obtain ⟨m,n,h⟩ := PeriodPair.mem_lattice.mp w.2
    have basis : m • down+(m+n) • up=w := by
      apply Subtype.ext
      change (m • (down:ℂ))+(m+n) • (up:ℂ)=(w:ℂ)
      rw [ed,eu,zsmul_eq_mul,zsmul_eq_mul,← h,Int.cast_add]
      change _= (m:ℂ)*2+(n:ℂ)*(1+I*t)
      ring
    exact ⟨m,m+n,basis ▸ eval m (m+n)⟩
  · rintro ⟨m,n,rfl⟩
    exact ⟨m • down+n • up,eval m n⟩

theorem original_horizontal_all_complex_loop_integrals {t : ℝ} (ht : 0<t) (a : ℝ)
    (q : PuncturedPeriodTorus (rhombicPeriodPair t ht)) (v : ℂ) :
    (∃ γ : Path q q, TorusPathIntegral (rhombicPeriodPair t ht) (thetaA t a) γ v) ↔
      ∃ m n : ℤ, v=(m:ℂ)*rhombicDownPeriod t (thetaA t a)+(n:ℂ)*rhombicUpPeriod t (thetaA t a) :=
  periodic_coefficient_all_complex_loop_integrals ht (fun _ hz => thetaA_analyticAt_off_lattice ht a hz)
    (fun z ω h => thetaA_add_lattice ht a z ⟨ω,h⟩) q v

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.periodic_coefficient_all_complex_loop_integrals
#print axioms TwoAxisHelicoid.original_horizontal_all_complex_loop_integrals
