import TwoAxisHelicoid.SlopingDisplacementBounds
import TwoAxisHelicoid.TraceDataCentralDisplacementCover
import TwoAxisHelicoid.CentralHalfPeriodSpatialSeparation
import TwoAxisHelicoid.CertifiedGlobalImmersion

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

/-- Signed transverse displacement, evaluated at the actual half period
of any closed normalized model in the certified root rectangle. -/
theorem central_half_period_displacement {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hp : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 hp)
    (per : ∀ z p, p∈(rhombicPeriodPair t hp).lattice → X (z+p)=X z) :
    X ((1+I*t)/2) 1-X 1 1 ∈ Icc (4743/8192:ℝ) (39705/16384) := by
  let p : ℂ := (1+I*t)/2
  let L := rhombicPeriodPair t hp
  have checked := TraceData.central_half_period_displacement_cover
  have disp := checked.sound ht ha (fun s hs => sloping_transverse_spatial_derivative hp d (s:=s) hs)
  have at0 : originalPeriodPath t (0:ℝ) = -1 := by simp [originalPeriodPath]
  have at1 : originalPeriodPath t (1:ℝ) = -p := by dsimp [p,originalPeriodPath]; ring
  have ea := per (-p) (1+I*t) L.ω₂_mem_lattice
  rw [show -p+(1+I*t)=p by dsimp [p]; ring] at ea
  have eb := per (-1) 2 L.ω₁_mem_lattice
  rw [show (-1:ℂ)+2=1 by norm_num] at eb
  simp only [div_one,Rat.cast_zero,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat,at0,at1,← ea,← eb] at disp
  exact disp

/-- The two central half-periods are separated in three-space in the
transverse direction by more than one unit. The crossing of the axes
lies strictly between them. -/
theorem closed_central_half_periods_separated {t a : ℝ} (ht : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ha : a∈Icc (rootALower:ℝ) rootAUpper) (hp : 0<t) {X : ℂ → Fin 3 → ℝ}
    (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 hp)
    (per : ∀ z p, p∈(rhombicPeriodPair t hp).lattice → X (z+p)=X z) :
    let p : ℂ := (1+I*t)/2
    let q : ℂ := -conj p
    1/2<X p 1-X 1 1 ∧ 1/2<X 1 1-X q 1 ∧ 1<X p 1-X q 1 ∧
      X p≠X q ∧ X p≠X 1 ∧ X q≠X 1 := by
  intro p q
  have bd := central_half_period_displacement ht ha hp d per
  have certified : (1/2:ℝ)<X p 1-X 1 1 := (by norm_num : (1/2:ℝ)<4743/8192).trans_le bd.1
  have sq := congrFun (central_half_period_spatial_test hp d per).2.2.2.2.1 1
  change X q 1-X 1 1= -(X p 1-X 1 1) at sq
  refine ⟨certified,by linarith,by linarith,?_,?_,?_⟩
  all_goals intro eq; have := congrFun eq 1; linarith

theorem certified_central_half_periods_separated :
    let p := certifiedClosedParameters
    let X := actualGlobalImmersion p.t p.a 1 p.height_pos
    let z : ℂ := (1+I*p.t)/2
    1/2<X z 1-X 1 1 ∧ 1/2<X 1 1-X (-conj z) 1 ∧ 1<X z 1-X (-conj z) 1 ∧
      X z≠X (-conj z) ∧ X z≠X 1 ∧ X (-conj z)≠X 1 := by
  intro p X z
  obtain ⟨t,a⟩ := certifiedClosedParameters_bounds
  have geom := actual_global_conformal_harmonic_immersion p.height_pos p.abscissa_mem (one_ne_zero : (1:ℝ)≠0)
    p.vertical_closed p.horizontal_closed
  exact closed_central_half_periods_separated (Ioo_subset_Icc_self t) (Ioo_subset_Icc_self a)
    p.height_pos (fun w hw => (geom.2.2.2 w hw).1)
    (actualGlobalImmersion_add_lattice p.height_pos p.abscissa_mem one_ne_zero p.vertical_closed p.horizontal_closed)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.certified_central_half_periods_separated
