import TwoAxisHelicoid.SpinSquareFundamentalDomain
import TwoAxisHelicoid.EquivariantTorusFrame
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace TwoAxisHelicoid
open Complex Set Topology

noncomputable def normalizedPhase (s : ℝ) : Circle := Circle.exp (2*Real.pi*s)

theorem normalizedPhase_eq_iff (s t : ℝ) : normalizedPhase s = normalizedPhase t ↔ ∃ n : ℤ, s-t = (n:ℝ) := by
  have hk : 2*Real.pi ≠ 0 := by positivity
  rw [normalizedPhase,normalizedPhase,Circle.exp_eq_exp]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,mul_left_cancel₀ hk ?_⟩
    linear_combination hn
  · rintro ⟨n,hn⟩
    exact ⟨n,by linear_combination (2*Real.pi)*hn⟩

noncomputable def planeCircleCoordinates (L : PeriodPair) (z : ℂ) : Circle × Circle :=
  (normalizedPhase (L.basis.repr z 0),normalizedPhase (L.basis.repr z 1))

theorem planeCircleCoordinates_continuous (L : PeriodPair) : Continuous (planeCircleCoordinates L) := by
  have hc (i : Fin 2) : Continuous (fun z => L.basis.repr z i) := (L.basis.coord i).continuous_of_finiteDimensional
  have hp : Continuous normalizedPhase := Circle.exp.continuous.comp (continuous_const.mul continuous_id)
  exact (hp.comp (hc 0)).prodMk (hp.comp (hc 1))

theorem planeCircleCoordinates_eq_iff (L : PeriodPair) (z w : ℂ) :
    planeCircleCoordinates L z = planeCircleCoordinates L w ↔ periodTorusProjection L z = periodTorusProjection L w := by
  have he : periodTorusProjection L z = periodTorusProjection L w ↔ z-w ∈ L.lattice :=
    QuotientAddGroup.eq_iff_sub_mem
  rw [he,integral_period_coordinates_iff]
  constructor
  · intro h
    obtain ⟨m,hm⟩ := (normalizedPhase_eq_iff _ _).mp (congrArg Prod.fst h)
    obtain ⟨n,hn⟩ := (normalizedPhase_eq_iff _ _).mp (congrArg Prod.snd h)
    exact ⟨m,n,by simpa only [map_sub,Finsupp.sub_apply] using hm,by simpa only [map_sub,Finsupp.sub_apply] using hn⟩
  · rintro ⟨m,n,hm,hn⟩
    simp only [map_sub,Finsupp.sub_apply] at hm hn
    exact Prod.ext ((normalizedPhase_eq_iff _ _).mpr ⟨m,hm⟩) ((normalizedPhase_eq_iff _ _).mpr ⟨n,hn⟩)

theorem planeCircleCoordinates_surjective (L : PeriodPair) : Function.Surjective (planeCircleCoordinates L) := by
  rintro ⟨a,b⟩
  obtain ⟨s,hs⟩ := Circle.exp_surjective a
  obtain ⟨t,ht⟩ := Circle.exp_surjective b
  let k := 2*Real.pi
  have hk : k ≠ 0 := by dsimp [k]; positivity
  let z := spinSquareLinear L (s/k) (t/k)
  obtain ⟨hu,hv⟩ := spinSquareLinear_coords L (s/k) (t/k)
  have H (v : ℝ) : normalizedPhase (v/k) = Circle.exp v := by
    change Circle.exp (k*(v/k)) = Circle.exp v
    congr 1
    field_simp
  exact ⟨z,Prod.ext ((congrArg normalizedPhase hu).trans ((H s).trans hs)) ((congrArg normalizedPhase hv).trans ((H t).trans ht))⟩

/-- The actual marked lattice quotient is an ordinary topological torus,
as required when applying the unmarked regular-homotopy theorem. -/
theorem marked_torus_circle_product (L : PeriodPair) :
    ∃ H : PeriodTorus L ≃ₜ Circle × Circle, ∀ z, H (periodTorusProjection L z) = planeCircleCoordinates L z := by
  let π := periodTorusProjection L
  have hπ : IsQuotientMap π := QuotientAddGroup.isQuotientMap_mk _
  let h := quotientFiberDescend π hπ.surjective (planeCircleCoordinates L)
  have hf (x y : ℂ) (he : π x = π y) := (planeCircleCoordinates_eq_iff L x y).mpr he
  have he (x : ℂ) : h (π x) = planeCircleCoordinates L x := quotientFiberDescend_apply _ _ _ hf x
  have hc : Continuous h := quotientFiberDescend_continuous hπ _ hf (planeCircleCoordinates_continuous L)
  have hi : Function.Injective h := by
    intro a b hab
    obtain ⟨x,rfl⟩ := hπ.surjective a
    obtain ⟨y,rfl⟩ := hπ.surjective b
    exact (planeCircleCoordinates_eq_iff L x y).mp ((he x).symm.trans (hab.trans (he y)))
  have hsur : Function.Surjective h := by
    intro p
    obtain ⟨z,hz⟩ := planeCircleCoordinates_surjective L p
    exact ⟨π z,(he z).trans hz⟩
  exact ⟨(hc.isClosedEmbedding hi).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hsur.range_eq) |>.trans
    (Homeomorph.Set.univ _),he⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_torus_circle_product
