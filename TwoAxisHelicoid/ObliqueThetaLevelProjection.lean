import TwoAxisHelicoid.RotatedThetaLevelInjective
import TwoAxisHelicoid.ObliqueThetaEdgeSound
import TwoAxisHelicoid.ThetaDirectionReflections
import TwoAxisHelicoid.ExplicitMarkedReflections

namespace TwoAxisHelicoid
open Complex Set
open scoped ComplexConjugate

private theorem oblique_conjugate (b : Bool) (u : ℂ) :
    (obliqueThetaFactor b*conj u).re=(obliqueThetaFactor (!b)*u).re := by
  cases b <;> simp [obliqueThetaFactor,Complex.mul_re]

private theorem oblique_inverse (b : Bool) (u : ℂ) :
    (obliqueThetaFactor (!b)*u).re<0 → (obliqueThetaFactor b*u⁻¹).re<0 := by
  intro neg
  have nz : u≠0 := fun e => by simp [e] at neg
  have eq : (obliqueThetaFactor b*u⁻¹).re=(obliqueThetaFactor (!b)*u).re/normSq u := by
    cases b <;> simp [obliqueThetaFactor,Complex.mul_re,inv_re,inv_im] <;> ring
  rw [eq]
  exact div_neg_of_neg_of_pos neg (normSq_pos.mpr nz)

theorem oblique_torus_direction_from_tile {t a : ℝ} (ht : 0<t) (_ha : a∈Ioo (0:ℝ) 1)
    (_root : thetaG t a=0) {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    (tile : ∀ x∈Icc (0:ℝ) 1, ∀ y∈Icc 0 (t/2), let z : ℂ := ⟨x,y⟩
      ((1/4:ℝ)≤(actualComplexHeight t a 1 ht z).re → (obliqueThetaFactor true*centralPhaseThetaRatio t a z).re<0) ∧
      ((actualComplexHeight t a 1 ht z).re≤ -(1/4:ℝ) → (obliqueThetaFactor false*centralPhaseThetaRatio t a z).re<0)) :
    ∀ z∉(rhombicPeriodPair t ht).lattice,
      (1/4≤X z 2-X 1 2 → (obliqueThetaFactor true*torusThetaDirection t a z).re<0) ∧
      (X z 2-X 1 2≤ -(1/4) → (obliqueThetaFactor false*torusThetaDirection t a z).re<0) := by
  let L := rhombicPeriodPair t ht
  let T := torusThetaDirection t a
  let H := fun z => X z 2-X 1 2
  let P := fun z : ℂ => z∉L.lattice →
    (1/4≤H z → (obliqueThetaFactor true*T z).re<0) ∧ (H z≤ -(1/4) → (obliqueThetaFactor false*T z).re<0)
  have translate (z ω : ℂ) (m : ω∈L.lattice) (h : P z) : P (z+ω) := by
    intro off
    dsimp only [H,T]
    rw [per z ω m,torusThetaDirection_add_lattice ht a z m]
    exact h (fun k => off (L.lattice.add_mem k m))
  have turn (z : ℂ) (h : P z) : P (-z) := by
    intro off
    have reg : z∉L.lattice := fun k => off (L.lattice.neg_mem k)
    have eq : H (-z)= -(H z) := congrFun (explicit_centered_primitive_reflections ht d per z reg).1 2
    change (1/4≤H (-z) → (obliqueThetaFactor true*torusThetaDirection t a (-z)).re<0) ∧
      (H (-z)≤ -(1/4) → (obliqueThetaFactor false*torusThetaDirection t a (-z)).re<0)
    rw [eq,torusThetaDirection_neg]
    exact ⟨fun hi => oblique_inverse true _ ((h reg).2 (by linarith)),fun lo => oblique_inverse false _ ((h reg).1 (by linarith))⟩
  have mirror (z : ℂ) (h : P z) : P (conj z) := by
    intro off
    have reg : z∉L.lattice := fun k => off (rhombic_conj_mem ht k)
    have eq : H (conj z)= -(H z) := congrFun (explicit_centered_primitive_reflections ht d per z reg).2 2
    change (1/4≤H (conj z) → (obliqueThetaFactor true*torusThetaDirection t a (conj z)).re<0) ∧
      (H (conj z)≤ -(1/4) → (obliqueThetaFactor false*torusThetaDirection t a (conj z)).re<0)
    rw [eq,torusThetaDirection_conj,oblique_conjugate,oblique_conjugate]
    exact ⟨fun hi => (h reg).2 (by linarith),fun lo => (h reg).1 (by linarith)⟩
  have full := rhombic_reflection_half_rectangle ht P translate turn (fun z h => turn _ (mirror z h)) (by
    intro x hx y hy off
    let z : ℂ := (x:ℂ)+I*y
    have val : z=⟨x,y⟩ := by apply Complex.ext <;> simp [z]
    have height : H z=(actualComplexHeight t a 1 ht z).re := actual_complex_height_centered_primitive ht d off
    have condition := tile x hx y hy
    dsimp only at condition
    rw [← val,← height] at condition
    have reduce (b : Bool) (neg : (obliqueThetaFactor b*centralPhaseThetaRatio t a z).re<0) :
        (obliqueThetaFactor b*T z).re<0 := by
      rw [theta_ratio_torus_direction,mul_left_comm] at neg
      rw [Complex.re_ofReal_mul] at neg
      exact neg_of_mul_neg_right neg (Real.exp_pos _).le
    exact ⟨fun hi => reduce true (condition.1 hi),fun lo => reduce false (condition.2 lo)⟩)
  exact full

theorem oblique_torus_level_injectivity {t a : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (root : thetaG t a=0) {X : ℂ → Fin 3 → ℝ} (d : HasTwoAxisHelicoidCoordinateDifferential X t a 1 ht)
    (per : ∀ z ω, ω∈(rhombicPeriodPair t ht).lattice → X (z+ω)=X z)
    (tile : ∀ x∈Icc (0:ℝ) 1, ∀ y∈Icc 0 (t/2), let z : ℂ := ⟨x,y⟩
      ((1/4:ℝ)≤(actualComplexHeight t a 1 ht z).re → (obliqueThetaFactor true*centralPhaseThetaRatio t a z).re<0) ∧
      ((actualComplexHeight t a 1 ht z).re≤ -(1/4:ℝ) → (obliqueThetaFactor false*centralPhaseThetaRatio t a z).re<0)) :
    let L := rhombicPeriodPair t ht
    let Y := fun p : PuncturedPeriodTorus L => periodTorusLift L X per p.1
    ∀ h : ℝ, 1/4≤|h| → InjOn Y {u | Y u 2=X 1 2+h} := by
  intro L Y
  let H := fun z => X z 2-X 1 2
  have full := oblique_torus_direction_from_tile ht ha root d per tile
  intro h hi
  have nz : h≠0 := fun e => by norm_num [e] at hi
  by_cases hp : 0<h
  · rw [abs_of_pos hp] at hi
    apply height_level_injective_of_rotated_theta ht ha root nz d per (obliqueThetaFactor true)
    intro z off lev
    exact ((full z off).1 (by simpa [H,lev] using hi)).ne
  · rw [abs_of_nonpos (le_of_not_gt hp)] at hi
    apply height_level_injective_of_rotated_theta ht ha root nz d per (obliqueThetaFactor false)
    intro z off lev
    exact ((full z off).2 (by rw [lev]; linarith)).ne

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.oblique_torus_direction_from_tile
#print axioms TwoAxisHelicoid.oblique_torus_level_injectivity
