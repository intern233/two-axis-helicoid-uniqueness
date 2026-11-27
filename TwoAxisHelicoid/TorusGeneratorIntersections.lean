import TwoAxisHelicoid.PuncturedTorusGeneratorLoops
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace TwoAxisHelicoid
open Complex Set

theorem real_integer_between_neg_one_one {x : ℝ}
    (hx : -1 < x) (hx' : x < 1) (hn : ∃ n : ℤ, x = n) : x = 0 := by
  obtain ⟨n,rfl⟩ := hn
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast hx
  have hnhi : n < (1 : ℤ) := by exact_mod_cast hx'
  have hn : n = 0 := by omega
  simp [hn]

theorem puncturedBasisLine_equal_coordinate (L : PeriodPair) (i k j : Fin 2) {s r : ℝ}
    (he : puncturedPlaneProjection L (puncturedBasisLine L i s) =
      puncturedPlaneProjection L (puncturedBasisLine L k r)) :
    ∃ n : ℤ, (if i = j then s else 0)-(if k = j then r else 0) = (n : ℝ) := by
  have hm := (puncturedPlaneProjection_eq_iff L _ _).mp he
  obtain ⟨n,hn⟩ := periodPair_lattice_coordinate L hm j
  change L.basis.repr (periodBasisLine L i s-periodBasisLine L k r) j = (n : ℝ) at hn
  rw [map_sub,Finsupp.sub_apply,periodBasisLine_coordinates,periodBasisLine_coordinates] at hn
  exact ⟨n,by linarith⟩

/-- Each marked generator is simple on its half-open period interval. -/
theorem puncturedBasisLine_projection_injOn (L : PeriodPair) (i : Fin 2) :
    InjOn (puncturedPlaneProjection L ∘ puncturedBasisLine L i) (Ico (0 : ℝ) 1) := by
  intro s hs r hr he
  have hn := puncturedBasisLine_equal_coordinate L i i i he
  simp only [ite_true] at hn
  have hz := real_integer_between_neg_one_one (x := s-r)
    (by linarith [hs.1,hr.2]) (by linarith [hs.2,hr.1]) hn
  linarith

/-- The two actual generator curves meet only at their common basepoint
when parametrized on a half-open period interval. -/
theorem puncturedBasisLines_intersection (L : PeriodPair) {s r : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (hr : r ∈ Ico (0 : ℝ) 1)
    (he : puncturedPlaneProjection L (puncturedBasisLine L 0 s) =
      puncturedPlaneProjection L (puncturedBasisLine L 1 r)) : s = 0 ∧ r = 0 := by
  have hn := puncturedBasisLine_equal_coordinate L 0 1 0 he
  have hm := puncturedBasisLine_equal_coordinate L 0 1 1 he
  norm_num only [Fin.reduceEq,ite_true,ite_false,sub_zero,zero_sub] at hn hm
  have hz := real_integer_between_neg_one_one (x := s) (by linarith [hs.1]) hs.2 hn
  have hz' := real_integer_between_neg_one_one (x := -r) (by linarith [hr.2])
    (by linarith [hr.1]) hm
  exact ⟨hz,by linarith⟩

theorem periodBasisLine_hasDerivAt (L : PeriodPair) (i : Fin 2) (s : ℝ) :
    HasDerivAt (periodBasisLine L i) (L.basis i) s := by
  simpa only [periodBasisLine,one_smul,id_eq] using!
    ((hasDerivAt_id s).smul_const (L.basis i)).const_add (periodPairCenter L)

/-- Injectivity of an actual surface differential makes the two generator
velocities linearly independent at their intersection. -/
theorem immersion_generator_velocities_independent (L : PeriodPair)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : ℂ →L[ℝ] E) (hD : Function.Injective D) :
    LinearIndependent ℝ (fun i : Fin 2 => D (L.basis i)) :=
  L.basis.linearIndependent.map' D.toLinearMap (LinearMap.ker_eq_bot.mpr hD)

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.puncturedBasisLine_projection_injOn
#print axioms TwoAxisHelicoid.puncturedBasisLines_intersection
#print axioms TwoAxisHelicoid.immersion_generator_velocities_independent
