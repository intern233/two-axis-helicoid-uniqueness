import TwoAxisHelicoid.PuncturedTorusGeneratorLoops
import TwoAxisHelicoid.WeierstrassSpinCover
import TwoAxisHelicoid.SpinCoverDeck

namespace TwoAxisHelicoid
open Complex Set Topology

noncomputable def periodGeneratorPeriod (L : PeriodPair) (i : Fin 2) : L.lattice :=
  L.latticeEquivProd.symm (if i = 0 then (1,0) else (0,1))

theorem periodGeneratorPeriod_val (L : PeriodPair) (i : Fin 2) :
    (periodGeneratorPeriod L i).1 = L.basis i := by
  fin_cases i <;> simp [periodGeneratorPeriod,L.latticeEquiv_symm_apply]

theorem latticeSpinParity_generator (L : PeriodPair) (m : ℤ) (i : Fin 2) :
    latticeSpinParity L m (periodGeneratorPeriod L i) = if i = 0 then 0 else (m : ZMod 2) := by
  fin_cases i <;> simp [periodGeneratorPeriod,latticeSpinParity_coordinates]

/-- The actual quaternion lifts along the two closed generator curves. -/
noncomputable def weierstrassGeneratorLift {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) (i : Fin 2) :
    ℝ → UnitQuaternion :=
  unitSpinorQuaternionHomeomorph ∘ weierstrassUnitLift ht ha m hC ∘
    puncturedBasisLine (rhombicPeriodPair t ht) i

theorem weierstrassGeneratorLift_continuous {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) (i : Fin 2) :
    Continuous (weierstrassGeneratorLift ht ha m hC i) :=
  unitSpinorQuaternionHomeomorph.continuous.comp
    ((weierstrassUnitLift_continuous ht ha m hC).comp
      (puncturedBasisLine_continuous _ i))

theorem weierstrassGeneratorLift_frame {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) (i : Fin 2)
    (s : unitInterval) :
    unitQuaternionFrame (weierstrassGeneratorLift ht ha m hC i s) =
      weierstrassTorusFrame ht ha m hC (puncturedTorusGeneratorLoop _ i s) := by
  rw [show puncturedTorusGeneratorLoop (rhombicPeriodPair t ht) i s =
    puncturedPlaneProjection _ (puncturedBasisLine _ i s) from rfl,
    weierstrassTorusFrame_projection]
  exact unitQuaternionFrame_spinor _

theorem weierstrassGeneratorLift_add_one {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) (i : Fin 2) (s : ℝ) :
    weierstrassGeneratorLift ht ha m hC i (s+1) =
      if (if i = 0 then (0 : ZMod 2) else m) = 0
      then weierstrassGeneratorLift ht ha m hC i s
      else unitQuaternionAntipode (weierstrassGeneratorLift ht ha m hC i s) := by
  let L := rhombicPeriodPair t ht
  have hval : (puncturedBasisLine L i (s+1)).1 =
      (puncturedBasisLine L i s).1+(periodGeneratorPeriod L i).1 := by
    rw [periodGeneratorPeriod_val]
    exact periodBasisLine_add_one L i s
  have he := weierstrassUnitLift_equivariant ht ha m hC (periodGeneratorPeriod L i)
    (puncturedBasisLine L i s) (puncturedBasisLine L i (s+1)) hval
  rw [latticeSpinParity_generator] at he
  dsimp only [weierstrassGeneratorLift,Function.comp_apply]
  rw [he]
  rcases zmod_two_cases (if i = 0 then (0 : ZMod 2) else m) with h | h
  · rw [h,ite_eq_left rfl,zero_vadd]
  · rw [h,ite_eq_right one_ne_zero,unitSpinor_vadd_one,unitQuaternionAntipode_spinor]

/-- The first generator always has a closed spin lift. The second has a
closed lift precisely for even m and otherwise ends at the antipode. -/
theorem weierstrassGeneratorLift_endpoints {t a : ℝ} (ht : 0 < t)
    (ha : a ∈ Ioo (0 : ℝ) 1) (m : ℤ) {C : ℂ} (hC : C ≠ 0) :
    weierstrassGeneratorLift ht ha m hC 0 1 = weierstrassGeneratorLift ht ha m hC 0 0 ∧
    weierstrassGeneratorLift ht ha m hC 1 1 =
      if Even m then weierstrassGeneratorLift ht ha m hC 1 0
      else unitQuaternionAntipode (weierstrassGeneratorLift ht ha m hC 1 0) := by
  constructor
  · simpa using weierstrassGeneratorLift_add_one ht ha m hC 0 0
  · simpa only [zero_add,show (1 : Fin 2) ≠ 0 from by decide,ite_false,
      ZMod.intCast_eq_zero_iff_even] using weierstrassGeneratorLift_add_one ht ha m hC 1 0

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.weierstrassGeneratorLift_frame
#print axioms TwoAxisHelicoid.weierstrassGeneratorLift_endpoints
