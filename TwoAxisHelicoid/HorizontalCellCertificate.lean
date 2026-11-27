import TwoAxisHelicoid.ThetaCellIntegral

namespace TwoAxisHelicoid
open ComplexBall Metric

def horizontalCenterBall (cfg : BallConfig) (bt : ComplexBall) (x : ℚ) : ComplexBall :=
  roundedAdd cfg.prec (rational x) (roundedMul cfg.prec (point ⟨0, 1/2⟩) bt)

theorem horizontalCenterBall_contains {bt : ComplexBall} {t : ℝ}
    (ht : bt.Contains (t : ℂ)) (cfg : BallConfig) (x : ℚ) :
    (horizontalCenterBall cfg bt x).Contains ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) := by
  have hhalf : (point (⟨0, 1/2⟩ : QComplex)).Contains (Complex.I/2) := by
    convert point_contains (⟨0, 1/2⟩ : QComplex) using 1
    apply Complex.ext <;> norm_num [QComplex.val]
  convert roundedAdd_contains (rational_contains x) (roundedMul_contains hhalf ht cfg.prec) cfg.prec using 1
  · rfl
  · push_cast
    ring

def evalHorizontalCell (cfg : BallConfig) (N : ℕ)
    (tlo thi alo ahi x h R : ℚ) : Option ComplexBall :=
  let bt := realInterval tlo thi
  let ba := realInterval alo ahi
  (evalThetaACoefficient cfg N bt ba).bind (fun bc =>
    evalThetaCellIntegral cfg N bt ba bc (horizontalCenterBall cfg bt x) h R)

def certifiesHorizontalCell (cfg : BallConfig) (N : ℕ)
    (tlo thi alo ahi x h R : ℚ) (out : ComplexBall) : Prop :=
  0 < tlo ∧ match evalHorizontalCell cfg N tlo thi alo ahi x h R with
    | none => False
    | some b => out.coarsens b

instance (cfg : BallConfig) (N : ℕ) (tlo thi alo ahi x h R : ℚ) (out : ComplexBall) :
    Decidable (certifiesHorizontalCell cfg N tlo thi alo ahi x h R out) := by
  unfold certifiesHorizontalCell
  split <;> infer_instance

theorem evalHorizontalCell_sound (cfg : BallConfig) (N : ℕ)
    (tlo thi alo ahi x h R : ℚ) (htlo : 0 < tlo) {t a : ℝ}
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    Sound (evalHorizontalCell cfg N tlo thi alo ahi x h R)
      (normalizedIntegral (thetaA t a) ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (h : ℝ)) := by
  have htpos : 0 < t := (Rat.cast_pos.mpr htlo).trans_le htl
  have ht := realInterval_contains htl htu
  have ha := realInterval_contains hal hau
  apply bind_sound (evalThetaACoefficient_sound ht ha cfg N)
  intro bc hbc
  exact evalThetaCellIntegral_sound ht ha hbc (horizontalCenterBall_contains ht cfg x) htpos cfg N h R

theorem certified_horizontal_cell_contains (cfg : BallConfig) (N : ℕ)
    (tlo thi alo ahi x h R : ℚ) (out : ComplexBall)
    (hcheck : certifiesHorizontalCell cfg N tlo thi alo ahi x h R out) {t a : ℝ}
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    out.Contains (normalizedIntegral (thetaA t a)
      ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (h : ℝ)) := by
  have hs := evalHorizontalCell_sound cfg N tlo thi alo ahi x h R hcheck.1 htl htu hal hau
  have hh := hcheck.2
  cases he : evalHorizontalCell cfg N tlo thi alo ahi x h R with
  | none => simp [he] at hh
  | some b =>
    simp only [he] at hh
    exact coarsen_contains (hs b he) hh

theorem evalThetaCellIntegral_disk_success (cfg : BallConfig) (N : ℕ)
    (bt ba bc center : ComplexBall) (h R : ℚ) {out : ComplexBall}
    (he : evalThetaCellIntegral cfg N bt ba bc center h R = some out) :
    0 ≤ h ∧ h < R ∧ ∃ M, evalThetaDisk cfg N bt ba bc center R = some M := by
  unfold evalThetaCellIntegral at he
  split_ifs at he with hg
  · change (evalThetaDisk cfg N bt ba bc center R).bind _ = some out at he
    obtain ⟨M, hM, _⟩ := Option.bind_eq_some_iff.mp he
    exact ⟨hg.1, hg.2, M, hM⟩

theorem certified_horizontal_cell_holomorphic (cfg : BallConfig) (N : ℕ)
    (tlo thi alo ahi x h R : ℚ) (out : ComplexBall)
    (hcheck : certifiesHorizontalCell cfg N tlo thi alo ahi x h R out) {t a : ℝ}
    (htl : (tlo : ℝ) ≤ t) (htu : t ≤ (thi : ℝ))
    (hal : (alo : ℝ) ≤ a) (hau : a ≤ (ahi : ℝ)) :
    0 ≤ h ∧ h < R ∧ DiffContOnCl ℂ (thetaA t a)
      (ball ((x : ℂ)+Complex.I*((t/2 : ℝ) : ℂ)) (R : ℝ)) := by
  have htpos : 0 < t := (Rat.cast_pos.mpr hcheck.1).trans_le htl
  have ht := realInterval_contains htl htu
  have ha := realInterval_contains hal hau
  have hh := hcheck.2
  cases he : evalHorizontalCell cfg N tlo thi alo ahi x h R with
  | none => simp [he] at hh
  | some b =>
    obtain ⟨bc, hbc, hcell⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨hh0, hhR, M, hM⟩ := evalThetaCellIntegral_disk_success cfg N _ _ _ _ h R hcell
    exact ⟨hh0, hhR, evalThetaDisk_holomorphic ht ha
      (evalThetaACoefficient_sound ht ha cfg N bc hbc)
      (horizontalCenterBall_contains ht cfg x) htpos cfg N R hM⟩

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.certified_horizontal_cell_contains
