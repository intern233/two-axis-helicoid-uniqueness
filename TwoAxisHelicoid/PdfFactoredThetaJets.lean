import TwoAxisHelicoid.PdfFactoredThetaWaves

namespace TwoAxisHelicoid.PdfVertical
open Complex
open scoped ComplexConjugate

def waveJetScale (n : ℕ) (j : Fin 5) : ℚ :=
  (if n%4<2 then 1 else -1)*(2*n+1:ℚ)^(j:ℕ)/2

def waveJetPair (j : Fin 5) (p m : CGrid) : CGrid :=
  match j.val with
  | 0 => (p.sub m).rot.neg
  | 1 => p.add m
  | 2 => (p.sub m).rot
  | 3 => (p.add m).neg
  | _ => (p.sub m).rot.neg

noncomputable def wavePairValue (j : Fin 5) (p m : ℂ) : ℂ :=
  match j.val with
  | 0 => -((p-m)*I)
  | 1 => p+m
  | 2 => (p-m)*I
  | 3 => -(p+m)
  | _ => -((p-m)*I)

theorem waveJetPair_sound (j : Fin 5) {P M : CGrid} {p m : ℂ}
    (hp : P.Contains p) (hm : M.Contains m) : (waveJetPair j P M).Contains (wavePairValue j p m) := by
  have d := CGrid.contains_rot (CGrid.contains_sub hp hm)
  have s := CGrid.contains_add hp hm
  fin_cases j <;> first | exact CGrid.contains_neg d | exact s | exact d | exact CGrid.contains_neg s

def factoredJetTerm (n : ℕ) (j : Fin 5) (p : FactoredFrequency) (node : CGrid) (s : Bool) : CGrid :=
  let w := p.waves node s
  (waveJetPair j w.1 w.2).scale (Grid.ofRats (waveJetScale n j) (waveJetScale n j))

theorem factoredJetTerm_sound {p : FactoredFrequency} {node : CGrid} {n : ℕ} {t a x : ℝ}
    (gp : p.Sound t a n) (gq : node.Contains (wavePhase n x)) (j : Fin 5) (s : Bool) :
    (factoredJetTerm n j p node s).Contains (thetaTerm t j n (sampleThetaArgument t a x s)) := by
  obtain ⟨up,dn⟩ := p.waves_sound gp gq s
  have sc : (Grid.ofRats (waveJetScale n j) (waveJetScale n j)).Contains (waveJetScale n j:ℝ) :=
    Grid.contains_rats le_rfl le_rfl
  have b := CGrid.contains_scale sc (waveJetPair_sound j up dn)
  obtain ⟨ep,em⟩ := factored_frequency_identities t a x n s
  rw [ep,em] at b
  let v := sampleThetaArgument t a x s
  let w : ℂ := Real.exp (-Real.pi*t*n*(n+1)/2)
  have value : thetaTerm t j n v=((waveJetScale n j:ℝ):ℂ)*wavePairValue j
      (w*Complex.exp ((2*n+1:ℂ)*v*I)) (w*Complex.exp (-((2*n+1:ℂ)*v)*I)) := by
    fin_cases j <;> by_cases hs : n%4<2 <;>
      simp [w,thetaTerm,sineJet,thetaSign,waveJetScale,wavePairValue,hs,Complex.I_sq] <;>
      field_simp <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring
  change (factoredJetTerm n j p node s).Contains (thetaTerm t j n v)
  rw [value]
  exact b

def factoredJet (p : Fin 6 → FactoredFrequency) (node : Fin 6 → CGrid) (j : Fin 5) (s : Bool) : CGrid :=
  (CGrid.finiteSum 6 (fun n => factoredJetTerm n j (p n) (node n) s)).widen (2^55)

theorem factoredJet_sound {p : Fin 6 → FactoredFrequency} {node : Fin 6 → CGrid}
    {t a x : ℝ} (gp : ∀ n : Fin 6, (p n).Sound t a n) (gn : ∀ n : Fin 6, (node n).Contains (wavePhase n x))
    (j : Fin 5) (s : Bool) (ht : 17/20≤t) (strip : |(sampleThetaArgument t a x s).im|≤2) :
    (factoredJet p node j s).Contains (thetaJet t j (sampleThetaArgument t a x s)) := by
  have sum := CGrid.contains_finiteSum (fun n => factoredJetTerm_sound (gp n) (gn n) j s)
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => thetaTerm t j n (sampleThetaArgument t a x s)) 6] at sum
  change CGrid.Contains _ (thetaPartial t j 6 (sampleThetaArgument t a x s)) at sum
  have tail := pdf_primal_six_term_tail ht j strip
  apply CGrid.contains_widen sum
  · have re := (Complex.abs_re_le_norm _).trans tail
    rw [Complex.sub_re] at re
    rw [abs_mul,abs_of_pos Grid.real_denom_pos]
    norm_num only [Grid.denom,Int.cast_pow,Int.cast_ofNat]
    linarith
  · have im := (Complex.abs_im_le_norm _).trans tail
    rw [Complex.sub_im] at im
    rw [abs_mul,abs_of_pos Grid.real_denom_pos]
    norm_num only [Grid.denom,Int.cast_pow,Int.cast_ofNat]
    linarith

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.factoredJet_sound

