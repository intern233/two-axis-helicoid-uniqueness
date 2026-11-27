import TwoAxisHelicoid.PdfVerticalRowSound
import TwoAxisHelicoid.VerticalBranchContinuity

namespace TwoAxisHelicoid.PdfVertical
open CertificateData CertificateSemantics Set

private theorem reported_signs (dual : Bool) {t a : ℝ} (ht : 0<t) :
    (0<reportedVertical dual t a ↔ 0<(thetaG t a).re) ∧
    (reportedVertical dual t a<0 ↔ (thetaG t a).re<0) := by
  have pos : 0<Real.pi^2*Real.exp (-Real.pi/(2*t))/t^2 := by positivity
  cases dual <;> simp [reportedVertical,div_pos_iff_of_pos_right pos,div_neg_iff,pos,not_lt.mpr pos.le]

private theorem partition_endpoints {lo hi : ℚ} {rows : List Interval} (h : Partition lo hi rows) :
    lo≤hi ∧ ∀ r∈rows, lo≤r.lower ∧ r.upper≤hi := by
  induction rows generalizing lo with
  | nil => exact ⟨le_of_eq h,by simp⟩
  | cons r rs ih =>
    obtain ⟨rfl,lt,tail⟩ := h
    obtain ⟨bound,rest⟩ := ih tail
    refine ⟨lt.le.trans bound,?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨le_rfl,bound⟩
    · exact ⟨lt.le.trans (rest s hs).1,(rest s hs).2⟩

theorem vertical_branches_of_verified_rows {b : Bool} {m lo hi : ℚ}
    {rows : List (CheckedSignRow b m)} (part : Partition lo hi (rows.map (fun r => r.t)))
    (lt : 0<lo) (ut : hi≤7/5) (sound : ∀ r∈rows,(originalKey r.toSignRow).Sound) :
    ∀ r∈rows, ∀ t : ℝ, RealMem r.t t → (r.a.lower:ℝ)<verticalA t ∧ verticalA t<(r.a.upper:ℝ) := by
  intro r hr t ht
  obtain ⟨l,u⟩ := (partition_endpoints part).2 _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
  have htp : 0<t := (Rat.cast_pos.mpr (lt.trans_le l)).trans_le ht.1
  have htu : t<ellipticVerticalUpper := by
    apply (ht.2.trans (Rat.cast_le.mpr (u.trans ut))).trans_lt
    push_cast
    exact lt_trans (by norm_num) ellipticVerticalUpper_location.1
  obtain ⟨ab,zero⟩ := verticalA_spec ⟨htp,htu⟩
  have zr : (thetaG t (verticalA t)).re=0 := by rw [zero];rfl
  obtain ⟨low,high⟩ := sound r hr t ht.1 ht.2
  obtain ⟨_,_,a0,a01,a1,lpos,_,_,uneg,_⟩ := r.verified
  let d := decide (r.t.upper<3/5)
  have gl : 0<(thetaG t r.a.lower).re := (reported_signs d htp).1.mp ((Rat.cast_pos.mpr lpos).trans_le low.1)
  have gh : (thetaG t r.a.upper).re<0 := (reported_signs d htp).2.mp (high.2.trans_lt (by exact_mod_cast uneg))
  have al : (r.a.lower:ℝ)∈Ioo (0:ℝ) 1 := ⟨by exact_mod_cast a0,by exact_mod_cast a01.trans a1⟩
  have au : (r.a.upper:ℝ)∈Ioo (0:ℝ) 1 := ⟨by exact_mod_cast a0.trans a01,by exact_mod_cast a1⟩
  have anti := (thetaG_strictAnti_unit_of_pos htp).antitoneOn
  constructor
  · by_contra h
    have le := anti ab al (le_of_not_gt h)
    change (thetaG t r.a.lower).re≤(thetaG t (verticalA t)).re at le
    linarith
  · by_contra h
    have le := anti au ab (le_of_not_gt h)
    change (thetaG t (verticalA t)).re≤(thetaG t r.a.upper).re at le
    linarith

end TwoAxisHelicoid.PdfVertical
#print axioms TwoAxisHelicoid.PdfVertical.vertical_branches_of_verified_rows
