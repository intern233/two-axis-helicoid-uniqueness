import TwoAxisHelicoid.ActualComplexHeightStraightLift
import TwoAxisHelicoid.PeriodicSmoothFlow

namespace TwoAxisHelicoid
open Complex Set Topology

private theorem segment_min_abs {h h' : ℝ} (side : (0<h ∧ 0<h') ∨ (h<0 ∧ h'<0))
    {k : ℝ} (hk : k∈Icc (0:ℝ) 1) : min |h| |h'|≤|h+k*(h'-h)| := by
  let e := min |h| |h'|
  have l : e≤|h| := min_le_left _ _
  have r : e≤|h'| := min_le_right _ _
  rcases side with pos|neg
  · rw [abs_of_pos pos.1] at l
    rw [abs_of_pos pos.2] at r
    have left := mul_nonneg (sub_nonneg.mpr hk.2) (sub_nonneg.mpr l)
    have right := mul_nonneg hk.1 (sub_nonneg.mpr r)
    have z : e≤h+k*(h'-h) := by nlinarith only [left,right]
    exact z.trans (le_abs_self _)
  · rw [abs_of_neg neg.1] at l
    rw [abs_of_neg neg.2] at r
    have left := mul_nonneg (sub_nonneg.mpr hk.2) (sub_nonneg.mpr l)
    have right := mul_nonneg hk.1 (sub_nonneg.mpr r)
    have z : e≤ -(h+k*(h'-h)) := by nlinarith only [left,right]
    exact z.trans (neg_le_abs _)

/-- Between any two horizontal levels on the same side of the saddles,
translation by any compatible complex height increment lifts to a
lattice-equivariant homeomorphism, with an actual inverse and fixed
punctures. -/
theorem actual_regular_height_translation {t a c : ℝ} (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) (hc : c≠0)
    {X : ℂ → Fin 3 → ℝ} (diff : HasTwoAxisHelicoidCoordinateDifferential X t a c ht)
    (period : ∀ z w, w∈(rhombicPeriodPair t ht).lattice → X (z+w)=X z)
    {h h' : ℝ} (side : (0<h ∧ 0<h') ∨ (h<0 ∧ h'<0)) {b : ℂ} (realIncrement : b.re=h'-h) :
    let L := rhombicPeriodPair t ht
    let H := actualComplexHeight t a c ht
    ∃ F : ℂ ≃ₜ ℂ, (∀ z w, w∈L.lattice → F (z+w)=F z+w) ∧ (∀ z∈L.lattice,F z=z) ∧
      (∀ z∉L.lattice, X z 2=X 1 2+h → F z∉L.lattice ∧ H (F z)=H z+b ∧ X (F z) 2=X 1 2+h') ∧
      ∀ z∉L.lattice, X z 2=X 1 2+h' → F.symm z∉L.lattice ∧ H (F.symm z)=H z-b ∧ X (F.symm z) 2=X 1 2+h := by
  let L := rhombicPeriodPair t ht
  let ε := min |h| |h'|
  have positive : 0<ε := by
    rcases side with ps|ns
    · exact lt_min (abs_pos.mpr ps.1.ne') (abs_pos.mpr ps.2.ne')
    · exact lt_min (abs_pos.mpr ns.1.ne) (abs_pos.mpr ns.2.ne)
  obtain ⟨V,sm,per,fixed,lift⟩ := actual_complex_height_straight_lift ht ha hc diff period positive
  let W := fun z => b*V z
  obtain ⟨F,fp,stop,forward,back⟩ := periodic_smooth_field_homeomorph L (W := W)
    (contDiff_const.mul sm) (fun z w hw => congrArg (b*·) (per z w hw))
  have one : (1:ℝ)∈Icc 0 1 := right_mem_Icc.mpr zero_le_one
  refine ⟨F,fp,fun z hz => stop z (by simp [W,fixed z hz]),?_,?_⟩
  · intro z hz level
    have sep (k : ℝ) (hk : k∈Icc (0:ℝ) 1) : ε≤|X z 2-X 1 2+k*b.re| := by
      rw [level,add_sub_cancel_left,realIncrement]
      exact segment_min_abs side hk
    obtain ⟨γ,init,ode,he⟩ := lift z b hz sep
    have eq := forward γ ode
    rw [init] at eq
    obtain ⟨off,ch,v⟩ := he 1 one
    rw [eq]
    exact ⟨off,by simpa only [one_smul] using ch,by rw [v,one_mul,level,realIncrement]; ring⟩
  · intro z hz level
    have side' : (0<h' ∧ 0<h) ∨ (h'<0 ∧ h<0) := side.imp And.symm And.symm
    have sep (k : ℝ) (hk : k∈Icc (0:ℝ) 1) : ε≤|X z 2-X 1 2+k*(-b).re| := by
      rw [level,add_sub_cancel_left,Complex.neg_re,realIncrement,neg_sub]
      change min |h| |h'|≤_
      rw [min_comm |h| |h'|]
      exact segment_min_abs side' hk
    obtain ⟨γ,init,ode,he⟩ := lift z (-b) hz sep
    have eq := back γ (fun s hs => by simpa only [W,neg_mul] using ode s hs)
    rw [init] at eq
    obtain ⟨off,ch,v⟩ := he 1 one
    rw [eq]
    exact ⟨off,by simpa only [one_smul,sub_eq_add_neg] using ch,by rw [v,one_mul,level,Complex.neg_re,realIncrement]; ring⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.actual_regular_height_translation
