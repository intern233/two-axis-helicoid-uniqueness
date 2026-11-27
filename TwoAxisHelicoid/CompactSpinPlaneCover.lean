import TwoAxisHelicoid.CompactMultiplierSpinBundle
import TwoAxisHelicoid.PuncturedCoverExtension
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace TwoAxisHelicoid
open Set Topology
variable (L : PeriodPair) (χ : L.lattice →+ ZMod 2)

/-- Simultaneous plane lifts of the torus parameter and of the spin
angle. Their product is simply connected. -/
noncomputable def compactSpinPlaneMk (x : ℂ × ℝ) : CompactMultiplierSpinBundle L χ :=
  Quotient.mk _ (latticeSignCoverMk L χ (x.1,0),Circle.exp x.2)

theorem compactSpinPlaneMk_projection (x : ℂ × ℝ) :
    compactMultiplierSpinProjection L χ (compactSpinPlaneMk L χ x) =
      (periodTorusProjection L x.1,(Circle.exp x.2)^2) := rfl

theorem compactSpinPlaneMk_isOpenQuotientMap : IsOpenQuotientMap (compactSpinPlaneMk L χ) := by
  let g := fun z : ℂ => latticeSignCoverMk L χ (z,0)
  have hi : IsOpenMap (fun z : ℂ => (z,(0 : ZMod 2))) := by
    intro U hU
    have h : (fun z : ℂ => (z,(0 : ZMod 2))) '' U = U ×ˢ {0} := by
      ext ⟨z,a⟩
      constructor
      · rintro ⟨w,hw,h⟩
        obtain ⟨rfl,rfl⟩ := Prod.ext_iff.mp h
        exact ⟨hw,rfl⟩
      · rintro ⟨hz,ha⟩
        exact ⟨z,hz,Prod.ext rfl ha.symm⟩
    rw [h]
    exact hU.prod (isOpen_discrete _)
  have hgo : IsOpenMap g := (latticeSignCoverMk_isLocalHomeomorph L χ).isOpenMap.comp hi
  have hgc : Continuous g := QuotientAddGroup.continuous_mk.comp
    (continuous_id.prodMk continuous_const)
  let hQ := spinPhaseMk_isOpenQuotientMap (latticeSignCoverDeck L χ) (latticeSignCoverDeck_involutive L χ)
  refine ⟨?_,hQ.continuous.comp (hgc.prodMap Circle.exp.continuous),
    hQ.isOpenMap.comp (hgo.prodMap Circle.isCoveringMap_exp.isOpenMap)⟩
  intro s
  obtain ⟨⟨e,u⟩,rfl⟩ := Quotient.exists_rep s
  obtain ⟨⟨z,σ⟩,rfl⟩ := Quotient.exists_rep e
  rcases zmod_two_cases σ with rfl | rfl
  · obtain ⟨r,hr⟩ := Circle.exp_surjective u
    exact ⟨(z,r),Quotient.sound (Or.inl (Prod.ext rfl hr))⟩
  · obtain ⟨r,hr⟩ := Circle.exp_surjective (-u)
    refine ⟨(z,r),Quotient.sound (Or.inr (Prod.ext ?_ hr))⟩
    change latticeSignCoverMk L χ (z,0) = latticeSignCoverDeck L χ (latticeSignCoverMk L χ (z,1))
    rw [latticeSignCoverDeck_mk,show (1 : ZMod 2)+1 = 0 from by decide]

noncomputable def compactSpinPlaneTranslate (a : ℂ × ℝ) :
    CompactMultiplierSpinBundle L χ → CompactMultiplierSpinBundle L χ :=
  Quotient.map (fun w => (w.1+latticeSignCoverMk L χ (a.1,0),w.2*Circle.exp a.2)) (by
    rintro x y (rfl | rfl)
    · exact Or.inl rfl
    · right
      refine Prod.ext ?_ (neg_mul _ _)
      change (y.1+latticeSignCoverMk L χ (0,1))+latticeSignCoverMk L χ (a.1,0) =
        (y.1+latticeSignCoverMk L χ (a.1,0))+latticeSignCoverMk L χ (0,1)
      abel)

theorem compactSpinPlaneMk_add (x a : ℂ × ℝ) :
    compactSpinPlaneMk L χ (x+a) = compactSpinPlaneTranslate L χ a (compactSpinPlaneMk L χ x) := by
  apply Quotient.sound
  left
  refine Prod.ext ?_ (Circle.exp_add _ _)
  change (QuotientAddGroup.mk (x.1+a.1,(0 : ZMod 2)) : LatticeSignCover L χ) =
    QuotientAddGroup.mk (x.1,(0 : ZMod 2))+QuotientAddGroup.mk (a.1,(0 : ZMod 2))
  rw [← QuotientAddGroup.mk_add]
  rfl

theorem compactSpinPlaneMk_eq_translate {x y : ℂ × ℝ} (h : compactSpinPlaneMk L χ x = compactSpinPlaneMk L χ y)
    (a : ℂ × ℝ) : compactSpinPlaneMk L χ (x+a) = compactSpinPlaneMk L χ (y+a) := by
  rw [compactSpinPlaneMk_add,compactSpinPlaneMk_add,h]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compactSpinPlaneMk_isOpenQuotientMap
#print axioms TwoAxisHelicoid.compactSpinPlaneMk_eq_translate
