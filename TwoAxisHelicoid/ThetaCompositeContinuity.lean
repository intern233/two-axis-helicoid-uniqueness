import TwoAxisHelicoid.DerivativeExpressions

namespace TwoAxisHelicoid
open Set Complex
attribute [local irreducible] thetaJet thetaA thetaQuotient

variable {α : Type*} [TopologicalSpace α] {S : Set α}

theorem thetaJet_comp_continuousOn {u : α → ℝ} {v : α → ℂ}
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) (ht : ∀ p ∈ S, 0 < u p) (j : ℕ) :
    ContinuousOn (fun p => thetaJet (u p) j (v p)) S := by
  intro p hp
  exact (thetaJet_joint_continuousAt (ht p hp) j (v p)).comp_continuousWithinAt
    (f := fun p => (u p,v p)) ((hu p hp).prodMk (hv p hp))

theorem thetaQuotient_comp_continuousOn {u : α → ℝ} {v : α → ℂ}
    (hu : ContinuousOn u S) (hv : ContinuousOn v S) (ht : ∀ p ∈ S, 0 < u p)
    (hn : ∀ p ∈ S, thetaJet (u p) 0 (v p) ≠ 0) (j : ℕ) :
    ContinuousOn (fun p => thetaQuotient (u p) j (v p)) S := by
  convert (thetaJet_comp_continuousOn hu hv ht j).div (thetaJet_comp_continuousOn hu hv ht 0) hn using 1
  funext p
  simp only [thetaQuotient, Pi.div_apply]

theorem thetaA_comp_continuousOn {u b : α → ℝ} {z : α → ℂ}
    (hu : ContinuousOn u S) (hb : ContinuousOn b S) (hz : ContinuousOn z S)
    (ht : ∀ p ∈ S, 0 < u p)
    (ha : ∀ p ∈ S, thetaJet (u p) 0 (Real.pi*b p/2) ≠ 0)
    (hv : ∀ p ∈ S, thetaJet (u p) 0 (Real.pi*z p/2) ≠ 0) :
    ContinuousOn (fun p => thetaA (u p) (b p) (z p)) S := by
  have hbc := Complex.continuous_ofReal.comp_continuousOn hb
  have hva : ContinuousOn (fun p => (Real.pi*b p/2 : ℂ)) S :=
    (continuousOn_const.mul hbc).div_const 2
  have hvz : ContinuousOn (fun p => (Real.pi*z p/2 : ℂ)) S :=
    (continuousOn_const.mul hz).div_const 2
  have hvm : ContinuousOn (fun p => (Real.pi*(z p-b p)/2 : ℂ)) S :=
    (continuousOn_const.mul (hz.sub hbc)).div_const 2
  have hzero := thetaJet_comp_continuousOn hu (v := fun _ => 0) continuousOn_const ht 1
  have ha0 := thetaJet_comp_continuousOn hu hva ht 0
  have hz0 := thetaJet_comp_continuousOn hu hvz ht 0
  have hm0 := thetaJet_comp_continuousOn hu hvm ht 0
  have hq := thetaQuotient_comp_continuousOn hu hvz ht hv 1
  have hp : ContinuousOn (fun p => ((Real.pi*thetaJet (u p) 1 0)/
      (2*thetaJet (u p) 0 (Real.pi*b p/2)))^2) S :=
    ((continuousOn_const.mul hzero).div (continuousOn_const.mul ha0)
    (fun p hp => mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (ha p hp))).pow 2
  have hr := (hm0.div hz0 hv).pow 2
  have he : ContinuousOn (fun p => Complex.exp ((b p-1)*Real.pi*
      thetaQuotient (u p) 1 (Real.pi*z p/2))) S :=
    (((hbc.sub continuousOn_const).mul continuousOn_const).mul hq).cexp
  convert (hp.mul hr).mul he using 1
  funext p
  simp only [thetaA, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]

theorem thetaAa_comp_continuousOn {u b : α → ℝ} {z : α → ℂ}
    (hu : ContinuousOn u S) (hb : ContinuousOn b S) (hz : ContinuousOn z S)
    (ht : ∀ p ∈ S, 0 < u p)
    (ha : ∀ p ∈ S, thetaJet (u p) 0 (Real.pi*b p/2) ≠ 0)
    (hv : ∀ p ∈ S, thetaJet (u p) 0 (Real.pi*z p/2) ≠ 0)
    (hm : ∀ p ∈ S, thetaJet (u p) 0 (Real.pi*(z p-b p)/2) ≠ 0) :
    ContinuousOn (fun p => thetaAa (u p) (b p) (z p)) S := by
  have hbc := Complex.continuous_ofReal.comp_continuousOn hb
  have hva : ContinuousOn (fun p => (Real.pi*b p/2 : ℂ)) S := (continuousOn_const.mul hbc).div_const 2
  have hvz : ContinuousOn (fun p => (Real.pi*z p/2 : ℂ)) S := (continuousOn_const.mul hz).div_const 2
  have hvm : ContinuousOn (fun p => (Real.pi*(z p-b p)/2 : ℂ)) S :=
    (continuousOn_const.mul (hz.sub hbc)).div_const 2
  have hqa := thetaQuotient_comp_continuousOn hu hva ht ha 1
  have hqz := thetaQuotient_comp_continuousOn hu hvz ht hv 1
  have hqm := thetaQuotient_comp_continuousOn hu hvm ht hm 1
  exact (thetaA_comp_continuousOn hu hb hz ht ha hv).mul
    (continuousOn_const.mul ((hqz.sub hqm).sub hqa))

theorem thetaAtMidline_comp_continuousOn {u b : α → ℝ} {z : α → ℂ}
    (hu : ContinuousOn u S) (hb : ContinuousOn b S) (hz : ContinuousOn z S)
    (ht : ∀ p ∈ S, 0 < u p)
    (ha : ∀ p ∈ S, thetaJet (u p) 0 (Real.pi*b p/2) ≠ 0)
    (hv : ∀ p ∈ S, thetaJet (u p) 0 (Real.pi*z p/2) ≠ 0)
    (hm : ∀ p ∈ S, thetaJet (u p) 0 (Real.pi*(z p-b p)/2) ≠ 0)
    (hn : ∀ p ∈ S, thetaJet (u p) 1 0 ≠ 0) :
    ContinuousOn (fun p => thetaAtMidline (u p) (b p) (z p)) S := by
  have hbc := Complex.continuous_ofReal.comp_continuousOn hb
  have hva : ContinuousOn (fun p => (Real.pi*b p/2 : ℂ)) S := (continuousOn_const.mul hbc).div_const 2
  have hvz : ContinuousOn (fun p => (Real.pi*z p/2 : ℂ)) S := (continuousOn_const.mul hz).div_const 2
  have hvm : ContinuousOn (fun p => (Real.pi*(z p-b p)/2 : ℂ)) S :=
    (continuousOn_const.mul (hz.sub hbc)).div_const 2
  have qa (j : ℕ) := thetaQuotient_comp_continuousOn hu hva ht ha j
  have qz (j : ℕ) := thetaQuotient_comp_continuousOn hu hvz ht hv j
  have qm (j : ℕ) := thetaQuotient_comp_continuousOn hu hvm ht hm j
  have q0 := (thetaJet_comp_continuousOn hu (v := fun _ => 0) continuousOn_const ht 3).div
    (thetaJet_comp_continuousOn hu (v := fun _ => 0) continuousOn_const ht 1) hn
  have hcoef : ContinuousOn (fun p => ((b p-1)*Real.pi^2 : ℂ)) S :=
    (hbc.sub continuousOn_const).mul continuousOn_const
  have hlt : ContinuousOn (fun p => thetaLt (u p) (b p) (z p)) S :=
    (continuousOn_const.mul (((q0.sub (qa 2)).add (qm 2)).sub (qz 2))).add
    ((hcoef.div_const 8).mul ((qz 3).sub ((qz 1).mul (qz 2))))
  have hlz : ContinuousOn (fun p => thetaLz (u p) (b p) (z p)) S :=
    (continuousOn_const.mul ((qm 1).sub (qz 1))).add
    ((hcoef.div_const 2).mul ((qz 2).sub ((qz 1).pow 2)))
  exact (thetaA_comp_continuousOn hu hb hz ht ha hv).mul
    (hlt.add (continuousOn_const.mul hlz))

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.thetaAtMidline_comp_continuousOn
