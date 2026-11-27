import TwoAxisHelicoid.CentralRatioJetSound
import TwoAxisHelicoid.RectangleThetaQuadrant
import TwoAxisHelicoid.RectangleRealPartBound

namespace TwoAxisHelicoid
open Complex Set Topology Bornology
open scoped ComplexOrder

theorem central_ratio_rectangle_regular {t a : ℝ} (tb : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1) {z : ℂ} (hx : z.re∈Icc (1/2:ℝ) (3/5))
    (hy : z.im∈Icc (0:ℝ) (7/16)) : z+a∉(rhombicPeriodPair t ht).lattice := by
  rcases hy.1.eq_or_lt with h|h
  · have e : z+a=((z.re+a:ℝ):ℂ) := by apply Complex.ext <;> simp [h.symm]
    rw [e]
    exact real_not_mem_rhombic_lattice_of_pos ht (by linarith [hx.1,ha.1]) (by linarith [hx.2,ha.2])
  · apply rhombic_horizontal_strip_not_mem ht
    have big : (7/16:ℝ)<t := by have low := tb.1; norm_num [rootTLower] at low; linarith
    change (z+a).im∈Ioo 0 t
    simpa using And.intro h (hy.2.trans_lt big)

theorem central_ratio_rectangle_derivative_signs {t a : ℝ} (tb : t∈Icc (rootTLower:ℝ) rootTUpper)
    (ab : a∈Icc (rootALower:ℝ) rootAUpper) (ht : 0<t) (ha : a∈Ioo (0:ℝ) 1)
    (left : CheckedCentralRatioJets false true (1/2) 0 (7/16))
    (right : CheckedCentralRatioJets false true (3/5) 0 (7/16))
    (bottom : CheckedCentralRatioJets false false 0 (1/2) (3/5))
    (top : CheckedCentralRatioJets false false (7/16) (1/2) (3/5))
    (third : CheckedCentralRatioJets true true (1/2) 0 (7/16)) :
    let f := centralPhaseThetaRatio t a
    (∀ x∈Icc (1/2:ℝ) (3/5), ∀ y∈Icc (0:ℝ) (7/16), 0<(deriv (deriv f) ((x:ℂ)+I*y)).re) ∧
      ∀ y∈Icc (0:ℝ) (7/16), 0<(deriv (deriv (deriv f)) (((1/2:ℝ):ℂ)+I*y)).re := by
  intro f
  let X := Icc (1/2:ℝ) (3/5)
  let Y := Icc (0:ℝ) (7/16)
  let Z := fun x y : ℝ => (x:ℂ)+I*y
  have reg {x y : ℝ} (hx : x∈X) (hy : y∈Y) : Z x y+a∉(rhombicPeriodPair t ht).lattice :=
    central_ratio_rectangle_regular tb ht ha (by simpa [Z,X] using hx) (by simpa [Z,Y] using hy)
  have vx {x : ℚ} (xin : (x:ℝ)∈X) (w : CheckedCentralRatioJets false true x 0 (7/16)) (y : ℝ) (hy : y∈Y) :
      centralRatioJetMargin false≤(deriv (deriv f) (⟨(x:ℝ),y⟩:ℂ)).re := by
    have hit := w.sound tb ab ht y (by norm_num; exact hy) (by exact reg xin hy)
    have eq : Z (x:ℝ) y=⟨(x:ℝ),y⟩ := by apply Complex.ext <;> simp [Z]
    change centralRatioJetMargin false<(iteratedDeriv 2 f (Z (x:ℝ) y)).re at hit
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,eq] using hit.le
  have wy {y : ℚ} (yin : (y:ℝ)∈Y) (w : CheckedCentralRatioJets false false y (1/2) (3/5)) (x : ℝ) (hx : x∈X) :
      centralRatioJetMargin false≤(deriv (deriv f) (⟨x,(y:ℝ)⟩:ℂ)).re := by
    have hit := w.sound tb ab ht x (by norm_num; exact hx) (by exact reg hx yin)
    have eq : Z x (y:ℝ)=⟨x,(y:ℝ)⟩ := by apply Complex.ext <;> simp [Z]
    change centralRatioJetMargin false<(iteratedDeriv 2 f (Z x (y:ℝ))).re at hit
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero,eq] using hit.le
  have allv (x : ℝ) (hx : x∈({1/2,3/5}:Set ℝ)) (y : ℝ) (hy : y∈Y) : centralRatioJetMargin false≤(deriv (deriv f) (⟨x,y⟩:ℂ)).re := by
    rcases hx with rfl|hx
    · simpa using vx (by norm_num [X]) left y hy
    · obtain rfl := mem_singleton_iff.mp hx
      simpa using vx (by norm_num [X]) right y hy
  have allh (y : ℝ) (hy : y∈({0,7/16}:Set ℝ)) (x : ℝ) (hx : x∈X) : centralRatioJetMargin false≤(deriv (deriv f) (⟨x,y⟩:ℂ)).re := by
    rcases hy with rfl|hy
    · simpa using wy (by norm_num [Y]) bottom x hx
    · obtain rfl := mem_singleton_iff.mp hy
      simpa using wy (by norm_num [Y]) top x hx
  have bd := rectangle_real_lower_bound (by norm_num : (1/2:ℝ)≤3/5) (by norm_num : (0:ℝ)≤7/16)
    (f:=deriv (deriv f)) (fun _ hx hy => (centralPhaseThetaRatio_analyticAt ht (central_ratio_rectangle_regular tb ht ha hx hy)).deriv.deriv.differentiableAt) allv allh
  refine ⟨fun x hx y hy => (centralRatioJetMargin_pos false).trans_le
    (bd (Z x y) (by simpa [Z] using hx) (by simpa [Z] using hy)),?_⟩
  intro y hy
  have check := third.sound tb ab ht y (by norm_num; exact hy)
    (by apply reg _ hy; norm_num [X])
  simpa [centralRatioEdgePoint,iteratedDeriv_succ] using (centralRatioJetMargin_pos true).trans check

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.central_ratio_rectangle_derivative_signs
