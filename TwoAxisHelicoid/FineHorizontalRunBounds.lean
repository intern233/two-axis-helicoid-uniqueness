import TwoAxisHelicoid.FineHorizontalNode

namespace TwoAxisHelicoid
open Complex
attribute [local irreducible] thetaA

noncomputable def horizontalSamplePrefix (t a : ℝ) (N n : ℕ) : ℝ :=
  ∑ i∈Finset.range n,(thetaA t a (((-1+(i:ℝ)/N:ℝ):ℂ)+I*((t/2:ℝ):ℂ))).re

/-- A contiguous group of dyadic node enclosures gives bounds on the
difference of two exact sample prefixes. Adjacent groups then telescope. -/
theorem fineHorizontalNodeRun_bounds {p : RootDyadicParameters} {t l u : ℚ}
    {N k : ℕ} {ws : List FineHorizontalNode}
    (data : p.HorizontalFineValid t t l u) (ok : fineHorizontalNodeRun p t N k ws)
    {a : ℝ} (al : (l:ℝ)≤a) (au : a≤(u:ℝ)) :
    (((ws.map FineHorizontalNode.lower).sum:ℚ):ℝ)≤horizontalSamplePrefix t a N (k+ws.length)-horizontalSamplePrefix t a N k ∧
    horizontalSamplePrefix t a N (k+ws.length)-horizontalSamplePrefix t a N k≤(((ws.map FineHorizontalNode.upper).sum:ℚ):ℝ) := by
  induction ws generalizing k with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨v₁,v₂⟩ := FineHorizontalNode.sound data ok.1 al au
    push_cast at v₁ v₂
    obtain ⟨s₁,s₂⟩ := ih ok.2
    have step (s : ℝ) (j : ℕ) : horizontalSamplePrefix s a N (j+1)=horizontalSamplePrefix s a N j+
        (thetaA s a (((-1+(j:ℝ)/N:ℝ):ℂ)+I*((s/2:ℝ):ℂ))).re := by
      unfold horizontalSamplePrefix
      exact Finset.sum_range_succ (fun i : ℕ =>
        (thetaA s a (((-1+(i:ℝ)/N:ℝ):ℂ)+I*((s/2:ℝ):ℂ))).re) j
    have eq : k+(w::ws).length=k+1+ws.length := by
      change k+(ws.length+1)=k+1+ws.length
      omega
    rw [eq]
    simp only [List.map_cons,List.sum_cons,Rat.cast_add]
    rw [step] at s₁ s₂
    push_cast at s₁ s₂ ⊢
    constructor <;> linarith

theorem fineHorizontalNodeRun_rational_bounds {p : RootDyadicParameters} {t l u : ℚ}
    {N k e : ℕ} {ws : List FineHorizontalNode} {lo hi : ℚ}
    (data : p.HorizontalFineValid t t l u) (ok : fineHorizontalNodeRun p t N k ws)
    (size : k+ws.length=e) (lower : (ws.map FineHorizontalNode.lower).sum=lo)
    (upper : (ws.map FineHorizontalNode.upper).sum=hi) {a : ℝ} (al : (l:ℝ)≤a) (au : a≤(u:ℝ)) :
    (lo:ℝ)≤horizontalSamplePrefix t a N e-horizontalSamplePrefix t a N k ∧
      horizontalSamplePrefix t a N e-horizontalSamplePrefix t a N k≤(hi:ℝ) := by
  simpa only [size,lower,upper] using fineHorizontalNodeRun_bounds data ok al au

theorem horizontalSamplePrefix_add_bounds {t a : ℝ} {N i j k : ℕ} {l₁ l₂ u₁ u₂ l u : ℚ}
    (left : (l₁:ℝ)≤horizontalSamplePrefix t a N j-horizontalSamplePrefix t a N i ∧
      horizontalSamplePrefix t a N j-horizontalSamplePrefix t a N i≤(u₁:ℝ))
    (right : (l₂:ℝ)≤horizontalSamplePrefix t a N k-horizontalSamplePrefix t a N j ∧
      horizontalSamplePrefix t a N k-horizontalSamplePrefix t a N j≤(u₂:ℝ))
    (lc : l₁+l₂=l) (uc : u₁+u₂=u) :
    (l:ℝ)≤horizontalSamplePrefix t a N k-horizontalSamplePrefix t a N i ∧
      horizontalSamplePrefix t a N k-horizontalSamplePrefix t a N i≤(u:ℝ) := by
  subst l;subst u
  push_cast
  constructor <;> linarith [left.1,left.2,right.1,right.2]

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.fineHorizontalNodeRun_bounds
#print axioms TwoAxisHelicoid.horizontalSamplePrefix_add_bounds
