import TwoAxisHelicoid.RealPeriodPrimitive

namespace TwoAxisHelicoid
open Set Filter Metric
open scoped Topology
set_option maxHeartbeats 800000

namespace HolomorphicPrimitiveDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Local primitive chains whose vertices lie in the regular locus. A later
geometric lemma realizes each step by paths avoiding the exceptional points. -/
inductive RegularChain (A : HolomorphicPrimitiveDisks X) (U : Set X) : X → X → ℝ → Prop
  | refl (x : X) (hx : x ∈ U) : RegularChain A U x x 0
  | step (p x y : X) (hx : x ∈ A.domain p) (hy : y ∈ A.domain p)
      (hxU : x ∈ U) (hyU : y ∈ U) : RegularChain A U x y (A.increment p x y)
  | trans {x y z : X} {r s : ℝ} :
      RegularChain A U x y r → RegularChain A U y z s → RegularChain A U x z (r+s)

theorem increment_continuousAt (A : HolomorphicPrimitiveDisks X) (p : X) {x y : X}
    (hx : x ∈ A.domain p) (hy : y ∈ A.domain p) :
    ContinuousAt (fun q : X × X => A.increment p q.1 q.2) (x,y) := by
  have hf {v : X} (hv : v ∈ A.domain p) :
      ContinuousAt (fun w => (A.primitive p (chartAt ℂ p w)).re) v :=
    Complex.continuous_re.continuousAt.comp
      ((A.analytic p _ hv.2).continuousAt.comp ((chartAt ℂ p).continuousAt hv.1))
  exact ((hf hy).comp (show ContinuousAt (fun q : X × X => q.2) (x,y) from
    continuous_snd.continuousAt)).sub
    ((hf hx).comp (show ContinuousAt (fun q : X × X => q.1) (x,y) from
      continuous_fst.continuousAt))

theorem increment_neighborhoods (A : HolomorphicPrimitiveDisks X) (p : X) {x y : X}
    (hx : x ∈ A.domain p) (hy : y ∈ A.domain p) {ε : ℝ} (hε : 0 < ε) :
    ∃ V W : Set X, IsOpen V ∧ IsOpen W ∧ x ∈ V ∧ y ∈ W ∧
      V ⊆ A.domain p ∧ W ⊆ A.domain p ∧
      ∀ v ∈ V, ∀ w ∈ W, |A.increment p v w-A.increment p x y| < ε := by
  have he := (A.increment_continuousAt p hx hy).preimage_mem_nhds
    (ball_mem_nhds (A.increment p x y) hε)
  obtain ⟨V,W,hV,hxV,hW,hyW,hVW⟩ := mem_nhds_prod_iff'.mp he
  refine ⟨V ∩ A.domain p,W ∩ A.domain p,hV.inter (A.domain_isOpen p),
    hW.inter (A.domain_isOpen p),⟨hxV,hx⟩,⟨hyW,hy⟩,inter_subset_right,
    inter_subset_right,?_⟩
  intro v hv w hw
  simpa only [mem_preimage,mem_ball,Real.dist_eq] using
    hVW (show (v,w) ∈ V ×ˢ W from ⟨hv.1,hw.1⟩)

theorem Chain.regular_approximation {A : HolomorphicPrimitiveDisks X} {U : Set X}
    (hU : Dense U) {x y : X} {r : ℝ} (h : A.Chain x y r) :
    ∀ ε : ℝ, 0 < ε → ∃ V W : Set X,
      IsOpen V ∧ IsOpen W ∧ x ∈ V ∧ y ∈ W ∧
      ∀ v ∈ V, ∀ w ∈ W, v ∈ U → w ∈ U →
        ∃ s, A.RegularChain U v w s ∧ |s-r| < ε := by
  induction h with
  | refl x =>
      intro ε hε
      obtain ⟨V,W,hV,hW,hxV,hxW,hVD,hWD,he⟩ :=
        A.increment_neighborhoods x (A.mem_domain x) (A.mem_domain x) hε
      refine ⟨V,W,hV,hW,hxV,hxW,?_⟩
      intro v hv w hw hvU hwU
      refine ⟨A.increment x v w,RegularChain.step x v w (hVD hv) (hWD hw) hvU hwU,?_⟩
      simpa only [increment,sub_self] using he v hv w hw
  | step p x y hx hy =>
      intro ε hε
      obtain ⟨V,W,hV,hW,hxV,hyW,hVD,hWD,he⟩ := A.increment_neighborhoods p hx hy hε
      exact ⟨V,W,hV,hW,hxV,hyW,fun v hv w hw hvU hwU =>
        ⟨A.increment p v w,RegularChain.step p v w (hVD hv) (hWD hw) hvU hwU,he v hv w hw⟩⟩
  | @trans x y z r s h₁ h₂ ih₁ ih₂ =>
      intro ε hε
      obtain ⟨V,W,hV,hW,hxV,hyW,h₁⟩ := ih₁ (ε/2) (by positivity)
      obtain ⟨P,Q,hP,hQ,hyP,hzQ,h₂⟩ := ih₂ (ε/2) (by positivity)
      obtain ⟨y',hy'U,hy'⟩ := hU.exists_mem_open (hW.inter hP) ⟨y,hyW,hyP⟩
      refine ⟨V,Q,hV,hQ,hxV,hzQ,?_⟩
      intro v hv w hw hvU hwU
      obtain ⟨r',hr',her⟩ := h₁ v hv y' hy'.1 hvU hy'U
      obtain ⟨s',hs',hes⟩ := h₂ y' hy'.2 w hw hy'U hwU
      refine ⟨r'+s',RegularChain.trans hr' hs',?_⟩
      have htri := abs_add_le (r'-r) (s'-s)
      rw [show r'-r+(s'-s) = r'+s'-(r+s) by ring] at htri
      linarith

/-- Periods extend across a dense exceptional-set complement by perturbing
the finitely many vertices of each closed chain. -/
theorem zeroRealPeriods_of_dense_regular_periods {A : HolomorphicPrimitiveDisks X}
    {U : Set X} (hU : Dense U)
    (hP : ∀ x r, A.RegularChain U x x r → r = 0) : A.ZeroRealPeriods := by
  intro x r hr
  have he (ε : ℝ) (hε : 0 < ε) : |r| < ε := by
    obtain ⟨V,W,hV,hW,hxV,hxW,h⟩ := hr.regular_approximation hU ε hε
    obtain ⟨v,hvU,hv⟩ := hU.exists_mem_open (hV.inter hW) ⟨x,hxV,hxW⟩
    obtain ⟨s,hs,hes⟩ := h v hv.1 v hv.2 hvU hvU
    rw [hP v s hs] at hes
    simpa only [zero_sub,abs_neg] using hes
  by_contra hn
  exact (lt_irrefl |r|) (he |r| (abs_pos.mpr hn))

end HolomorphicPrimitiveDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicPrimitiveDisks.zeroRealPeriods_of_dense_regular_periods
