import TwoAxisHelicoid.CompactRealPrimitiveRigidity
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

namespace TwoAxisHelicoid
open Complex Set Filter Metric InnerProductSpace
open scoped Topology

/-- Local holomorphic primitives on coordinate disks. The increment along a
step inside a disk is the real part of the difference of these primitives. -/
structure HolomorphicPrimitiveDisks (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  radius : X → ℝ
  radius_pos : ∀ p, 0 < radius p
  ball_target : ∀ p, ball (chartAt ℂ p p) (radius p) ⊆ (chartAt ℂ p).target
  primitive : X → ℂ → ℂ
  analytic : ∀ p z, z ∈ ball (chartAt ℂ p p) (radius p) → AnalyticAt ℂ (primitive p) z

namespace HolomorphicPrimitiveDisks
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

def domain (A : HolomorphicPrimitiveDisks X) (p : X) : Set X :=
  (chartAt ℂ p).source ∩ (chartAt ℂ p) ⁻¹' ball (chartAt ℂ p p) (A.radius p)

theorem domain_isOpen (A : HolomorphicPrimitiveDisks X) (p : X) : IsOpen (A.domain p) :=
  (chartAt ℂ p).isOpen_inter_preimage isOpen_ball

theorem mem_domain (A : HolomorphicPrimitiveDisks X) (p : X) : p ∈ A.domain p :=
  ⟨mem_chart_source ℂ p,mem_ball_self (A.radius_pos p)⟩

noncomputable def increment (A : HolomorphicPrimitiveDisks X) (p x y : X) : ℝ :=
  (A.primitive p (chartAt ℂ p y)).re-(A.primitive p (chartAt ℂ p x)).re

/-- Finite chains of local primitive increments; this is the period data
before a global primitive has been constructed. -/
inductive Chain (A : HolomorphicPrimitiveDisks X) : X → X → ℝ → Prop
  | refl (x : X) : Chain A x x 0
  | step (p x y : X) (hx : x ∈ A.domain p) (hy : y ∈ A.domain p) :
      Chain A x y (A.increment p x y)
  | trans {x y z : X} {r s : ℝ} : Chain A x y r → Chain A y z s → Chain A x z (r+s)

theorem Chain.symm {A : HolomorphicPrimitiveDisks X} {x y : X} {r : ℝ}
    (h : A.Chain x y r) : A.Chain y x (-r) := by
  induction h with
  | refl x => simpa using Chain.refl (A := A) x
  | step p x y hx hy =>
      simpa only [increment,neg_sub] using Chain.step (A := A) p y x hy hx
  | trans h₁ h₂ ih₁ ih₂ =>
      convert Chain.trans ih₂ ih₁ using 1
      ring

def ZeroRealPeriods (A : HolomorphicPrimitiveDisks X) : Prop :=
  ∀ x r, A.Chain x x r → r = 0

theorem chain_value_unique {A : HolomorphicPrimitiveDisks X} (hP : A.ZeroRealPeriods)
    {x y : X} {r s : ℝ} (hr : A.Chain x y r) (hs : A.Chain x y s) : r = s := by
  have h := hP x (r+ -s) (Chain.trans hr hs.symm)
  linarith

theorem exists_chain [PreconnectedSpace X] (A : HolomorphicPrimitiveDisks X) (x y : X) :
    ∃ r, A.Chain x y r := by
  let S : Set X := {z | ∃ r, A.Chain x z r}
  have ho : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    rintro z ⟨r,hr⟩
    filter_upwards [(A.domain_isOpen z).mem_nhds (A.mem_domain z)] with w hw
    exact ⟨r+A.increment z z w,Chain.trans hr (Chain.step z z w (A.mem_domain z) hw)⟩
  have hc : IsClosed S := by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    filter_upwards [(A.domain_isOpen z).mem_nhds (A.mem_domain z)] with w hw
    rintro ⟨r,hr⟩
    exact hz ⟨r+A.increment z w z,Chain.trans hr (Chain.step z w z hw (A.mem_domain z))⟩
  have hall := (show IsClopen S from ⟨hc,ho⟩).eq_univ ⟨x,0,Chain.refl x⟩
  have hy : y ∈ S := by rw [hall]; trivial
  exact hy

noncomputable def realPrimitive [PreconnectedSpace X] (A : HolomorphicPrimitiveDisks X)
    (base : X) (x : X) : ℝ := Classical.choose (A.exists_chain base x)

theorem realPrimitive_chain [PreconnectedSpace X] (A : HolomorphicPrimitiveDisks X)
    (base x : X) : A.Chain base x (A.realPrimitive base x) :=
  Classical.choose_spec (A.exists_chain base x)

theorem realPrimitive_sub [PreconnectedSpace X] {A : HolomorphicPrimitiveDisks X}
    (hP : A.ZeroRealPeriods) (base p : X) {x y : X}
    (hx : x ∈ A.domain p) (hy : y ∈ A.domain p) :
    A.realPrimitive base y-A.realPrimitive base x = A.increment p x y := by
  have h := chain_value_unique hP (A.realPrimitive_chain base y)
    (Chain.trans (A.realPrimitive_chain base x) (Chain.step p x y hx hy))
  linarith

theorem realPrimitive_continuous [PreconnectedSpace X] {A : HolomorphicPrimitiveDisks X}
    (hP : A.ZeroRealPeriods) (base : X) : Continuous (A.realPrimitive base) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have ha := (A.analytic p (chartAt ℂ p p) (mem_ball_self (A.radius_pos p))).continuousAt
  have hf : ContinuousAt (fun x => (A.primitive p (chartAt ℂ p x)).re+
      (A.realPrimitive base p-(A.primitive p (chartAt ℂ p p)).re)) p :=
    (Complex.continuous_re.continuousAt.comp
      (ha.comp ((chartAt ℂ p).continuousAt (mem_chart_source ℂ p)))).add continuousAt_const
  apply hf.congr_of_eventuallyEq
  filter_upwards [(A.domain_isOpen p).mem_nhds (A.mem_domain p)] with y hy
  have h := realPrimitive_sub hP base p (A.mem_domain p) hy
  dsimp [increment] at h
  linarith

theorem realPrimitive_chart_formula [PreconnectedSpace X] {A : HolomorphicPrimitiveDisks X}
    (hP : A.ZeroRealPeriods) (base p : X) :
    ∀ᶠ z in 𝓝 (chartAt ℂ p p),
      A.realPrimitive base ((chartAt ℂ p).symm z) = (A.primitive p z).re+
        (A.realPrimitive base p-(A.primitive p (chartAt ℂ p p)).re) := by
  filter_upwards [ball_mem_nhds (chartAt ℂ p p) (A.radius_pos p)] with z hz
  have hzt := A.ball_target p hz
  have hD : (chartAt ℂ p).symm z ∈ A.domain p := by
    refine ⟨(chartAt ℂ p).map_target hzt,?_⟩
    change (chartAt ℂ p) ((chartAt ℂ p).symm z) ∈ ball (chartAt ℂ p p) (A.radius p)
    rwa [(chartAt ℂ p).right_inv hzt]
  have h := realPrimitive_sub hP base p (A.mem_domain p) hD
  dsimp [increment] at h
  rw [(chartAt ℂ p).right_inv hzt] at h
  linarith

theorem realPrimitive_harmonic [PreconnectedSpace X] {A : HolomorphicPrimitiveDisks X}
    (hP : A.ZeroRealPeriods) (base : X) : HarmonicInComplexCharts (A.realPrimitive base) := by
  intro p
  have hh := (A.analytic p (chartAt ℂ p p) (mem_ball_self (A.radius_pos p))).harmonicAt_re
  exact (harmonicAt_congr_nhds (realPrimitive_chart_formula hP base p)).mpr
    (hh.add (harmonicAt_const _))

/-- Zero real periods of the local primitives construct a global real
harmonic primitive. Compactness then forces every local holomorphic
coefficient to vanish. No global primitive is assumed. -/
theorem coefficient_zero_of_zero_real_periods [CompactSpace X] [PreconnectedSpace X]
    {A : HolomorphicPrimitiveDisks X} (hP : A.ZeroRealPeriods) (p : X) :
    deriv (A.primitive p) (chartAt ℂ p p) = 0 := by
  have hc := compact_connected_chart_harmonic_constant
    (realPrimitive_continuous hP p) (realPrimitive_harmonic hP p)
  apply analytic_deriv_zero_of_locally_constant_re
    (A.analytic p (chartAt ℂ p p) (mem_ball_self (A.radius_pos p)))
  filter_upwards [realPrimitive_chart_formula hP p p] with z hz
  have he := hc ((chartAt ℂ p).symm z) p
  linarith

end HolomorphicPrimitiveDisks
end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.HolomorphicPrimitiveDisks.exists_chain
#print axioms TwoAxisHelicoid.HolomorphicPrimitiveDisks.realPrimitive_harmonic
#print axioms TwoAxisHelicoid.HolomorphicPrimitiveDisks.coefficient_zero_of_zero_real_periods
