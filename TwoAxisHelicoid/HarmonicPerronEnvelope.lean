import TwoAxisHelicoid.HolomorphicDiskNormalFamily
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Topology.Order.MonotoneConvergence

namespace TwoAxisHelicoid
open Complex Set Filter Metric Function Topology InnerProductSpace
open scoped Topology

/-- An upper bounded family of harmonic functions on a disk with
finite pointwise ultrafilter limits has a harmonic limit. Holomorphic
conjugates can be chosen independently for each family member. -/
theorem harmonic_disk_ultrafilter_limit {ι : Type*} (l : Ultrafilter ι)
    {u : ι → ℂ → ℝ} {v : ℂ → ℝ} {c : ℂ} {r C : ℝ}
    (hu : ∀ i, HarmonicOnNhd (u i) (ball c r))
    (bound : ∀ i z, z∈ball c r → u i z≤C)
    (limit : ∀ z∈ball c r, Tendsto (fun i => u i z) (l : Filter ι) (𝓝 (v z))) :
    HarmonicOnNhd v (ball c r) := by
  choose g an realPart using fun i => (hu i).exists_analyticOnNhd_ball_re_eq
  have reG (i : ι) (z : ℂ) (hz : z∈ball c r) : (g i z).re=u i z := realPart i hz
  let F := fun i z => Complex.exp (g i z-(C:ℂ))
  obtain ⟨f,conv,hol,_⟩ := bounded_holomorphic_disk_normal_limit l F (U:=ball c r) (by
    intro x hx
    obtain ⟨d,dp,sub⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
    refine ⟨d,dp,sub,.of_forall fun i => ⟨?_,?_⟩⟩
    · exact fun z hz => (((an i z (sub hz)).sub analyticAt_const).cexp).differentiableAt.differentiableWithinAt
    · intro z hz
      apply mem_closedBall_zero_iff.mpr
      change ‖Complex.exp (g i z-(C:ℂ))‖≤1
      rw [Complex.norm_exp,Complex.sub_re,Complex.ofReal_re,reG i z (sub hz),Real.exp_le_one_iff]
      exact sub_nonpos.mpr (bound i z (sub hz)))
  have value (z : ℂ) (hz : z∈ball c r) : ‖f z‖=Real.exp (v z-C) := by
    apply tendsto_nhds_unique (conv.tendsto_at hz).norm
    exact ((Real.continuous_exp.tendsto _).comp ((limit z hz).sub_const C)).congr fun i => by
      change Real.exp (u i z-C)=‖Complex.exp (g i z-(C:ℂ))‖
      rw [Complex.norm_exp,Complex.sub_re,Complex.ofReal_re,reG i z hz]
  intro z hz
  have nz : f z≠0 := norm_pos_iff.mp ((value z hz).trans_gt (Real.exp_pos _))
  have hh := ((hol z hz).harmonicAt_log_norm nz).add (harmonicAt_const (c:=C))
  apply (harmonicAt_congr_nhds (f₂:=fun w => Real.log ‖f w‖+C) ?_).mpr hh
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  rw [value w hw,Real.log_exp]
  ring

/-- Interior Perron theorem. Directed subfunctions with harmonic
majorants in the class have a harmonic upper envelope on the chart.
All bounds used in this assertion are local to the chosen disk. -/
theorem directed_harmonic_perron_envelope {X : Type*} {A : Set (X → ℝ)} (non : A.Nonempty)
    (direct : ∀ f∈A, ∀ g∈A, ∃ h∈A, f≤h ∧ g≤h) (q : ℂ → X) {c : ℂ} {r C : ℝ}
    (bound : ∀ f∈A, ∀ z∈ball c r, f (q z)≤C)
    (lift : ∀ f∈A, ∃ g∈A, f≤g ∧ HarmonicOnNhd (g ∘ q) (ball c r)) :
    HarmonicOnNhd (fun z => ⨆ f : A, f.val (q z)) (ball c r) := by
  classical
  let _ : Nonempty A := non.to_subtype
  let _ : IsDirectedOrder A := ⟨fun f g => by
    obtain ⟨h,mem,hf,hg⟩ := direct _ f.2 _ g.2
    exact ⟨⟨h,mem⟩,hf,hg⟩⟩
  choose G mem up harmonic using fun f : A => lift f.val f.2
  let l := Ultrafilter.of (atTop : Filter A)
  have upper (z : ℂ) (hz : z∈ball c r) : BddAbove (range (fun f : A => f.val (q z))) :=
    ⟨C,fun _ ⟨f,eq⟩ => eq ▸ bound _ f.2 z hz⟩
  apply harmonic_disk_ultrafilter_limit l (u:=fun f => G f ∘ q) harmonic (fun f z hz => bound _ (mem f) z hz)
  intro z hz
  have m : Monotone (fun f : A => f.val (q z)) := fun a b h => h (q z)
  have lo := (tendsto_atTop_ciSup m (upper z hz)).mono_left (Ultrafilter.of_le (atTop : Filter A))
  exact lo.squeeze tendsto_const_nhds (fun f => up f (q z))
    (fun f => le_ciSup (upper z hz) (⟨G f,mem f⟩ : A))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.directed_harmonic_perron_envelope
