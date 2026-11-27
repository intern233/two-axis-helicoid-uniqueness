module

public import TwoAxisHelicoid.SupportedChartComplement
public import TwoAxisHelicoid.PunctureClosedDiskPlane
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith

public section
namespace TwoAxisHelicoid
open Complex Set Metric Topology

/-- In a Hausdorff surface, replacing one puncture by a closed coordinate
disk lying inside a larger coordinate disk preserves the homeomorphism
type. The same chart is used throughout the construction. -/
theorem chart_puncture_closed_disk_homeomorphism {M : Type*} [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph M ℂ) {p : M} (hp : p∈e.source) {r : ℝ} (hr : 0<r)
    (buffer : closedBall (e p) (2*r)⊆e.target) :
    Nonempty ({x : M // x≠p} ≃ₜ {x : M // x∉e.symm '' closedBall (e p) r}) := by
  let c := e p
  let K := e.symm '' closedBall c (2*r)
  let S := {x : M | x≠p}
  let T := (e.symm '' closedBall c r)ᶜ
  let U := {z : ℂ | z≠c}
  let V := {z : ℂ | r<‖z-c‖}
  have small : closedBall c r⊆e.target := (closedBall_subset_closedBall (by linarith : r≤2*r)).trans buffer
  have kc : IsClosed K := ((isCompact_closedBall c (2*r)).image_of_continuousOn
    (e.continuousOn_symm.mono buffer)).isClosed
  have ks : K⊆e.source := by rintro _ ⟨z,h,rfl⟩; exact e.map_target (buffer h)
  have sU (x : M) (hx : x∈e.source) : x∈S ↔ e x∈U :=
    ⟨fun non eq => non (e.injOn hx hp eq),fun non eq => non (congrArg e eq)⟩
  have tV (x : M) (hx : x∈e.source) : x∈T ↔ e x∈V := by
    constructor
    · intro non
      change r < ‖e x - c‖
      apply lt_of_not_ge
      intro bound
      exact non ⟨e x,mem_closedBall.mpr (by simpa only [dist_eq_norm] using bound),e.left_inv hx⟩
    · rintro far ⟨z,hz,eq⟩
      have same : e x=z := by rw [←eq,e.right_inv (small hz)]
      change r<‖e x-c‖ at far
      rw [same] at far
      exact far.not_ge (by simpa only [dist_eq_norm] using mem_closedBall.mp hz)
  have out (x : M) (hx : x∉e.source) : x∈S ↔ x∈T := by
    have neq : x≠p := fun eq => hx (eq ▸ hp)
    have no : x∈T := by rintro ⟨z,h,rfl⟩; exact hx (e.map_target (small h))
    exact ⟨fun _ => no,fun _ => neq⟩
  have uo : IsOpen U := isClosed_singleton.isOpen_compl
  have vo : IsOpen V := isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
  obtain ⟨H,fixF,innerF,fixG,innerG⟩ := puncture_and_disk_plane_homeomorphism c hr
  have far {x : M} (hs : x∈e.source) (outside : x∉K) : 2*r≤‖e x-c‖ := by
    apply le_of_lt
    apply lt_of_not_ge
    intro near
    exact outside ⟨e x,mem_closedBall.mpr (by simpa only [dist_eq_norm] using near),e.left_inv hs⟩
  apply supported_chart_complement_homeomorphism (K:=K) e kc ks sU tV out uo vo H
  · intro z hz
    by_cases h : ‖z.1-c‖≤2*r
    · exact buffer (mem_closedBall.mpr (by simpa only [dist_eq_norm] using innerF z h))
    · rwa [fixF z (le_of_not_ge h)]
  · intro z hz
    by_cases h : ‖z.1-c‖≤2*r
    · exact buffer (mem_closedBall.mpr (by simpa only [dist_eq_norm] using innerG z h))
    · rwa [fixG z (le_of_not_ge h)]
  · exact fun x hs ha hk => fixF ⟨e x,(sU x hs).mp ha⟩ (far hs hk)
  · exact fun x hs hb hk => fixG ⟨e x,(tV x hs).mp hb⟩ (far hs hk)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.chart_puncture_closed_disk_homeomorphism
