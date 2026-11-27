import TwoAxisHelicoid.RegularPlaneZeroGraph
import TwoAxisHelicoid.AnalyticContactAngles
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Compactness.Compact

namespace TwoAxisHelicoid
open Complex Real Function Set Filter Topology
open scoped Topology ContDiff

/-- A full circle of directions is compact. Around radius zero all its
zeros belong to the finitely many locally continued simple roots, and
these roots retain their strict angular order. -/
theorem compact_angular_zero_branches {H : ℝ × ℂ → ℝ} (sh : ContDiff ℝ ∞ H)
    {C : ℂ} (nz : C≠0) {n : ℕ} (pos : 0<n) (profile : ∀ v, H (0,v)=(C*v^n).re) :
    ∃ φ : Fin (2*n) → ℝ → ℝ,
      (∀ i, ContDiffAt ℝ ∞ (φ i) 0 ∧ φ i 0=contactArmAngle n C i.1) ∧
      ∀ᶠ r in 𝓝 (0:ℝ), StrictMono (fun i => φ i r) ∧
        (∀ i, φ i r∈Ioo (contactAngleBase n C) (contactAngleBase n C+2*Real.pi)) ∧
        ∀ θ∈Icc (contactAngleBase n C) (contactAngleBase n C+2*Real.pi),
          H (r,circleMap 0 1 θ)=0 ↔ ∃ i, θ=φ i r := by
  classical
  let K := fun p : ℝ×ℝ => H (p.1,circleMap 0 1 p.2)
  let b := contactAngleBase n C
  let a := fun i : Fin (2*n) => contactArmAngle n C i.1
  let J := Icc b (b+2*Real.pi)
  have sk : ContDiff ℝ ∞ K := sh.comp (contDiff_fst.prodMk ((contDiff_circleMap 0 1).comp contDiff_snd))
  have ka (θ : ℝ) : K (0,θ)=(C*(circleMap 0 1 θ)^n).re := profile _
  have zero (i : Fin (2*n)) : K (0,a i)=0 := (ka _).trans ((contact_circle_zero_iff nz pos).mpr ⟨i.1,rfl⟩)
  have localGraph (i : Fin (2*n)) := by
    have dz := ((sk.differentiable (by norm_num) (0,a i)).hasFDerivAt).comp_hasDerivAt
      (a i) ((hasDerivAt_const (a i) (0:ℝ)).prodMk (hasDerivAt_id (a i)))
    have derivSlice : deriv (fun θ => K (0,θ)) (a i)=fderiv ℝ K (0,a i) (0,1) := dz.deriv
    have trans := contact_circle_zero_transverse nz pos ((ka _).symm.trans (zero i))
    rw [← funext ka,derivSlice] at trans
    exact regular_plane_zero_graph (n:=∞) (by simp) sk.contDiffAt (zero i) trans
  choose φ sm center rooted unique using localGraph
  refine ⟨φ,fun i => ⟨sm i,center i⟩,?_⟩
  let S : Set (ℝ×ℝ) := {q | K q=0 → ∃ i, q.2=φ i q.1}
  have around : S∈𝓝ˢ (({0}:Set ℝ) ×ˢ J) := by
    apply mem_nhdsSet_iff_forall.mpr
    rintro ⟨r,θ⟩ ⟨hr,hθ⟩
    obtain rfl : r=0 := hr
    by_cases h : K (0,θ)=0
    · obtain ⟨i,eq⟩ := (contact_zeros_in_period nz pos hθ).mp ((ka θ).symm.trans h)
      change θ=a i at eq
      subst θ
      filter_upwards [unique i] with q uq
      exact fun hv => ⟨i,uq.mp hv⟩
    · filter_upwards [sk.continuous.continuousAt.eventually_ne h] with q hn
      exact fun hv => (hn hv).elim
  rw [isCompact_singleton.nhdsSet_prod_eq isCompact_Icc,nhdsSet_singleton] at around
  obtain ⟨U,hu,V,hv,sub⟩ := Filter.mem_prod_iff.mp around
  have ordered : ∀ᶠ r in 𝓝 (0:ℝ), StrictMono (fun i => φ i r) := by
    have pair (i j : Fin (2*n)) : ∀ᶠ r in 𝓝 (0:ℝ), i<j → φ i r<φ j r := by
      by_cases ij : i<j
      · have lt : φ i 0<φ j 0 := by
          rw [center i,center j]
          apply contact_arm_angle_strict pos C
          exact_mod_cast (show i.1<j.1 from ij)
        exact (((sm i).continuousAt.tendsto.eventually_lt (sm j).continuousAt.tendsto lt)).mono (fun _ e _ => e)
      · exact Eventually.of_forall (fun _ h => (ij h).elim)
    have h := eventually_all.mpr (fun i => eventually_all.mpr (pair i))
    exact h.mono (fun _ eq i j ij => eq i j ij)
  have inner : ∀ᶠ r in 𝓝 (0:ℝ), ∀ i, φ i r∈Ioo b (b+2*Real.pi) :=
    eventually_all.mpr fun i => (sm i).continuousAt.eventually (isOpen_Ioo.mem_nhds (by rw [center i]; exact contact_arm_inside_period pos C i))
  filter_upwards [hu,ordered,inner,eventually_all.mpr rooted] with r hr order bounds roots
  refine ⟨order,bounds,?_⟩
  intro θ hθ
  have member : (r,θ)∈S := sub (show (r,θ)∈U ×ˢ V from ⟨hr,subset_of_mem_nhdsSet hv hθ⟩)
  refine ⟨member,?_⟩
  rintro ⟨i,rfl⟩
  exact roots i

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_angular_zero_branches
