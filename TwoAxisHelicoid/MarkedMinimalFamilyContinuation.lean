import TwoAxisHelicoid.MarkedPlaneFamilyTopology
import TwoAxisHelicoid.RegularMinimalLimitContact
import TwoAxisHelicoid.ConnectedImmersionInjectivity
import TwoAxisHelicoid.PuncturedCurveNoncompact
import TwoAxisHelicoid.OpenPuncturedCoreConnectivity
import TwoAxisHelicoid.PeriodTorusComplexManifold

namespace TwoAxisHelicoid
open Complex Set Filter Topology InnerProductSpace
open scoped Topology

/-- A real analytic family of harmonic conformal immersions of a fixed
punctured torus stays embedded in the sense of injectivity as long as
all possible double points lie locally in uniformly compact cores. -/
theorem marked_minimal_family_injectivity_continuation (L : PeriodPair) (Y : ℝ → PuncturedPeriodTorus L → Fin 3 → ℝ)
    (joint : ∀ t z, z ∉ L.lattice → AnalyticAt ℝ (fun p : ℝ × ℂ => puncturedTorusPullback L (Y p.1) p.2) (t,z))
    (reg : ∀ t z, z ∉ L.lattice → (∀ j, HarmonicAt (fun w => puncturedTorusPullback L (Y t) w j) z) ∧
      ConformalCoordinateDerivatives (puncturedTorusPullback L (Y t)) z ∧ Function.Injective (fderiv ℝ (puncturedTorusPullback L (Y t)) z))
    (tight : ∀ t : ℝ, ∃ K : Set (PuncturedPeriodTorus L × PuncturedPeriodTorus L), IsCompact K ∧
      ∀ᶠ s in 𝓝 t, immersionDoublePoints (Y s) ⊆ K) {t₀ : ℝ} (inj : Function.Injective (Y t₀)) :
    ∀ t, Function.Injective (Y t) := by
  let _ := punctured_torus_is_path_connected L
  let _ := punctured_complex_curve_noncompact (0:PeriodTorus L)
  apply connected_family_injective_of_coincident_contacts Y (marked_family_joint_continuous L Y (fun t z hz => (joint t z hz).continuousAt))
    (marked_family_uniform_local_injectivity L Y joint (fun t z hz => (reg t z hz).2.2)) tight _ inj
  intro t freq x y neq same V hV
  obtain ⟨a,rfl⟩ := puncturedPlaneProjection_surjective L x
  obtain ⟨b,rfl⟩ := puncturedPlaneProjection_surjective L y
  let π := finiteTorusProjection L (puncturedPlaneProjection L a)
  let F := fun p : ℝ × ℂ => puncturedTorusPullback L (Y p.1) p.2
  have val (z : ℂ) (hz : z ∉ L.lattice) (s : ℝ) : F (s,z)=Y s (π z) := by
    simp only [F,π,puncturedTorusPullback,finiteTorusProjection,dite_eq_left hz]
  have proj (z : PuncturedLatticePlane L) : π z.1=puncturedPlaneProjection L z := by simp [π,finiteTorusProjection,z.2]
  obtain ⟨A,B,hA,hB,am,bm,dis⟩ := t2_separation neq
  let U := π ⁻¹' A ∩ (L.lattice : Set ℂ)ᶜ
  let W := π ⁻¹' (B ∩ V) ∩ (L.lattice : Set ℂ)ᶜ
  have nu : U ∈ 𝓝 a.1 := inter_mem (show A ∈ map π (𝓝 a.1) by rw [finiteTorusProjection_map_nhds _ _ a.2]; exact hA.mem_nhds am)
    (L.isClosed_lattice.isOpen_compl.mem_nhds a.2)
  have nw : W ∈ 𝓝 b.1 := inter_mem (show B ∩ V ∈ map π (𝓝 b.1) by rw [finiteTorusProjection_map_nhds _ _ b.2]; exact inter_mem (hB.mem_nhds bm) hV)
    (L.isClosed_lattice.isOpen_compl.mem_nhds b.2)
  have sep : ∃ᶠ s in 𝓝 t, ∀ u ∈ U, ∀ v ∈ W, F (s,u) ≠ F (s,v) := freq.mono (by
    intro s hi u hu v hv eq
    rw [val u hu.2 s,val v hv.2 s] at eq
    have e := hi eq
    exact Set.disjoint_left.mp dis hu.1 (e ▸ hv.1.1))
  have pReg (c : PuncturedLatticePlane L) : ∀ᶠ u in 𝓝 c.1, (∀ j, HarmonicAt (fun z => F (t,z) j) u) ∧
      ConformalCoordinateDerivatives (fun z => F (t,z)) u :=
    Filter.mem_of_superset (L.isClosed_lattice.isOpen_compl.mem_nhds c.2) fun z hz => ⟨(reg t z hz).1,(reg t z hz).2.1⟩
  have pos : F (t,a.1)=F (t,b.1) := by rw [val _ a.2,val _ b.2,proj,proj]; exact same
  have close := frequent_separation_forces_minimal_sheet_coincidence (F := F)
    (show a.1 ≠ b.1 from fun e => neq (congrArg (puncturedPlaneProjection L) (Subtype.ext e))) pos (joint t a a.2) (joint t b b.2)
    (pReg a) (pReg b) (reg t a a.2).2.2 (reg t b b.2).2.2 nu nw sep
  rw [← finiteTorusProjection_map_nhds L (puncturedPlaneProjection L a) a.2]
  change ∀ᶠ z in 𝓝 a.1, Y t (π z) ∈ Y t '' V
  filter_upwards [close,nu] with z hit hz
  obtain ⟨v,hv,eq⟩ := hit
  exact ⟨π v,hv.1.2,(val v hv.2 t).symm.trans (eq.trans (val z hz.2 t))⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.marked_minimal_family_injectivity_continuation
