import TwoAxisHelicoid.RegularComponentSpinParity
import TwoAxisHelicoid.TiltedPlaneSpinParity
import TwoAxisHelicoid.RegularHeightComponentObstruction
import TwoAxisHelicoid.CountableTiltedCriticalValues

namespace TwoAxisHelicoid
open Set Complex Filter Topology InnerProductSpace
open scoped ContDiff Topology Manifold RealInnerProductSpace

/-- A nonlifting regular plane section at an arbitrary slope gives even
ambient spin in the original spatial coordinates. -/
theorem embedded_torus_even_of_nonlifting_tilted_level (L : PeriodPair)
    (F : PeriodTorus L → Fin 3 → ℝ) (cont : Continuous F) (emb : Function.Injective F)
    (sm : ∀ q≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (imm : ∀ q≠0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (H : PeriodTorus L ≃ₜ Circle×Circle)
    (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    (s : ℂ) {v : ℝ} (distinct : v≠tiltedSpatialHeight s (F 0))
    (reg : ∀ z, tiltedSpatialHeight s (F (periodTorusProjection L z))=v →
      fderiv ℝ ((tiltedSpatialHeight s ∘ F) ∘ periodTorusProjection L) z≠0)
    (x : (tiltedSpatialHeight s ∘ F) ⁻¹' {v})
    (obs : ¬∃ a b : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
      normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2) :
    capAmbientSpinQuadratic L F (1,0)*capAmbientSpinQuadratic L F (0,1)=0 := by
  let A := heightPlaneShear s 1
  let G := A ∘ F
  let h := tiltedSpatialHeight s ∘ F
  let π := periodTorusProjection L
  have heights : (fun q => G q 2)=h := by
    funext q
    change heightPlaneShear s 1 (F q) 2=tiltedSpatialHeight s (F q)
    rw [heightPlaneShear_vertical,one_mul]
    rfl
  have sg (q : PeriodTorus L) (hq : q≠0) : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ G q :=
    A.contDiff.contMDiff.contMDiffAt.comp q (sm q hq)
  have ig (q : PeriodTorus L) (hq : q≠0) : Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) G q) := by
    change Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) (A ∘ F) q)
    rw [mfderiv_comp q A.mdifferentiableAt ((sm q hq).mdifferentiableAt (by simp)),A.mfderiv_eq]
    exact (heightPlaneShear_injective s 1).comp (imm q hq)
  have diff (z : ℂ) (hz : G (π z) 2=v) : DifferentiableAt ℝ (G ∘ π) z := by
    have away : z∉L.lattice := fun mem => distinct (hz.symm.trans
      ((congrArg (fun q => G q 2) ((periodTorusProjection_eq_zero L z).mpr mem)).trans (congrFun heights 0)))
    exact (spatial_torus_lift_regular_at L G away sg ig).1.differentiableAt (by simp)
  have regular (z : ℂ) (hz : G (π z) 2=v) : ∃ w, fderiv ℝ (G ∘ π) z w 2≠0 := by
    have nz := reg z ((congrFun heights (π z)).symm.trans hz)
    let P := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 2
    have eq : h ∘ π=P ∘ (G ∘ π) := funext (fun y => (congrFun heights (π y)).symm)
    by_contra! zero
    apply nz
    change fderiv ℝ (h ∘ π) z=0
    rw [eq,(P.hasFDerivAt.comp z (diff z hz).hasFDerivAt).fderiv]
    exact ContinuousLinearMap.ext zero
  have markedLevel : ∃ x : (fun q => G q 2) ⁻¹' {v}, ¬∃ a b : C(connectedComponent x,ℝ),
      ∀ q : connectedComponent x, normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2 := by
    rw [heights]
    exact ⟨x,obs⟩
  obtain ⟨base,obstruction⟩ := markedLevel
  apply cap_arf_even_of_height_shear L F sm imm s
  exact embedded_torus_even_of_nonlifting_regular_height L G (A.continuous.comp cont)
    ((heightPlaneShear_injective s 1).comp emb) sg ig H marked
    (fun eq => distinct (eq.trans (congrFun heights 0))) regular base obstruction

/-- If a marked obstruction is already carried by a component with
regular height charts, a countable set of exceptional heights and the
filled point's height can both be avoided before applying plane parity. -/
theorem cap_even_of_regular_component_and_countable_critical_values (L : PeriodPair)
    (F : PeriodTorus L → Fin 3 → ℝ) (cont : Continuous F) (emb : Function.Injective F)
    (sm : ∀ q≠0, ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) ∞ F q)
    (imm : ∀ q≠0, Function.Injective (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,Fin 3 → ℝ) F q))
    (H : PeriodTorus L ≃ₜ Circle×Circle)
    (marked : ∀ z, H (periodTorusProjection L z)=planeCircleCoordinates L z)
    (s : ℂ) (v : ℝ) (x : (tiltedSpatialHeight s ∘ F) ⁻¹' {v})
    (charts : ∀ q∈connectedComponent x, ∃ e : OpenPartialHomeomorph (PeriodTorus L) (ℝ×ℝ),
      q.1∈e.source ∧ ∀ w∈e.target, tiltedSpatialHeight s (F (e.symm w))=w.2)
    (obstruct : ¬∃ a b : C(connectedComponent x,ℝ), ∀ q : connectedComponent x,
      normalizedPhase (a q)=(H q.1.1).1 ∧ normalizedPhase (b q)=(H q.1.1).2)
    (count : let f := (tiltedSpatialHeight s ∘ F) ∘ periodTorusProjection L
      (f '' {z | z∉L.lattice ∧ fderiv ℝ f z=0}).Countable) :
    capAmbientSpinQuadratic L F (1,0)*capAmbientSpinQuadratic L F (0,1)=0 := by
  let h := tiltedSpatialHeight s ∘ F
  let f := h ∘ periodTorusProjection L
  let B := f '' {z | z∉L.lattice ∧ fderiv ℝ f z=0}
  have stable := regular_component_height_obstruction_persists ⟨H,H.continuous⟩ h v x charts obstruct
  obtain ⟨u,good,y,obsy⟩ := exists_height_outside_countable (B:=insert (h 0) B) (count.insert _) stable
  have different : u≠h 0 := fun eq => good (Or.inl eq)
  apply embedded_torus_even_of_nonlifting_tilted_level L F cont emb sm imm H marked s different _ y obsy
  intro z hit zero
  have off : z∉L.lattice := fun mem => different (hit.symm.trans (congrArg h ((periodTorusProjection_eq_zero L _).mpr mem)))
  exact good (Or.inr ⟨z,⟨off,zero⟩,hit⟩)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.embedded_torus_even_of_nonlifting_tilted_level
#print axioms TwoAxisHelicoid.cap_even_of_regular_component_and_countable_critical_values
