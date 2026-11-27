import TwoAxisHelicoid.CompactCoreReflectionContinuity
import TwoAxisHelicoid.UnmarkedReflectionCompactCore
import TwoAxisHelicoid.CoordinateSignMaps
import TwoAxisHelicoid.SimilaritySymmetry

namespace TwoAxisHelicoid
open Set Filter Matrix Complex Topology
open scoped Topology ContDiff

/-- The induced slice reflections on a once-punctured torus are pointwise
continuous in time at a proper central slice. The image assumptions on
the nearby slices are purely setwise. -/
theorem unmarked_punctured_torus_reflections_lift {M E : Type*} [TopologicalSpace M] [T2Space M]
    [MetricSpace E] [ProperSpace E] (o : E) {A : PeriodPair} (mark : M ≃ₜ PuncturedPeriodTorus A)
    {X : ℝ → M → E} (joint : ∀ z, ContinuousAt (fun a : ℝ × M => X a.1 a.2) (0,z))
    (proper : IsProperMap (X 0)) (emb : ∀ᶠ s in 𝓝 (0:ℝ), IsEmbedding (X s))
    {R : E → E} (cont : Continuous R) (inv : Function.Involutive R)
    (symmetric : ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, R (X s p) ∈ range (X s)) :
    ∃ d : ℝ → M ≃ₜ M, (∀ p, ContinuousAt (fun s => d s p) 0) ∧
      ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, X s (d s p) = R (X s p) :=
  compact_core_unmarked_reflections_lift o (punctured_torus_compact_core_meets_images mark)
    joint proper emb cont inv symmetric

/-- Oddness of the true normal velocity of an unmarked family. The
central proper slice and the topology of its handle supply the continuous
parameters of the reflected points. -/
theorem punctured_torus_unmarked_reflection_velocity {M : Type*} [TopologicalSpace M] [T2Space M]
    {A : PeriodPair} (mark : M ≃ₜ PuncturedPeriodTorus A) (X : ℝ → M → Fin 3 → ℝ)
    (proper : IsProperMap (X 0))
    (emb : ∀ᶠ s in 𝓝 (0:ℝ), IsEmbedding (X s))
    (e : M → OpenPartialHomeomorph M ℂ) (center : ∀ p, p ∈ (e p).source)
    (smooth : ∀ p, ContDiffAt ℝ ∞ (fun a : ℝ × ℂ => X a.1 ((e p).symm a.2)) (0,e p p))
    (imm : ∀ p, Function.Injective (fderiv ℝ (X 0 ∘ (e p).symm) (e p p)))
    (N : M → Fin 3 → ℝ) (normal : ∀ p h, fderiv ℝ (X 0 ∘ (e p).symm) (e p p) h ⬝ᵥ N p = 0)
    (R : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (inv : Function.Involutive R)
    (orth : ∀ a b, R a ⬝ᵥ R b = a ⬝ᵥ b)
    (sym : ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, R (X s p) ∈ range (X s))
    (sign : ∀ p q, X 0 q = R (X 0 p) → N q = -R (N p)) :
    let u := fun p => deriv (fun s => X s p) 0 ⬝ᵥ N p
    ∃ ρ : M ≃ₜ M, (∀ p, X 0 (ρ p) = R (X 0 p)) ∧
      (∀ p, u (ρ p) = -u p) ∧ (∀ p, R (X 0 p) = X 0 p → u p = 0) :=
  compact_core_unmarked_reflection_velocity (punctured_torus_compact_core_meets_images mark)
    X proper emb e center smooth imm N normal R inv orth sym sign

/-- Manuscript D.2, with the actual two Euclidean half-turns and the
normal component of the derivative of the original family. -/
theorem punctured_torus_fixed_axes_normal_velocity_odd {M : Type*} [TopologicalSpace M] [T2Space M]
    {A : PeriodPair} (mark : M ≃ₜ PuncturedPeriodTorus A) (X : ℝ → M → Fin 3 → ℝ)
    (proper : IsProperMap (X 0))
    (emb : ∀ᶠ s in 𝓝 (0:ℝ), IsEmbedding (X s))
    (e : M → OpenPartialHomeomorph M ℂ) (center : ∀ p, p ∈ (e p).source)
    (smooth : ∀ p, ContDiffAt ℝ ∞ (fun a : ℝ × ℂ => X a.1 ((e p).symm a.2)) (0,e p p))
    (imm : ∀ p, Function.Injective (fderiv ℝ (X 0 ∘ (e p).symm) (e p p)))
    (N : M → Fin 3 → ℝ) (normal : ∀ p h, fderiv ℝ (X 0 ∘ (e p).symm) (e p p) h ⬝ᵥ N p = 0)
    (sym : ∀ᶠ s in 𝓝 (0:ℝ), ∀ p, halfTurnX (X s p) ∈ range (X s) ∧ halfTurnZ (X s p) ∈ range (X s))
    (signX : ∀ p q, X 0 q = halfTurnX (X 0 p) → N q = -halfTurnX (N p))
    (signZ : ∀ p q, X 0 q = halfTurnZ (X 0 p) → N q = -halfTurnZ (N p)) :
    let u := fun p => deriv (fun s => X s p) 0 ⬝ᵥ N p
    ∃ ρX ρZ : M ≃ₜ M, ∀ p, X 0 (ρX p) = halfTurnX (X 0 p) ∧ X 0 (ρZ p) = halfTurnZ (X 0 p) ∧
      u (ρX p) = -u p ∧ u (ρZ p) = -u p ∧
      (halfTurnX (X 0 p) = X 0 p ∨ halfTurnZ (X 0 p) = X 0 p → u p = 0) := by
  intro u
  let A₁ := coordinateSignMap (![1,-1,-1] : Fin 3 → ℝ)
  let A₂ := coordinateSignMap (![-1,-1,1] : Fin 3 → ℝ)
  have hx (v : Fin 3 → ℝ) : A₁ v = halfTurnX v := by ext i; fin_cases i <;> simp [A₁,halfTurnX]
  have hz (v : Fin 3 → ℝ) : A₂ v = halfTurnZ v := by ext i; fin_cases i <;> simp [A₂,halfTurnZ]
  have ix : Function.Involutive A₁ := coordinateSignMap_involutive (by intro i; fin_cases i <;> norm_num)
  have iz : Function.Involutive A₂ := coordinateSignMap_involutive (by intro i; fin_cases i <;> norm_num)
  have ox (v w : Fin 3 → ℝ) : A₁ v ⬝ᵥ A₁ w = v ⬝ᵥ w := by
    simp [hx,halfTurnX,dotProduct,Fin.sum_univ_succ]
  have oz (v w : Fin 3 → ℝ) : A₂ v ⬝ᵥ A₂ w = v ⬝ᵥ w := by
    simp [hz,halfTurnZ,dotProduct,Fin.sum_univ_succ]
  obtain ⟨rx,ax,ux,zx⟩ := punctured_torus_unmarked_reflection_velocity mark X proper emb e center
    smooth imm N normal A₁ ix ox (sym.mono fun _ h p => by simpa only [hx] using (h p).1)
    (fun p q eq => (signX p q (eq.trans (hx _))).trans (congrArg Neg.neg (hx _).symm))
  obtain ⟨rz,az,uz,zz⟩ := punctured_torus_unmarked_reflection_velocity mark X proper emb e center
    smooth imm N normal A₂ iz oz (sym.mono fun _ h p => by simpa only [hz] using (h p).2)
    (fun p q eq => (signZ p q (eq.trans (hz _))).trans (congrArg Neg.neg (hz _).symm))
  refine ⟨rx,rz,fun p => ⟨(ax p).trans (hx _),(az p).trans (hz _),ux p,uz p,?_⟩⟩
  exact fun h => h.elim (fun f => zx p ((hx _).trans f)) (fun f => zz p ((hz _).trans f))

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.unmarked_punctured_torus_reflections_lift
#print axioms TwoAxisHelicoid.punctured_torus_unmarked_reflection_velocity
#print axioms TwoAxisHelicoid.punctured_torus_fixed_axes_normal_velocity_odd
