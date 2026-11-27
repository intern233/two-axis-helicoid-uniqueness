import TwoAxisHelicoid.TorusManifoldC1Path

namespace TwoAxisHelicoid
open Complex Set
open scoped Manifold

namespace ComplexPeriodArc

variable {L : PeriodPair} (a : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ)

def start : PuncturedPeriodTorus L :=
  puncturedPlaneProjection L ⟨a.curve a.left,a.stays ⟨le_rfl,a.ordered⟩⟩

def finish : PuncturedPeriodTorus L :=
  puncturedPlaneProjection L ⟨a.curve a.right,a.stays ⟨a.ordered,le_rfl⟩⟩

def time (s : unitInterval) : ℝ := AffineMap.lineMap a.left a.right (s:ℝ)

theorem time_mem (s : unitInterval) : a.time s ∈ Icc a.left a.right :=
  (convex_Icc _ _).lineMap_mem ⟨le_rfl,a.ordered⟩ ⟨a.ordered,le_rfl⟩ s.property

noncomputable def projected : Path a.start a.finish := by
  let f (s : unitInterval) : PuncturedLatticePlane L := ⟨a.curve (a.time s),a.stays (a.time_mem s)⟩
  have ht : Continuous a.time := AffineMap.lineMap_continuous.comp continuous_subtype_val
  have hcont : Continuous f := (a.continuous_curve.comp_continuous ht a.time_mem).subtype_mk _
  exact {
    toFun := puncturedPlaneProjection L ∘ f
    continuous_toFun := (puncturedPlaneProjection_continuous L).comp hcont
    source' := Subtype.ext (by simp [f,start,time,puncturedPlaneProjection])
    target' := Subtype.ext (by simp [f,finish,time,puncturedPlaneProjection]) }

end ComplexPeriodArc

/-- Line integral on a genuine path in the punctured torus, computed in
lattice charts. At a corner, lifts of consecutive arcs need only agree in
the quotient. The arc constructor records the complete projected path. -/
inductive TorusPathIntegral (L : PeriodPair) (f : ℂ → ℂ) :
    {q r : PuncturedPeriodTorus L} → Path q r → ℂ → Prop
  | refl (q : PuncturedPeriodTorus L) : TorusPathIntegral L f (Path.refl q) 0
  | arc {q r : PuncturedPeriodTorus L} (γ : Path q r) (a : ComplexPeriodArc (L.lattice : Set ℂ)ᶜ)
      (h : ∀ s, (γ s).1 = periodTorusProjection L (a.curve (a.time s))) :
      TorusPathIntegral L f γ (a.integral f)
  | trans {p q r : PuncturedPeriodTorus L} {γ : Path p q} {δ : Path q r} {v w : ℂ} :
      TorusPathIntegral L f γ v → TorusPathIntegral L f δ w → TorusPathIntegral L f (γ.trans δ) (v+w)

theorem TorusPathIntegral.cast {L : PeriodPair} {f : ℂ → ℂ} {q r q' r' : PuncturedPeriodTorus L}
    {γ : Path q r} {v : ℂ} (h : TorusPathIntegral L f γ v) (hq : q' = q) (hr : r' = r) :
    TorusPathIntegral L f (γ.cast hq hr) v := by
  subst q' r'
  simpa using h

theorem PiecewiseComplexPath.projected_hasIntegral {L : PeriodPair} {x y : ℂ}
    (p : PiecewiseComplexPath (L.lattice : Set ℂ)ᶜ x y) (f : ℂ → ℂ) :
    ∃ (hx : x ∉ L.lattice) (hy : y ∉ L.lattice)
      (γ : Path (puncturedPlaneProjection L ⟨x,hx⟩) (puncturedPlaneProjection L ⟨y,hy⟩)),
      TorusPathIntegral L f γ (p.integral f) := by
  induction p with
  | refl z hz => exact ⟨hz,hz,_,.refl _⟩
  | arc a => exact ⟨a.stays ⟨le_rfl,a.ordered⟩,a.stays ⟨a.ordered,le_rfl⟩,
      a.projected,.arc _ a (fun _ => rfl)⟩
  | trans p q hp hq =>
    obtain ⟨hx,hy,γ,hγ⟩ := hp
    obtain ⟨_,hz,δ,hδ⟩ := hq
    exact ⟨hx,hz,γ.trans δ,.trans hγ hδ⟩

theorem torus_manifold_C1_path_has_integral {L : PeriodPair} {q r : PuncturedPeriodTorus L}
    (f : ℂ → ℂ) (γ : Path q r) (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, ℂ) 1 γ.extend (Icc (0:ℝ) 1)) :
    ∃ v, TorusPathIntegral L f γ v := by
  obtain ⟨x,hx⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) q.1
  obtain ⟨a,h0,h1,_,he⟩ := punctured_torus_path_exists_C1_lift L γ
    (torusPathC1_of_contMDiffOn γ hγ) hx
  refine ⟨_,.arc γ a (fun s => ?_)⟩
  have hs : a.time s = s := by simp [ComplexPeriodArc.time,h0,h1,AffineMap.lineMap_apply]
  rw [hs,he s s.property,γ.extend_extends']
  
theorem TorusPathIntegral.real_primitive {L : PeriodPair} {f : ℂ → ℂ} {X : ℂ → ℝ}
    (hf : ContinuousOn f (L.lattice : Set ℂ)ᶜ)
    (hX : ∀ z ∉ L.lattice, HasFDerivAt X (realCoefficientDerivative (f z)) z)
    (hp : ∀ z ω, ω ∈ L.lattice → X (z+ω) = X z)
    {q r : PuncturedPeriodTorus L} {γ : Path q r} {v : ℂ} (h : TorusPathIntegral L f γ v) :
    v.re = periodTorusLift L X hp r.1-periodTorusLift L X hp q.1 := by
  induction h with
  | refl => simp
  | trans _ _ h₁ h₂ => simp only [add_re,h₁,h₂]; ring
  | arc γ a he =>
    have hs := he 0
    have ht := he 1
    simp only [γ.source,γ.target,ComplexPeriodArc.time,Set.Icc.coe_zero,Set.Icc.coe_one,
      AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] at hs ht
    rw [ht,hs]
    exact a.integral_re_eq_sub hf hX

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.torus_manifold_C1_path_has_integral
#print axioms TwoAxisHelicoid.TorusPathIntegral.real_primitive
