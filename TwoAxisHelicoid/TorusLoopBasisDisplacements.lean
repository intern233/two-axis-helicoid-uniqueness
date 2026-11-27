import TwoAxisHelicoid.TorusFundamentalGenerators

namespace TwoAxisHelicoid
open Complex Set Topology

/-- A global torus homeomorphism transports all loop classes onto the target
fundamental group. -/
theorem fundamentalGroup_map_surjective_of_homeomorph {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (e : S ≃ₜ T) (x : S) : Function.Surjective (FundamentalGroup.map (⟨e,e.continuous⟩ : C(_, _)) x) := by
  intro g
  obtain ⟨γ,hγ⟩ := Quotient.exists_rep g.asHom
  let p := (γ.map e.symm.continuous).cast (e.symm_apply_apply x).symm (e.symm_apply_apply x).symm
  have he : p.map e.continuous = γ := by
    ext t
    change e (e.symm (γ t)) = γ t
    exact e.apply_symm_apply _
  exact ⟨.of (.mk p),show FundamentalGroup.fromPath (.mk (p.map e.continuous)) = g from
    by rw [he]; exact congrArg FundamentalGroup.fromPath hγ⟩

/-- The deck displacements of arbitrary lifted generating loops span the whole
integer lattice. No preselected normal form or intersection pairing of
the new loops is assumed. -/
theorem torus_generating_loops_span_deck (L : PeriodPair) (z : ℂ)
    (γ : Fin 2 → Path (periodTorusProjection L z) (periodTorusProjection L z))
    (f : Fin 2 → C(unitInterval,ℂ)) (ω : Fin 2 → L.lattice)
    (hf : ∀ i, periodTorusProjection L ∘ f i = γ i) (h0 : ∀ i, f i 0 = z)
    (h1 : ∀ i, f i 1 = z+(ω i).1)
    (hg : ∀ g : FundamentalGroup (PeriodTorus L) (periodTorusProjection L z),
      ∃ m n : ℤ, g = (FundamentalGroup.fromPath (.mk (γ 0)))^m * (FundamentalGroup.fromPath (.mk (γ 1)))^n) :
    ∀ u ∈ L.lattice, ∃ m n : ℤ, u = (m:ℂ)*(ω 0).1+(n:ℂ)*(ω 1).1 := by
  intro u hu
  let e := periodTorusFundamentalGroupEquiv L z
  let v : L.lattice := ⟨u,hu⟩
  let g := e.symm (Multiplicative.ofAdd (L.latticeEquivProd v))
  obtain ⟨m,n,hg'⟩ := hg g
  have hf' i : e (FundamentalGroup.fromPath (.mk (γ i))) = Multiplicative.ofAdd (L.latticeEquivProd (ω i)) :=
    periodTorusFundamentalGroupEquiv_of_lift L z (γ i) (f i) (hf i) (h0 i) (ω i) (h1 i)
  have he := congrArg e hg'
  simp only [g,MulEquiv.apply_symm_apply,map_mul,map_zpow,hf'] at he
  have hcoord := congrArg Multiplicative.toAdd he
  have hsum : v = m • ω 0 + n • ω 1 := L.latticeEquivProd.injective (by
    rw [map_add,map_zsmul,map_zsmul]; exact hcoord)
  refine ⟨m,n,?_⟩
  simpa only [Submodule.coe_add,Submodule.coe_smul_of_tower,zsmul_eq_mul] using congrArg Subtype.val hsum

/-- The two intrinsic generators of one compact torus also generate after
transport through any homeomorphism to a second compact torus. -/
theorem torus_transported_generator_classes (A L : PeriodPair) (e : PeriodTorus A ≃ₜ PeriodTorus L)
    (g : FundamentalGroup (PeriodTorus L) (e (puncturedTorusCenter A).1)) :
    ∃ m n : ℤ, g = (FundamentalGroup.map (⟨e,e.continuous⟩ : C(_, _)) _ (periodTorusGeneratorClass A 0))^m *
      (FundamentalGroup.map (⟨e,e.continuous⟩ : C(_, _)) _ (periodTorusGeneratorClass A 1))^n := by
  obtain ⟨g',rfl⟩ := fundamentalGroup_map_surjective_of_homeomorph e _ g
  obtain ⟨m,n,hg⟩ := periodTorusFundamentalGroup_generated A g'
  exact ⟨m,n,by rw [hg,map_mul,map_zpow,map_zpow]⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.torus_generating_loops_span_deck
#print axioms TwoAxisHelicoid.torus_transported_generator_classes
