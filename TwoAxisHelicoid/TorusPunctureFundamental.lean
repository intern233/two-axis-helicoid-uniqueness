import TwoAxisHelicoid.TorusFundamentalGenerators

namespace TwoAxisHelicoid

noncomputable def puncturedTorusGeneratorClass (L : PeriodPair) (i : Fin 2) :
    FundamentalGroup (PuncturedPeriodTorus L) (puncturedTorusCenter L) :=
  .of (.mk (puncturedTorusGeneratorLoop L i))

noncomputable def puncturedTorusFundamentalInclusion (L : PeriodPair) :
    FundamentalGroup (PuncturedPeriodTorus L) (puncturedTorusCenter L) →*
      FundamentalGroup (PeriodTorus L) (puncturedTorusCenter L).1 :=
  FundamentalGroup.map ⟨Subtype.val,continuous_subtype_val⟩ (puncturedTorusCenter L)

theorem puncturedTorusFundamentalInclusion_generator (L : PeriodPair) (i : Fin 2) :
    puncturedTorusFundamentalInclusion L (puncturedTorusGeneratorClass L i) =
      periodTorusGeneratorClass L i := rfl

/-- Every compact-torus loop class is represented by a loop avoiding
the puncture; this is proved from the actual two generator loops. -/
theorem puncturedTorusFundamentalInclusion_surjective (L : PeriodPair) :
    Function.Surjective (puncturedTorusFundamentalInclusion L) := by
  intro γ
  obtain ⟨n,m,he⟩ := periodTorusFundamentalGroup_generated L γ
  refine ⟨puncturedTorusGeneratorClass L 0^n*puncturedTorusGeneratorClass L 1^m,?_⟩
  rw [map_mul,map_zpow,map_zpow,puncturedTorusFundamentalInclusion_generator,
    puncturedTorusFundamentalInclusion_generator]
  exact he.symm

/-- In particular a monodromy homomorphism on the compact torus has at
most one extension from its restriction to the punctured torus. This is
only the group-theoretic part of spin-extension uniqueness. -/
theorem torus_monodromy_unique_of_punctured_restriction (L : PeriodPair)
    {G : Type*} [Group G]
    (f g : FundamentalGroup (PeriodTorus L) (puncturedTorusCenter L).1 →* G)
    (he : f.comp (puncturedTorusFundamentalInclusion L) =
      g.comp (puncturedTorusFundamentalInclusion L)) : f = g := by
  ext γ
  obtain ⟨γ',rfl⟩ := puncturedTorusFundamentalInclusion_surjective L γ
  exact congrArg (fun h => h γ') he

theorem torus_monodromy_determined_by_two_generators (L : PeriodPair)
    {G : Type*} [Group G]
    (f g : FundamentalGroup (PeriodTorus L) (puncturedTorusCenter L).1 →* G)
    (h0 : f (periodTorusGeneratorClass L 0) = g (periodTorusGeneratorClass L 0))
    (h1 : f (periodTorusGeneratorClass L 1) = g (periodTorusGeneratorClass L 1)) : f = g := by
  ext γ
  obtain ⟨n,m,rfl⟩ := periodTorusFundamentalGroup_generated L γ
  rw [map_mul,map_mul,map_zpow,map_zpow,map_zpow,map_zpow,h0,h1]

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.puncturedTorusFundamentalInclusion_surjective
#print axioms TwoAxisHelicoid.torus_monodromy_unique_of_punctured_restriction
