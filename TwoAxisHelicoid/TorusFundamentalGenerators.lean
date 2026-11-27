import TwoAxisHelicoid.SpinGeneratorHolonomy
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

namespace TwoAxisHelicoid
open Complex Set Topology

theorem periodTorusProjection_isAddQuotientCoveringMap (L : PeriodPair) :
    IsAddQuotientCoveringMap (periodTorusProjection L) L.lattice := by
  have hd : IsDiscrete (L.lattice.toAddSubgroup : Set ℂ) :=
    isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology L.lattice))
  exact L.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm hd

/-- The actual lattice projection computes the compact torus fundamental
group. The isomorphism records the endpoint displacement of a plane lift. -/
noncomputable def periodTorusFundamentalGroupEquiv (L : PeriodPair) (z : ℂ) :
    FundamentalGroup (PeriodTorus L) (periodTorusProjection L z) ≃* Multiplicative (ℤ × ℤ) :=
  (((periodTorusProjection_isAddQuotientCoveringMap L).fundamentalGroupEquiv ⟨z,rfl⟩).trans
    MulOpposite.opMulEquiv.symm).trans L.latticeEquivProd.toAddEquiv.toMultiplicative

theorem periodTorusFundamentalGroupEquiv_of_lift (L : PeriodPair) (z : ℂ)
    (γ : Path (periodTorusProjection L z) (periodTorusProjection L z))
    (f : C(unitInterval,ℂ)) (hf : periodTorusProjection L ∘ f = γ)
    (h0 : f 0 = z) (ω₀ : L.lattice) (h1 : f 1 = z+ω₀.1) :
    periodTorusFundamentalGroupEquiv L z (.of (.mk γ)) =
      Multiplicative.ofAdd (L.latticeEquivProd ω₀) := by
  have h : (periodTorusProjection_isAddQuotientCoveringMap L).fundamentalGroupEquiv
      ⟨z,rfl⟩ (.of (.mk γ)) = MulOpposite.op (Multiplicative.ofAdd ω₀) := by
    apply (periodTorusProjection_isAddQuotientCoveringMap L).fundamentalGroupToMulOpposite_apply_mk_eq hf h0
    change f 1 = ω₀.1+z
    rw [h1,add_comm]
  simp only [periodTorusFundamentalGroupEquiv,MulEquiv.trans_apply,h]
  rfl

noncomputable def periodTorusGeneratorClass (L : PeriodPair) (i : Fin 2) :
    FundamentalGroup (PeriodTorus L) (puncturedTorusCenter L).1 :=
  .of (.mk ((puncturedTorusGeneratorLoop L i).map continuous_subtype_val))

noncomputable def periodTorusBasedFundamentalGroupEquiv (L : PeriodPair) :
    FundamentalGroup (PeriodTorus L) (puncturedTorusCenter L).1 ≃* Multiplicative (ℤ × ℤ) :=
  periodTorusFundamentalGroupEquiv L (periodBasisLine L 0 0)

/-- The two closed curves already used for the spin lifts give the two
standard generators of the genuine fundamental group of the compact torus. -/
theorem periodTorusGeneratorClass_coordinates (L : PeriodPair) (i : Fin 2) :
    periodTorusBasedFundamentalGroupEquiv L (periodTorusGeneratorClass L i) =
      Multiplicative.ofAdd (if i = 0 then (1,0) else (0,1)) := by
  let f : C(unitInterval,ℂ) := ⟨fun s => periodBasisLine L i s,
    (continuous_subtype_val.comp (puncturedBasisLine_continuous L i)).comp continuous_subtype_val⟩
  have h0 : f 0 = periodBasisLine L 0 0 := by simp [f,periodBasisLine]
  have h1 : f 1 = periodBasisLine L 0 0+(periodGeneratorPeriod L i).1 := by
    simp [f,periodBasisLine,periodGeneratorPeriod_val]
  have h := periodTorusFundamentalGroupEquiv_of_lift L (periodBasisLine L 0 0)
    ((puncturedTorusGeneratorLoop L i).map continuous_subtype_val) f rfl h0
      (periodGeneratorPeriod L i) h1
  simpa only [periodTorusBasedFundamentalGroupEquiv,periodTorusGeneratorClass,
    periodGeneratorPeriod,L.latticeEquivProd.apply_symm_apply] using! h

theorem periodTorusFundamentalGroup_generated (L : PeriodPair)
    (γ : FundamentalGroup (PeriodTorus L) (puncturedTorusCenter L).1) :
    ∃ n m : ℤ, γ = periodTorusGeneratorClass L 0^n*periodTorusGeneratorClass L 1^m := by
  let e := periodTorusBasedFundamentalGroupEquiv L
  let p := (e γ).toAdd
  refine ⟨p.1,p.2,e.injective ?_⟩
  rw [map_mul,map_zpow,map_zpow]
  change e γ =
    (periodTorusBasedFundamentalGroupEquiv L (periodTorusGeneratorClass L 0))^p.1 *
    (periodTorusBasedFundamentalGroupEquiv L (periodTorusGeneratorClass L 1))^p.2
  rw [periodTorusGeneratorClass_coordinates,periodTorusGeneratorClass_coordinates]
  apply Multiplicative.toAdd.injective
  change p = _
  simp

end TwoAxisHelicoid

#print axioms TwoAxisHelicoid.periodTorusGeneratorClass_coordinates
#print axioms TwoAxisHelicoid.periodTorusFundamentalGroup_generated
