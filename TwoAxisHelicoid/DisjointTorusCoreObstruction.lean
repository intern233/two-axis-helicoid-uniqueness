import TwoAxisHelicoid.TorusGeneratingCoreModels
import TwoAxisHelicoid.FundamentalCoreBaseChange

namespace TwoAxisHelicoid
open Complex Set Topology

noncomputable def TorusGeneratingCoreModel.transportedClass {A L : PeriodPair} (C : TorusGeneratingCoreModel A)
    (f : C.carrier → PeriodTorus L) (hf : Continuous f) (i : Fin 2) : FundamentalGroup (PeriodTorus L) (f C.base) :=
  .fromPath (.mk ((C.loop i).map hf))

private theorem first_generator_nontrivial (A : PeriodPair) : periodTorusGeneratorClass A 0 ≠ 1 := by
  intro h
  have e := periodTorusGeneratorClass_coordinates A 0
  rw [h,map_one,ite_eq_left rfl] at e
  have he := congrArg (fun x : Multiplicative (ℤ × ℤ) => x.toAdd.1) e
  norm_num at he

/-- A single open genus-one core detects every loop in the ambient closed
torus, even based in another sheet, and its concrete pair generates the
whole integral fundamental group. -/
theorem TorusGeneratingCoreModel.ambient_detection {A L : PeriodPair} (C : TorusGeneratingCoreModel A)
    (f : C.carrier → PeriodTorus L) (hf : IsOpenEmbedding f) :
    ∃ F : C(PeriodTorus L,PeriodTorus A), (∀ y ∉ range f, F y = 0) ∧
      (∀ y, Function.Injective (FundamentalGroup.map F y)) ∧
      (∀ v : FundamentalGroup (PeriodTorus L) (f C.base), ∃ m n : ℤ,
        v = C.transportedClass f hf.continuous 0 ^ m * C.transportedClass f hf.continuous 1 ^ n) ∧
      C.transportedClass f hf.continuous 0 ≠ 1 := by
  obtain ⟨F,hF,ho⟩ := C.detect L f hf
  have hb : F (f C.base) = (puncturedTorusCenter A).1 := by
    simpa using (hF 0 0).trans (C.projects 0 0)
  let g := C.transportedClass f hf.continuous
  let u := FundamentalGroup.mapOfEq F hb
  have hU (i : Fin 2) : u (g i) = periodTorusGeneratorClass A i := by
    rw [show u (g i) = _ from fundamental_mapOfEq_loop F hb ((C.loop i).map hf.continuous)]
    apply congrArg FundamentalGroup.fromPath
    apply congrArg Path.Homotopic.Quotient.mk
    ext s
    exact (hF i s).trans (C.projects i s)
  have transport (q : PeriodTorus L) (a : Fin 2 → FundamentalGroup (PeriodTorus L) q)
      (v : FundamentalGroup (PeriodTorus L) q →* FundamentalGroup (PeriodTorus A) (puncturedTorusCenter A).1)
      (h : ∀ i, v (a i) = periodTorusGeneratorClass A i) :
      (∀ x, ∃ m n : ℤ, x = a 0^m*a 1^n) ∧ ∀ x, v x = 1 → x = 1 := by
    obtain ⟨z,rfl⟩ := (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)) q
    exact detecting_map_forces_generators_and_trivial_complement L A z a v h
  have e := transport _ g u hU
  have hinj := injective_fundamental_map_of_mapOfEq F hb ((injective_iff_map_eq_one u).mpr e.2)
  let : PathConnectedSpace (PeriodTorus L) :=
    (Quotient.mk_surjective : Function.Surjective (periodTorusProjection L)).pathConnectedSpace QuotientAddGroup.continuous_mk
  refine ⟨F,ho,fun y => fundamental_map_injective_along_path F (PathConnectedSpace.somePath y (f C.base)) hinj,e.1,?_⟩
  intro h
  exact first_generator_nontrivial A ((hU 0).symm.trans ((congrArg u h).trans u.map_one))

/-- Two disjoint open genus-one cores cannot occur in a surface whose
compactification is a marked torus. This is the sheet exclusion used by
the original Appendix B compactness proof. -/
theorem disjoint_genus_one_cores_impossible {A B L : PeriodPair}
    (C : TorusGeneratingCoreModel A) (D : TorusGeneratingCoreModel B)
    (f : C.carrier → PeriodTorus L) (g : D.carrier → PeriodTorus L)
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) : ¬ Disjoint (range f) (range g) := by
  intro hdisj
  obtain ⟨F,hout,hinj,_,_⟩ := C.ambient_detection f hf
  obtain ⟨_,_,_,_,hn⟩ := D.ambient_detection g hg
  have hF (x : D.carrier) : F (g x) = 0 := hout _ (fun h => Set.disjoint_left.mp hdisj h ⟨x,rfl⟩)
  have e : (((D.loop 0).map hg.continuous).map F.continuous) = Path.refl (F (g D.base)) := by
    ext s
    exact (hF (D.loop 0 s)).trans (hF D.base).symm
  apply hn
  apply hinj (g D.base)
  rw [map_one]
  change FundamentalGroup.fromPath (.mk (((D.loop 0).map hg.continuous).map F.continuous)) = _
  rw [e]
  rfl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.disjoint_genus_one_cores_impossible
