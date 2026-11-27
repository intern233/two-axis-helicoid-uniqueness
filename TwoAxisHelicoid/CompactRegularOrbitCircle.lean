import TwoAxisHelicoid.PlaneOrientationCircleDegree
import TwoAxisHelicoid.ConjugateLatticeRealBasis

namespace TwoAxisHelicoid
open Set Function Topology

/-- A locally open real flow on a compact connected level curve has a
primitive positive period. Time modulo that period parametrizes the curve
homeomorphically. Only the elementary action laws enter this statement. -/
theorem compact_open_orbit_circle {C : Type*} [TopologicalSpace C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] (Φ : ℝ → C → C) (x : C)
    (zero : ∀ y, Φ 0 y=y) (add : ∀ a b y, Φ (a+b) y=Φ a (Φ b y))
    (cont : ∀ y, Continuous (fun t => Φ t y)) (op : ∀ y, IsOpenMap (fun t => Φ t y))
    (gap : ∃ d>0, ∀ t∈Ioo (0:ℝ) d, Φ t x≠x) :
    ∃ T>0, ∃ e : OrientationCircle ≃ₜ C, ∀ t : ℝ, e (t:OrientationCircle)=Φ (t*T) x := by
  classical
  let A := range (fun t => Φ t x)
  have openA : IsOpen A := (op x).isOpen_range
  have openC : IsOpen Aᶜ := isOpen_iff_forall_mem_open.mpr (by
    intro y outside
    refine ⟨range (fun t => Φ t y),?_,(op y).isOpen_range,0,zero y⟩
    rintro _ ⟨t,rfl⟩ ⟨s,eq⟩
    apply outside
    refine ⟨(-t)+s,?_⟩
    change Φ ((-t)+s) x=y
    change Φ s x=Φ t y at eq
    rw [add,eq,← add,neg_add_cancel,zero])
  have onto : Surjective (fun t => Φ t x) :=
    range_eq_univ.mp (IsClopen.eq_univ ⟨isOpen_compl_iff.mp openC,openA⟩ ⟨_,mem_range_self 0⟩)
  let K : AddSubgroup ℝ := {
    carrier := {t | Φ t x=x}
    zero_mem' := zero x
    add_mem' := fun {a b} ha hb => by change Φ (a+b) x=x; rw [add,hb,ha]
    neg_mem' := fun {a} ha => by
      change Φ (-a) x=x
      calc Φ (-a) x=Φ (-a) (Φ a x) := congrArg (Φ (-a)) ha.symm
           _ = x := by rw [← add,neg_add_cancel,zero] }
  have collision (a b : ℝ) : Φ a x=Φ b x ↔ a-b∈K := by
    constructor
    · intro eq
      change Φ (a-b) x=x
      rw [sub_eq_neg_add,add,eq,← add,neg_add_cancel,zero]
    · intro mem
      change Φ (a-b) x=x at mem
      calc Φ a x=Φ (b+(a-b)) x := by ring_nf
           _=Φ b x := by rw [add,mem]
  have nonzero : K≠⊥ := by
    intro trivialK
    have inj : Injective (fun t => Φ t x) := by
      intro a b eq
      have m := (collision a b).mp eq
      rwa [trivialK,AddSubgroup.mem_bot,sub_eq_zero] at m
    let e := (Equiv.ofBijective _ ⟨inj,onto⟩).toHomeomorphOfContinuousOpen (cont x) (op x)
    exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) e.symm.compactSpace
  obtain ⟨d,dp,hgap⟩ := gap
  obtain ⟨T,minimal⟩ := AddSubgroup.exists_isLeast_pos nonzero dp
    (Set.disjoint_left.mpr (fun t mem inside => hgap t inside mem))
  have tp := minimal.1.2
  have basis := AddSubgroup.zmultiples_eq_of_isLeast_mem_and_pos minimal
  let f := fun t : ℝ => Φ (t*T) x
  have congr (a b : ℝ) : f a=f b ↔ (a : OrientationCircle)=(b : OrientationCircle) := by
    rw [QuotientAddGroup.eq_iff_sub_mem]
    change Φ (a*T) x=Φ (b*T) x ↔ _
    rw [collision,← basis,← sub_mul]
    constructor
    · rintro ⟨n,hn⟩
      refine ⟨n,?_⟩
      simp only [zsmul_eq_mul,mul_one]
      exact mul_right_cancel₀ tp.ne' (by simpa only [zsmul_eq_mul] using hn)
    · rintro ⟨n,hn⟩
      refine ⟨n,?_⟩
      simpa only [zsmul_eq_mul,mul_one] using congrArg (fun s : ℝ => s*T) hn
  have periodic : Periodic f 1 := fun a => (congr _ _).mpr (by rw [AddCircle.coe_add]; simp)
  let g : OrientationCircle → C := periodic.lift
  have eq (a : ℝ) : g (a:OrientationCircle)=f a := periodic.lift_coe a
  have cg : Continuous g := (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
    ((cont x).comp (continuous_id.mul continuous_const))
  have gi : Injective g := by
    rintro u v same
    obtain ⟨a,rfl⟩ := (Quotient.mk_surjective : Surjective ((↑) : ℝ → OrientationCircle)) u
    obtain ⟨b,rfl⟩ := (Quotient.mk_surjective : Surjective ((↑) : ℝ → OrientationCircle)) v
    exact (congr a b).mp same
  have gs : Surjective g := by
    intro y
    obtain ⟨t,ht⟩ := onto y
    refine ⟨((t/T:ℝ):OrientationCircle),?_⟩
    rw [eq]; change Φ (t/T*T) x=y
    rwa [div_mul_cancel₀ _ tp.ne']
  let emb := (cg.isClosedEmbedding gi).isEmbedding.toHomeomorph
  exact ⟨T,tp,emb.trans ((Homeomorph.setCongr gs.range_eq).trans (Homeomorph.Set.univ C)),eq⟩

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.compact_open_orbit_circle
