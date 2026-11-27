import TwoAxisHelicoid.GraphBandGreenFlux
import Mathlib.Analysis.Calculus.FDeriv.Const

namespace TwoAxisHelicoid
open Set Function MeasureTheory Filter Topology
open scoped Interval ContDiff Topology

/-- A smooth local defining graph has zero two-dimensional area.
The assertion concerns its whole graph in the measured coordinate plane. -/
theorem plane_graph_volume_zero {φ : ℝ → ℝ} (c : Continuous φ) :
    volume {z : ℝ×ℝ | z.2=φ z.1}=0 := by
  let G := {z : ℝ×ℝ | z.2=φ z.1}
  have ms : MeasurableSet G := (isClosed_eq continuous_snd (c.comp continuous_fst)).measurableSet
  change (volume.prod volume) G=0
  rw [Measure.prod_apply ms]
  have fiber (x : ℝ) : Prod.mk x ⁻¹' G={φ x} := rfl
  simp only [fiber,measure_singleton,lintegral_zero]

/-- A field supported in a single open boundary chart has only the
flux through the true curved boundary. The rest of the measurable
region can extend arbitrarily beyond the chart. The defining side is
specified geometrically in the chart and all three artificial edges
drop out by support. -/
theorem compactly_supported_boundary_graph_divergence {φ : ℝ → ℝ} (cφ : ContDiff ℝ 2 φ)
    {l r d : ℝ} (lr : l≤r) (dp : 0<d) (Ω : Set (ℝ×ℝ)) (ms : MeasurableSet Ω)
    (side : ∀ q∈Icc (l,-d) (r,d), realGraphShear φ q∈Ω ↔ 0≤q.2)
    {P Q : ℝ×ℝ → ℝ}
    (support : tsupport P ∪ tsupport Q ⊆ realGraphShear φ '' (Ioo l r ×ˢ Ioo (-d) d))
    (cP : ∀ z∈realGraphShear φ '' Icc (l,0) (r,d), ContDiffAt ℝ 1 P z)
    (cQ : ∀ z∈realGraphShear φ '' Icc (l,0) (r,d), ContDiffAt ℝ 1 Q z) :
    (∫ z in Ω, fderiv ℝ P z (1,0)+fderiv ℝ Q z (0,1))=
      -(∫ x in l..r, Q (x,φ x)-deriv φ x*P (x,φ x)) := by
  let T := realGraphShear φ
  let B := Icc (l,(0:ℝ)) (r,d)
  let W := Ioo l r ×ˢ Ioo (-d) d
  have inj : Injective T := by
    rintro ⟨x,y⟩ ⟨u,v⟩ eq
    have xu : x=u := congrArg Prod.fst eq
    subst u
    exact Prod.ext rfl (add_right_cancel (congrArg Prod.snd eq))
  have inside : T '' B⊆Ω := by
    rintro _ ⟨q,hq,rfl⟩
    apply (side q ⟨⟨hq.1.1,(neg_nonpos.mpr dp.le).trans hq.1.2⟩,hq.2⟩).mpr hq.1.2
  have negligible (z : ℝ×ℝ) (hz : z∈Ω \ T '' B) : z∉tsupport P ∪ tsupport Q := by
    intro member
    obtain ⟨q,hq,eq⟩ := support member
    have inBox : q∈Icc (l,-d) (r,d) := ⟨⟨hq.1.1.le,hq.2.1.le⟩,hq.1.2.le,hq.2.2.le⟩
    have above := (side q inBox).mp (eq.symm ▸ hz.1)
    exact hz.2 ⟨q,⟨⟨hq.1.1.le,above⟩,hq.1.2.le,hq.2.2.le⟩,eq⟩
  have vanish (q : ℝ×ℝ) (out : q∉W) : P (T q)=0 ∧ Q (T q)=0 := by
    have absent : T q∉tsupport P ∪ tsupport Q := by
      intro member
      obtain ⟨x,insideW,eq⟩ := support member
      exact out (inj eq ▸ insideW)
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h => absent (Or.inl h)),
      image_eq_zero_of_notMem_tsupport (fun h => absent (Or.inr h))⟩
  let N := fun q : ℝ×ℝ => Q (T q)-deriv φ q.1*P (T q)
  have top (x : ℝ) : N (x,d)=0 := by
    obtain ⟨p,q⟩ := vanish (x,d) (fun m => (lt_irrefl d) m.2.2)
    simp [N,p,q]
  have left (y : ℝ) : P (T (l,y))=0 := (vanish (l,y) (fun m => (lt_irrefl l) m.1.1)).1
  have right (y : ℝ) : P (T (r,y))=0 := (vanish (r,y) (fun m => (lt_irrefl r) m.1.2)).1
  have base (x : ℝ) : N (x,0)=Q (x,φ x)-deriv φ x*P (x,φ x) := by simp [N,T,realGraphShear]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero ms inside (fun z hz => by
    have no := negligible z hz
    rw [fderiv_of_notMem_tsupport (𝕜:=ℝ) (fun mem => no (Or.inl mem)),
      fderiv_of_notMem_tsupport (𝕜:=ℝ) (fun mem => no (Or.inr mem))]
    simp)]
  have flux := divergence_on_graph_band cφ (l,0) (r,d) ⟨lr,dp.le⟩ cP cQ
  change (∫ z in T '' B, fderiv ℝ P z (1,0)+fderiv ℝ Q z (0,1))=
    (((∫ x in l..r, N (x,d))-(∫ x in l..r, N (x,0)))+(∫ y in (0:ℝ)..d, P (T (r,y))))-
      (∫ y in (0:ℝ)..d, P (T (l,y))) at flux
  simpa only [top,left,right,base,intervalIntegral.integral_zero,zero_sub,add_zero,sub_zero] using flux

/-- The same physical flux formula for an open region. Adding the local
defining graph gives the closed-side calculation and changes the area
integral by zero. -/
theorem open_boundary_graph_divergence {φ : ℝ → ℝ} (cφ : ContDiff ℝ 2 φ)
    {l r d : ℝ} (lr : l≤r) (dp : 0<d) (Ω : Set (ℝ×ℝ)) (ms : MeasurableSet Ω)
    (side : ∀ q∈Icc (l,-d) (r,d), realGraphShear φ q∈Ω ↔ 0<q.2)
    {P Q : ℝ×ℝ → ℝ}
    (support : tsupport P ∪ tsupport Q ⊆ realGraphShear φ '' (Ioo l r ×ˢ Ioo (-d) d))
    (cP : ∀ z∈realGraphShear φ '' Icc (l,0) (r,d), ContDiffAt ℝ 1 P z)
    (cQ : ∀ z∈realGraphShear φ '' Icc (l,0) (r,d), ContDiffAt ℝ 1 Q z) :
    (∫ z in Ω, fderiv ℝ P z (1,0)+fderiv ℝ Q z (0,1))=
      -(∫ x in l..r, Q (x,φ x)-deriv φ x*P (x,φ x)) := by
  let G := {p : ℝ×ℝ | p.2=φ p.1}
  have mg : MeasurableSet G := (isClosed_eq continuous_snd (cφ.continuous.comp continuous_fst)).measurableSet
  have eq : Ω =ᵐ[volume] Ω∪G := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (plane_graph_volume_zero cφ.continuous)] with z hz
    exact propext ⟨Or.inl,fun m => m.elim id (fun bad => (hz bad).elim)⟩
  rw [setIntegral_congr_set eq]
  apply compactly_supported_boundary_graph_divergence cφ lr dp _ (ms.union mg) _ support cP cQ
  intro q hq
  change (realGraphShear φ q∈Ω ∨ q.2+φ q.1=φ q.1) ↔ 0≤q.2
  rw [side q hq,add_eq_right]
  constructor
  · exact fun h => h.elim le_of_lt (fun zero => zero.ge)
  · exact fun h => h.eq_or_lt.elim (fun zero => Or.inr zero.symm) Or.inl

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.plane_graph_volume_zero
#print axioms TwoAxisHelicoid.compactly_supported_boundary_graph_divergence
