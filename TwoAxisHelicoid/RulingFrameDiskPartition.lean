import TwoAxisHelicoid.ReferenceHelicoidRulingFrame
import TwoAxisHelicoid.MarkedSpatialDisks

namespace TwoAxisHelicoid
open Set Complex

/-- Transport the two actual disk components back from a ruling-centred
frame. The transported disks have the correct connected components,
side inequalities and physical vertical half-turn in the original frame. -/
theorem two_disk_partition_in_original_ruling_frame (S : Set (Fin 3 → ℝ)) (α h : ℝ)
    (disks : HasSpatialTwoDiskPartition (referenceRulingFrame α h '' S) α) :
    HasSpatialTwoDiskPartition S α := by
  let R := referenceRulingFrame α h
  let T := range (axisRuledHelicoid I α 0)
  let C := S \ T
  let D := R '' S \ T
  let half := fun p : Fin 3 → ℝ => ![-p 0,-p 1,p 2]
  have back : R ⁻¹' D=C := by
    ext p
    change (R p∈R '' S ∧ R p∉T) ↔ p∈S ∧ p∉T
    rw [R.injective.mem_set_image,referenceRulingFrame_mem_helicoid]
  have full : R '' C=D := by rw [← back,R.image_preimage]
  have invol (p : Fin 3 → ℝ) : half (half p)=p := by ext j; fin_cases j <;> simp [half]
  have commute (p : Fin 3 → ℝ) : R (half p)=half (R p) := referenceRulingFrame_half_turn α h p
  obtain ⟨A,B,cov,apart,⟨a⟩,⟨b⟩,ca,cb,swap,sides⟩ := disks
  change D=A∪B at cov
  change half '' A=B at swap
  have liftComponent {V : Set (Fin 3 → ℝ)} (sub : V⊆D)
      (component : ∀ q∈V, connectedComponentIn D q=V) {p : Fin 3 → ℝ} (hp : R p∈V) :
      connectedComponentIn C p=R ⁻¹' V := by
    have pc : p∈C := back ▸ (show p∈R ⁻¹' D from sub hp)
    calc connectedComponentIn C p=R ⁻¹' (R '' connectedComponentIn C p) := (R.preimage_image _).symm
         _ = _ := by rw [R.image_connectedComponentIn pc,full,component _ hp]
  refine ⟨R ⁻¹' A,R ⁻¹' B,?_,apart.preimage R,⟨(R.subtype (fun _ => Iff.rfl)).trans a⟩,
    ⟨(R.subtype (fun _ => Iff.rfl)).trans b⟩,
    fun _ hp => liftComponent (cov.symm ▸ subset_union_left) ca hp,
    fun _ hp => liftComponent (cov.symm ▸ subset_union_right) cb hp,?_,?_⟩
  · change C=R ⁻¹' A ∪ R ⁻¹' B
    rw [← back,cov,preimage_union]
  · ext p
    constructor
    · rintro ⟨q,hq,rfl⟩
      change R (half q)∈B
      rw [commute,← swap]
      exact mem_image_of_mem half hq
    · intro hp
      obtain ⟨q,hq,eq⟩ := (show R p∈half '' A from swap.symm ▸ hp)
      refine ⟨half p,?_,invol p⟩
      change R (half p)∈A
      rw [commute,← eq,invol]
      exact hq
  · have positive {V : Set (Fin 3 → ℝ)} (sign : V⊆{p | 0<axisHelicoidSide I α 0 p}) :
        R ⁻¹' V⊆{p | 0<axisHelicoidSide I α 0 p} := by
      intro p hp
      change 0<axisHelicoidSide I α 0 p
      rw [← referenceRulingFrame_side α h p]
      exact sign hp
    have negative {V : Set (Fin 3 → ℝ)} (sign : V⊆{p | axisHelicoidSide I α 0 p<0}) :
        R ⁻¹' V⊆{p | axisHelicoidSide I α 0 p<0} := by
      intro p hp
      change axisHelicoidSide I α 0 p<0
      rw [← referenceRulingFrame_side α h p]
      exact sign hp
    exact sides.imp (fun v => ⟨positive v.1,negative v.2⟩) (fun v => ⟨negative v.1,positive v.2⟩)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.two_disk_partition_in_original_ruling_frame
