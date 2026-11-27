import TwoAxisHelicoid.BoundedPlaneFill
import TwoAxisHelicoid.DisjointFilledNeighborhoods

namespace TwoAxisHelicoid
open Set Metric Bornology Topology

private theorem bounded_translate_cannot_stay {K : Set ℂ} (bounded : IsBounded K) (non : K.Nonempty)
    {a : ℂ} (notzero : a≠0) : ¬∀ z∈K, z+a∈K := by
  intro stay
  obtain ⟨z,hz⟩ := non
  obtain ⟨B,b⟩ := bounded.exists_norm_le
  have all (n : ℕ) : z+(n:ℂ)*a∈K := by
    induction n with
    | zero => simpa using hz
    | succ n ih =>
      have e : z+((n+1:ℕ):ℂ)*a=(z+(n:ℂ)*a)+a := by push_cast; ring
      rw [e]
      exact stay _ ih
  have normA := norm_pos_iff.mpr notzero
  obtain ⟨n,far⟩ := exists_nat_gt ((B+‖z‖)/‖a‖)
  have gap := (div_lt_iff₀ normA).mp far
  have limit := norm_sub_le (z+(n:ℂ)*a) z
  have step : (z+(n:ℂ)*a)-z=(n:ℂ)*a := by abel
  rw [step,norm_mul,Complex.norm_natCast] at limit
  linarith [b _ (all n)]

/-- Filling a bounded connected open set cannot introduce overlap with
a disjoint lattice translate. Neither filled lift can nest inside its
translate, because repeated translation leaves every bounded region. -/
theorem boundedPlaneFill_disjoint_translate {U : Set ℂ} (bounded : IsBounded U)
    (op : IsOpen U) (connected : IsConnected U) {a : ℂ} (nz : a≠0)
    (apart : Disjoint U ((Homeomorph.addRight a) '' U)) :
    Disjoint (boundedPlaneFill U) ((Homeomorph.addRight a) '' boundedPlaneFill U) := by
  let e := Homeomorph.addRight a
  let V := e '' U
  let F := boundedPlaneFill U
  let G := boundedPlaneFill V
  have shifted : e '' F=G := boundedPlaneFill_homeomorph e U
  have vc : IsConnected V := connected.image e e.continuous.continuousOn
  have vo : IsOpen V := e.isOpenMap U op
  have vb : IsBounded V := (bounded.isCompact_closure.image e.continuous).isBounded.subset (image_mono subset_closure)
  obtain ⟨incl,fb,_,_,_⟩ := boundedPlaneFill_properties bounded
  have fn : F.Nonempty := connected.nonempty.mono incl
  have notGU : ¬G⊆F := by
    intro sub
    exact bounded_translate_cannot_stay fb fn nz fun z hz => sub (shifted ▸ mem_image_of_mem e hz)
  have notUG : ¬F⊆G := by
    intro sub
    apply bounded_translate_cannot_stay fb fn (neg_ne_zero.mpr nz)
    intro z hz
    obtain ⟨x,hx,eq⟩ := (show z∈e '' F from shifted.symm ▸ sub hz)
    change x+a=z at eq
    rwa [←eq,add_neg_cancel_right]
  obtain ⟨R,rb⟩ := (bounded.union vb).exists_norm_le
  let B := max R 0
  let p : ℂ := (B+1:ℝ)
  have bp : 0≤B := le_max_right _ _
  have large : B<‖p‖ := by dsimp only [p]; rw [Complex.norm_real,Real.norm_of_nonneg (by linarith)]; linarith
  have ub' (z : ℂ) (zu : z∈U) : ‖z‖≤B := (rb z (Or.inl zu)).trans (le_max_left _ _)
  have vb' (z : ℂ) (zv : z∈V) : ‖z‖≤B := (rb z (Or.inr zv)).trans (le_max_left _ _)
  have uf : F=fillAwayFrom p U := (boundedPlaneFill_eq_exterior bp ub' large).1
  have vf : G=fillAwayFrom p V := (boundedPlaneFill_eq_exterior bp vb' large).1
  have gc : IsPreconnected G := ((boundedPlaneFill_properties vb).2.2.2.2 vo vc).isPreconnected
  rw [uf,vf] at notUG notGU
  rw [vf] at gc
  change Disjoint F (e '' F)
  rw [shifted,uf,vf]
  exact nonnested_filled_neighborhoods_disjoint (fun h => large.not_ge (ub' _ h))
    (fun h => large.not_ge (vb' _ h)) connected vc gc apart notUG notGU

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.boundedPlaneFill_disjoint_translate
