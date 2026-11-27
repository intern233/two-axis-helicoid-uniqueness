import TwoAxisHelicoid.TransverseCoreTubeSheets
import TwoAxisHelicoid.RegularCoreNormalCoordinates

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- Around a compact-core foot point the same actual inverse normal
coordinates work throughout an ambient neighborhood. Every immersed
surface with a nearby unoriented tangent plane then has a smooth sheet
over the base, with no regularity or local invertibility hypothesis on
the base projection. -/
theorem normal_tube_transverse_coordinates_near_foot {X N : ℂ → SurfaceEuclideanSpace} {z : ℂ}
    (sx : ContDiffAt ℝ 1 X z) (sn : ContDiffAt ℝ 1 N z) (inj : Function.Injective (fderiv ℝ X z))
    (unit : ‖N z‖=1) (orth : ∀ v, ⟪fderiv ℝ X z v,N z⟫=0) :
    ∃ (base : SurfaceEuclideanSpace → ℂ) (height : SurfaceEuclideanSpace → ℝ)
      (V : Set SurfaceEuclideanSpace), IsOpen V ∧ X z∈V ∧ base (X z)=z ∧ height (X z)=0 ∧
      (∀ y∈V, ContDiffAt ℝ 1 base y ∧ ContDiffAt ℝ 1 height y ∧
        y=X (base y)+height y • N (base y)) ∧
      ∀ (Y : ℂ → SurfaceEuclideanSpace) (w : ℂ), Y w∈V → ContDiffAt ℝ 1 Y w →
        Function.Injective (fderiv ℝ Y w) → ∀ m : SurfaceEuclideanSpace,
        ‖m‖=1 → (∀ v, ⟪fderiv ℝ Y w v,m⟫=0) →
        (‖N (base (Y w))-m‖<1 ∨ ‖N (base (Y w))+m‖<1) →
        ∃ e : OpenPartialHomeomorph ℂ ℂ, w∈e.source ∧ (e : ℂ → ℂ)=base ∘ Y ∧
          ContDiffAt ℝ 1 (Y ∘ e.symm) (base (Y w)) := by
  obtain ⟨e,inside,eq,reg⟩ := normal_coordinate_smooth_local_inverse sx sn inj unit orth
  have zero : e (z,0)=X z := by rw [eq]; simp
  have target : X z∈e.target := zero ▸ e.map_source inside
  have back : e.symm (X z)=(z,0) := zero ▸ e.left_inv inside
  let b := Prod.fst ∘ e.symm
  let h := Prod.snd ∘ e.symm
  have bz : b (X z)=z := congrArg Prod.fst back
  have hz : h (X z)=0 := congrArg Prod.snd back
  have near : Tendsto b (𝓝 (X z)) (𝓝 z) := by
    have lim : Tendsto b (𝓝 (X z)) (𝓝 (b (X z))) := (contDiffAt_fst.comp _ reg).continuousAt
    rwa [bz] at lim
  have allNear := ((reg.eventually (by simp)).and (near.eventually (sx.eventually (by simp)))).and
    ((near.eventually (sn.eventually (by simp))).and (e.open_target.mem_nhds target))
  obtain ⟨V,good,vo,vz⟩ := mem_nhds_iff.mp allNear
  have data (y : SurfaceEuclideanSpace) (hy : y∈V) : ContDiffAt ℝ 1 b y ∧ ContDiffAt ℝ 1 h y ∧
      y=X (b y)+h y • N (b y) := by
    have g := good hy
    refine ⟨contDiffAt_fst.comp y g.1.1,contDiffAt_snd.comp y g.1.1,?_⟩
    have recov := (e.right_inv g.2.2).symm
    rwa [eq] at recov
  refine ⟨b,h,V,vo,vz,bz,hz,data,?_⟩
  intro Y w yw sm imm m un perp close
  have g := good yw
  have d := data _ yw
  apply transverse_core_normal_sheet (g.1.2.differentiableAt (by simp)) (g.2.1.differentiableAt (by simp)) d.1 (d.2.1.differentiableAt (by simp)) _ sm imm m perp (nearby_core_normals_transverse un close)
  filter_upwards [vo.mem_nhds yw] with v hv using (data v hv).2.2.symm

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.normal_tube_transverse_coordinates_near_foot
