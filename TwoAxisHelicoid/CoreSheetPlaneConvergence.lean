import TwoAxisHelicoid.CoreSheetNormalTilt

namespace TwoAxisHelicoid
open Set Filter Topology
open scoped Topology ContDiff RealInnerProductSpace

/-- Distance between unoriented tangent planes represented by their
unit normals. -/
noncomputable def coreNormalDistance (m n : SurfaceEuclideanSpace) : ℝ := min ‖m-n‖ ‖m+n‖

private theorem oriented_core_normal {m n : SurfaceEuclideanSpace} (unit : ‖m‖=1) :
    ∃ a : SurfaceEuclideanSpace, (a=m ∨ a= -m) ∧ ‖a‖=1 ∧ ‖a-n‖=coreNormalDistance m n := by
  by_cases h : ‖m-n‖≤‖m+n‖
  · exact ⟨m,Or.inl rfl,unit,(min_eq_left h).symm⟩
  · refine ⟨-m,Or.inr rfl,by simpa only [norm_neg] using unit,?_⟩
    rw [coreNormalDistance,min_eq_right (le_of_not_ge h),show -m-n= -(m+n) by abel,norm_neg]

/-- Local convergence of the physical heights and of the *unoriented*
tangent planes implies local C¹ convergence of the height functions
and of the spatial parametrizations over the reference patch. -/
theorem physical_plane_convergence_gives_core_derivative_convergence {U : Set ℂ} (openU : IsOpen U)
    (X N : ℂ → SurfaceEuclideanSpace) (Z ns : ℕ → ℂ → SurfaceEuclideanSpace) (u : ℕ → ℂ → ℝ)
    (sx : ∀ z∈U, ContDiffAt ℝ 1 X z) (sn : ∀ z∈U, ContDiffAt ℝ 1 N z)
    (du : ∀ k z, z∈U → DifferentiableAt ℝ (u k) z)
    (graph : ∀ k z, z∈U → Z k z=X z+u k z • N z)
    (normal : ∀ z∈U, ‖N z‖=1 ∧ ∀ v, ⟪N z,fderiv ℝ X z v⟫=0)
    (moving : ∀ k z, z∈U → ‖ns k z‖=1 ∧ ∀ v, ⟪ns k z,fderiv ℝ (Z k) z v⟫=0)
    (heights : TendstoLocallyUniformlyOn u (fun _ => 0) atTop U)
    (planes : TendstoLocallyUniformlyOn (fun k z => coreNormalDistance (ns k z) (N z)) (fun _ => 0) atTop U) :
    TendstoLocallyUniformlyOn (fun k => fderiv ℝ (u k)) (fun _ => 0) atTop U ∧
    TendstoLocallyUniformlyOn (fun k => fderiv ℝ (Z k)) (fderiv ℝ X) atTop U := by
  suffices slope : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (u k)) (fun _ => 0) atTop U from
    ⟨slope,(normal_graph_spatial_derivative_convergence openU X N Z u sx sn du graph heights slope).2⟩
  apply openU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro z hz
  let l := (atTop : Filter ℕ) ×ˢ 𝓝 z
  let err := fun p : ℕ × ℂ => coreNormalDistance (ns p.1 p.2) (N p.2)
  have e : Tendsto err l (𝓝 0) :=
    tendsto_const_nhds.congr_uniformity ((openU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp planes) z hz)
  have h : Tendsto (fun p : ℕ × ℂ => u p.1 p.2) l (𝓝 0) :=
    tendsto_const_nhds.congr_uniformity ((openU.tendstoLocallyUniformlyOn_iff_forall_tendsto.mp heights) z hz)
  have nd : Tendsto (fun p : ℕ × ℂ => fderiv ℝ N p.2) l (𝓝 (fderiv ℝ N z)) :=
    ((sn z hz).continuousAt_fderiv one_ne_zero).tendsto.comp tendsto_snd
  have xd : Tendsto (fun p : ℕ × ℂ => fderiv ℝ X p.2) l (𝓝 (fderiv ℝ X z)) :=
    ((sx z hz).continuousAt_fderiv one_ne_zero).tendsto.comp tendsto_snd
  have lim : Tendsto (fun p : ℕ × ℂ => fderiv ℝ (u p.1) p.2) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards [tendsto_snd (openU.mem_nhds hz),e.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))]
        with p hp small
      obtain ⟨a,choice,unit,dist⟩ := oriented_core_normal (n := N p.2) (moving p.1 p.2 hp).1
      have perp (v : ℂ) : ⟪a,fderiv ℝ (Z p.1) p.2 v⟫=0 := by
        rcases choice with h|h
        · simpa only [h] using (moving p.1 p.2 hp).2 v
        · rw [h,inner_neg_left,(moving p.1 p.2 hp).2,neg_zero]
      have gr : Z p.1 =ᶠ[𝓝 p.2] fun w => X w+u p.1 w • N w := by
        filter_upwards [openU.mem_nhds hp] with w hw
        exact graph p.1 w hw
      have b := core_sheet_height_slope ((sx p.2 hp).differentiableAt one_ne_zero)
        ((sn p.2 hp).differentiableAt one_ne_zero) (du p.1 p.2 hp) gr (normal p.2 hp).1
        (normal p.2 hp).2 unit perp (dist.trans_le small.le)
      simpa only [dist] using b
    · simpa only [abs_zero,zero_mul,zero_add,mul_zero] using
        (((e.mul xd.norm).add (h.abs.mul nd.norm)).const_mul 2)
  exact (tendsto_const_nhds.prodMk_nhds lim).mono_right (nhds_le_uniformity _)

end TwoAxisHelicoid
#print axioms TwoAxisHelicoid.physical_plane_convergence_gives_core_derivative_convergence
