module

public import LocalConjugacy.CocycleDescent

@[expose] public section

namespace LocalConjugacy
open scoped Pointwise

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- A small open normal subgroup kills a cocycle on its domain and fixes its
finite image. The coefficient group itself may be infinite. -/
theorem exists_cocycle_neighborhood_kernel (H : Subgroup J)
    (hH : IsClosed (H : Set J)) (f : Cocycle (N := N) H) :
    ∃ U : OpenNormalSubgroup J,
      (∀ u ∈ U, ∀ x : H, u • f.toFun x = f.toFun x) ∧
      ∀ x : H, (x : J) ∈ U → f.toFun x = 1 := by
  letI := profinite_closed_subgroup H hH
  have hf : (Set.range f.toFun).Finite :=
    (isCompact_range f.continuous_toFun).finite_of_discrete
  let A : Set J := ⋂ n ∈ Set.range f.toFun, {j : J | j • n = n}
  have hA : IsOpen A := hf.isOpen_biInter fun n _ =>
    (continuous_id.smul continuous_const).isOpen_preimage _ (isOpen_discrete {n})
  have h1A : (1 : J) ∈ A := by simp [A]
  have ho : IsOpen (f.toFun ⁻¹' {1}) :=
    f.continuous_toFun.isOpen_preimage _ (isOpen_discrete _)
  obtain ⟨O, hO, he⟩ := isOpen_induced_iff.mp ho
  have h1O : (1 : J) ∈ O := by
    have hh : (1 : H) ∈ Subtype.val ⁻¹' O := by rw [he]; exact cocycle_one f
    exact hh
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hA.inter hO) ⟨h1A, h1O⟩
  refine ⟨U, ?_, ?_⟩
  · intro u hu x
    exact Set.mem_iInter.mp (Set.mem_iInter.mp (hU hu).1 (f.toFun x)) ⟨x, rfl⟩
  · intro x hx
    have hh : x ∈ Subtype.val ⁻¹' O := (hU hx).2
    rw [he] at hh
    exact hh

/-- Every continuous cocycle on a closed subgroup extends to an open subgroup
containing it. Only discreteness of the coefficients is needed. -/
theorem extend_cocycle_to_open_subgroup (H : Subgroup J)
    (hH : IsClosed (H : Set J)) (f : Cocycle (N := N) H) :
    ∃ (V : Subgroup J) (hHV : H ≤ V), IsOpen (V : Set J) ∧
      ∃ F : Cocycle (N := N) V, restrictCocycle hHV F = f := by
  classical
  obtain ⟨U, hfix, htriv⟩ := exists_cocycle_neighborhood_kernel H hH f
  let V := H ⊔ U.toSubgroup
  have hHV : H ≤ V := le_sup_left
  have hUV : U.toSubgroup ≤ V := le_sup_right
  have hex (v : V) : ∃ x : H, ∃ u : U, (x : J) * u = v := by
    have hv : (v : J) ∈ (H : Set J) * (U.toSubgroup : Set J) := by
      rw [← Subgroup.mul_normal]
      exact v.property
    obtain ⟨x, hx, u, hu, he⟩ := hv
    exact ⟨⟨x, hx⟩, ⟨u, hu⟩, he⟩
  choose a b hab using hex
  let F : V → N := fun v => f.toFun (a v)
  let m : H × U → V := fun t =>
    ⟨(t.1 : J) * t.2, V.mul_mem (hHV t.1.property) (hUV t.2.property)⟩
  have hval (x : H) (u : U) : F (m (x, u)) = f.toFun x := by
    let v := m (x, u)
    let d : H := x⁻¹ * a v
    have hd : (d : J) ∈ U := by
      have he : (d : J) = (u : J) * (b v : J)⁻¹ := by
        have hh := hab v
        change (a v : J) * b v = (x : J) * u at hh
        change (x : J)⁻¹ * a v = (u : J) * (b v : J)⁻¹
        calc
          (x : J)⁻¹ * a v = (x : J)⁻¹ * ((a v : J) * b v) * (b v : J)⁻¹ := by group
          _ = (u : J) * (b v : J)⁻¹ := by rw [hh]; group
      rw [he]
      exact U.toSubgroup.mul_mem u.property (U.toSubgroup.inv_mem (b v).property)
    have he : a v = x * d := by dsimp [d]; group
    change f.toFun (a v) = f.toFun x
    rw [he, f.map_mul, htriv d hd, smul_one, mul_one]
  have hmul (v w : V) : F (v * w) = F v * ((v : J) • F w) := by
    let t : U := ⟨(a w : J)⁻¹ * b v * a w * b w,
      U.toSubgroup.mul_mem
        (by
          simpa using (inferInstance : U.toSubgroup.Normal).conj_mem
            (b v) (b v).property (a w : J)⁻¹) (b w).property⟩
    have he : v * w = m (a v * a w, t) := by
      apply Subtype.ext
      change (v : J) * w = ((a v : J) * a w) *
        ((a w : J)⁻¹ * b v * a w * b w)
      rw [← hab v, ← hab w]
      group
    rw [he, hval, f.map_mul]
    change f.toFun (a v) * ((a v : J) • f.toFun (a w)) =
      f.toFun (a v) * ((v : J) • f.toFun (a w))
    rw [← hab v, mul_smul, hfix (b v) (b v).property]
  letI := profinite_closed_subgroup H hH
  letI := profinite_closed_subgroup U.toSubgroup U.isClosed
  have hm : Continuous m :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  have hms : Function.Surjective m := by
    intro v
    exact ⟨(a v, b v), Subtype.ext (hab v)⟩
  have hc : Continuous F := hm.isClosedMap.isQuotientMap hm hms |>.continuous_iff.mpr (by
    exact (f.continuous_toFun.comp continuous_fst).congr (fun t => (hval t.1 t.2).symm))
  refine ⟨V, hHV, Subgroup.isOpen_mono hUV U.isOpen,
    ⟨{ toFun := F, continuous_toFun := hc, map_mul := hmul }, ?_⟩⟩
  apply Cocycle.ext
  intro x
  change F ⟨(x : J), hHV x.property⟩ = f.toFun x
  simpa only [m, Subgroup.coe_one, mul_one] using hval x 1

end LocalConjugacy
