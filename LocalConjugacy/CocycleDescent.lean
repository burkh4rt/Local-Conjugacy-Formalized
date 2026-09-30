module

public import LocalConjugacy.CocycleFiniteQuotient

@[expose] public section

namespace LocalConjugacy

section Descent
variable {J F N : Type*} [Group J] [Group F] [Group N]
  [TopologicalSpace J] [TopologicalSpace F] [TopologicalSpace N]
  [MulDistribMulAction J N] [MulDistribMulAction F N]

/-- The restriction of a homomorphism to a subgroup, with its image as codomain. -/
def subgroupImageHom (P : Subgroup J) (π : J →* F) : P →* P.map π :=
  (π.comp P.subtype).codRestrict (P.map π) (fun x => Subgroup.mem_map_of_mem π x.property)

theorem subgroupImageHom_surjective (P : Subgroup J) (π : J →* F) :
    Function.Surjective (subgroupImageHom P π) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

namespace Cocycle
/-- Inflate a global cocycle through a continuous action-compatible homomorphism. -/
def inflate (π : J →* F) (hπ : Continuous π)
    (ha : ∀ (j : J) (n : N), π j • n = j • n)
    (f : Cocycle (J := F) (N := N) ⊤) : Cocycle (J := J) (N := N) ⊤ where
  toFun x := f.toFun ⟨π x, trivial⟩
  continuous_toFun := f.continuous_toFun.comp ((hπ.comp continuous_subtype_val).subtype_mk _)
  map_mul x y := by
    change f.toFun ⟨π ((x : J) * y), trivial⟩ = _
    rw [π.map_mul]
    change f.toFun ((⟨π x, trivial⟩ : (⊤ : Subgroup F)) * ⟨π y, trivial⟩) = _
    rw [f.map_mul]
    exact congrArg (fun z => f.toFun ⟨π x, trivial⟩ * z) (ha x (f.toFun ⟨π y, trivial⟩))

variable (P : Subgroup J) (π : J →* F)
  (ha : ∀ (j : J) (n : N), π j • n = j • n) (f : Cocycle (N := N) P)
  (hf : ∀ x y : P, π x = π y → f.toFun x = f.toFun y)

noncomputable def imageSection (y : P.map π) : P :=
  (subgroupImageHom_surjective P π y).choose

theorem imageSection_spec (y : P.map π) :
    subgroupImageHom P π (imageSection P π y) = y :=
  (subgroupImageHom_surjective P π y).choose_spec

/-- Descent of a cocycle along a finite continuous image, with the action
compatibility and constancy on fibers recorded explicitly. -/
noncomputable def descend [DiscreteTopology F] : Cocycle (N := N) (P.map π) where
  toFun y := f.toFun (imageSection P π y)
  continuous_toFun := continuous_of_discreteTopology
  map_mul x y := by
    let r := imageSection P π
    have hr (z : P.map π) : π (r z) = z := congrArg Subtype.val (imageSection_spec P π z)
    have he : π (r (x * y)) = π (r x * r y) := by
      simp only [Subgroup.coe_mul, π.map_mul]
      change π (r (x * y)) = π (r x) * π (r y)
      rw [hr, hr, hr]
      rfl
    change f.toFun (r (x * y)) = f.toFun (r x) * ((x : F) • f.toFun (r y))
    rw [hf (r (x * y)) (r x * r y) he, f.map_mul]
    congr 1
    exact (ha (r x) (f.toFun (r y))).symm.trans (by rw [hr])

@[simp] theorem descend_apply [DiscreteTopology F] (x : P) :
    (descend (P := P) (π := π) (ha := ha) (f := f) (hf := hf)).toFun (subgroupImageHom P π x) = f.toFun x := by
  apply hf
  exact congrArg Subtype.val (imageSection_spec P π (subgroupImageHom P π x))

/-- Stability descends for normal domain subgroups. -/
theorem descend_invariant [DiscreteTopology F] [P.Normal]
    (hπ : Function.Surjective π) (hinv : InvariantUnder ⊤ P f) :
    InvariantUnder ⊤ (P.map π) (descend (P := P) (π := π) (ha := ha) (f := f) (hf := hf)) := by
  intro j _
  obtain ⟨t, rfl⟩ := hπ j
  obtain ⟨n, hn⟩ := hinv t trivial
  refine ⟨n, fun x hx hjx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hx
  have hty : t⁻¹ * y * t ∈ P := by
    simpa using (inferInstance : P.Normal).conj_mem y hy t⁻¹
  change π t • (descend (P := P) (π := π) (ha := ha) (f := f) (hf := hf)).toFun ⟨(π t)⁻¹ * π y * π t, hjx⟩ = _
  have hleft : (⟨(π t)⁻¹ * π y * π t, hjx⟩ : P.map π) =
      subgroupImageHom P π ⟨t⁻¹ * y * t, hty⟩ := by
    apply Subtype.ext
    change (π t)⁻¹ * π y * π t = π (t⁻¹ * y * t)
    simp only [π.map_mul, π.map_inv]
  rw [hleft, descend_apply]
  change π t • f.toFun ⟨t⁻¹ * y * t, hty⟩ =
    n⁻¹ * (descend (P := P) (π := π) (ha := ha) (f := f) (hf := hf)).toFun (subgroupImageHom P π ⟨y, hy⟩) * (π y • n)
  rw [descend_apply, ha, ha]
  exact hn y hy hty

end Cocycle
end Descent

section OpenNormal
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N] [Finite N]

/-- A cocycle on a closed subgroup and the whole ambient action have a
common finite quotient. -/
theorem exists_subgroup_cocycle_openNormal (P : Subgroup J)
    (f : Cocycle (N := N) P) :
    ∃ U : OpenNormalSubgroup J,
      (∀ u ∈ U, ∀ n : N, u • n = n) ∧
      ∀ x : P, (x : J) ∈ U → f.toFun x = 1 := by
  obtain ⟨V, hV, _⟩ := exists_cocycle_openNormal
    (fun _ : Empty => trivialCocycle (N := N) (⊤ : Subgroup J))
  have ho : IsOpen (f.toFun ⁻¹' {1}) := f.continuous_toFun.isOpen_preimage _ (isOpen_discrete _)
  obtain ⟨O, hO, he⟩ := isOpen_induced_iff.mp ho
  have h1 : (1 : J) ∈ O := by
    have hh : (1 : P) ∈ Subtype.val ⁻¹' O := by rw [he]; exact cocycle_one f
    exact hh
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
  refine ⟨V ⊓ W, fun u hu => hV u hu.1, fun x hx => ?_⟩
  have hh : x ∈ Subtype.val ⁻¹' O := hW hx.2
  rw [he] at hh
  exact hh

theorem cocycle_constant_on_quotient_fibers (P : Subgroup J)
    (f : Cocycle (N := N) P) (U : OpenNormalSubgroup J)
    (hf : ∀ x : P, (x : J) ∈ U → f.toFun x = 1)
    (x y : P) (hxy : QuotientGroup.mk' U.toSubgroup x = QuotientGroup.mk' U.toSubgroup y) :
    f.toFun x = f.toFun y := by
  have hu : ((x⁻¹ * y : P) : J) ∈ U := QuotientGroup.eq.mp hxy
  have he := f.map_mul x (x⁻¹ * y)
  rw [mul_inv_cancel_left, hf _ hu, smul_one, mul_one] at he
  exact he.symm

end OpenNormal
end LocalConjugacy
