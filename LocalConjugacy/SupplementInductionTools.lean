module

public import LocalConjugacy.FiniteConjugacyTools

@[expose] public section

namespace LocalConjugacy
open scoped Pointwise

section Algebra
variable {G F : Type*} [Group G] [Group F]

theorem Conjugate.map {H K : Subgroup G} (h : Conjugate H K) (f : G →* F) :
    Conjugate (H.map f) (K.map f) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨f g, (conjugate_map f g H).symm.trans (congrArg (Subgroup.map f) hg)⟩

theorem supplements_subgroupOf (N H L : Subgroup G) (hs : Supplements N H) (hHL : H ≤ L) :
    Supplements (N.subgroupOf L) (H.subgroupOf L) := by
  intro x
  obtain ⟨n, hn, h, hh, he⟩ := hs x
  have hnL : n ∈ L := by
    have he' : n = (x : G) * h⁻¹ := by rw [← he]; group
    rw [he']
    exact L.mul_mem x.property (L.inv_mem (hHL hh))
  exact ⟨⟨n, hnL⟩, hn, ⟨h, hHL hh⟩, hh, Subtype.ext he⟩

theorem nilpotent_subgroupOf (N L : Subgroup G) [Group.IsNilpotent N] :
    Group.IsNilpotent (N.subgroupOf L) := by
  let f : N.subgroupOf L →* N :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  apply nilpotent_of_injective_hom f
  intro x y h
  have hv : x.val.val = y.val.val := congrArg (fun z : N => (z : G)) h
  exact Subtype.ext (Subtype.ext hv)

theorem nilpotent_subgroup_map (N : Subgroup G) [Group.IsNilpotent N] (f : G →* F) :
    Group.IsNilpotent (N.map f) := by
  let φ : N →* N.map f := (f.comp N.subtype).codRestrict _
    (fun x => Subgroup.mem_map_of_mem f x.property)
  apply Group.nilpotent_of_surjective φ
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem conjugacy_case_subgroup (N L : Subgroup G) [N.Normal]
    (h : Supersolvable G ∨ Group.IsNilpotent (G ⧸ N)) :
    Supersolvable L ∨ Group.IsNilpotent (L ⧸ N.subgroupOf L) := by
  rcases h with h | h
  · exact Or.inl (supersolvable_subgroup h L)
  · letI := h
    exact Or.inr (nilpotent_quotient_subgroup N L)

theorem conjugacy_case_map (N : Subgroup G) [N.Normal] (f : G →* F)
    (hs : Function.Surjective f) [(N.map f).Normal]
    (h : Supersolvable G ∨ Group.IsNilpotent (G ⧸ N)) :
    Supersolvable F ∨ Group.IsNilpotent (F ⧸ N.map f) := by
  rcases h with h | h
  · exact Or.inl (supersolvable_of_surjective h f hs)
  · letI := h
    exact Or.inr (nilpotent_quotient_image N f hs)

end Algebra

section Finite
variable {G : Type*} [Group G] [Finite G]

theorem card_subgroupOf_lt_of_not_le (N L : Subgroup G) (h : ¬ N ≤ L) :
    Nat.card (N.subgroupOf L) < Nat.card N := by
  let f : N.subgroupOf L → N := fun x => ⟨x.val.val, x.property⟩
  have hi : Function.Injective f := by
    intro x y h
    have hv : x.val.val = y.val.val := congrArg (fun z : N => (z : G)) h
    exact Subtype.ext (Subtype.ext hv)
  apply lt_of_le_of_ne (Nat.card_le_card_of_injective f hi)
  intro he
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi, he⟩).2
  apply h
  intro n hn
  obtain ⟨x, hx⟩ := hs ⟨n, hn⟩
  have hv := congrArg Subtype.val hx
  change x.val.val = n at hv
  exact hv ▸ x.val.property

theorem relIndex_sup_dvd_card (A H : Subgroup G) [A.Normal] :
    H.relIndex (A ⊔ H) ∣ Nat.card A := by
  let L := A ⊔ H
  have hs : Supplements (A.subgroupOf L) (H.subgroupOf L) := by
    intro x
    have hm : (x : G) ∈ (A : Set G) * (H : Set G) := by
      rw [← Subgroup.normal_mul]
      exact x.property
    obtain ⟨a, ha, h, hh, he⟩ := hm
    exact ⟨⟨a, (show A ≤ L from le_sup_left) ha⟩, ha,
      ⟨h, (show H ≤ L from le_sup_right) hh⟩, hh, Subtype.ext he⟩
  have hd := index_dvd_card_of_supplements (A.subgroupOf L) (H.subgroupOf L) hs
  have hc : Nat.card (A.subgroupOf L) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A ≤ L from le_sup_left)).toEquiv
  rwa [hc] at hd

/-- Coprimeness supplies the intersection identity used in the paper's
reduction to a single coefficient prime. -/
theorem inf_sup_eq_of_coprime (A B H : Subgroup G) [A.Normal] [B.Normal]
    (hcop : (Nat.card A).Coprime (Nat.card B)) : (A ⊔ H) ⊓ (B ⊔ H) = H := by
  let D := (A ⊔ H) ⊓ (B ⊔ H)
  have hHD : H ≤ D := le_inf le_sup_right le_sup_right
  have hA : H.relIndex D ∣ Nat.card A :=
    (dvd_of_mul_right_eq _ (Subgroup.relIndex_mul_relIndex H D (A ⊔ H) hHD inf_le_left)).trans
      (relIndex_sup_dvd_card A H)
  have hB : H.relIndex D ∣ Nat.card B :=
    (dvd_of_mul_right_eq _ (Subgroup.relIndex_mul_relIndex H D (B ⊔ H) hHD inf_le_right)).trans
      (relIndex_sup_dvd_card B H)
  exact le_antisymm (Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop hA hB)) hHD

omit [Finite G] in
theorem conjugate_le_sup_of_quotient (D H K : Subgroup G) [D.Normal]
    (n : G) (he : conjugate (QuotientGroup.mk' D n) (H.map (QuotientGroup.mk' D)) ≤
      K.map (QuotientGroup.mk' D)) : conjugate n H ≤ D ⊔ K := by
  have h := Subgroup.comap_mono (f := QuotientGroup.mk' D) he
  rw [← conjugate_map, Subgroup.comap_map_eq, Subgroup.comap_map_eq,
    QuotientGroup.ker_mk', sup_comm K D] at h
  exact le_sup_left.trans h

/-- The two coprime quotient conjugators combine because the factors commute. -/
theorem merge_coprime_conjugators (A B H K : Subgroup G) [A.Normal] [B.Normal]
    (hcop : (Nat.card A).Coprime (Nat.card B)) (hdis : Disjoint A B)
    (a : A) (b : B) (hA : conjugate (b : G) H ≤ A ⊔ K)
    (hB : conjugate (a : G) H ≤ B ⊔ K) : conjugate ((a : G) * b) H ≤ K := by
  rw [← inf_sup_eq_of_coprime A B K hcop]
  apply le_inf
  · rw [← conjugate_comp]
    exact (conjugate_mono (a : G) hA).trans_eq
      (conjugate_eq_self_of_mem (A ⊔ K) ((show A ≤ A ⊔ K from le_sup_left) a.property))
  · have hc := Subgroup.commute_of_normal_of_disjoint A B inferInstance inferInstance hdis
      a b a.property b.property
    rw [hc.eq, ← conjugate_comp]
    exact (conjugate_mono (b : G) hB).trans_eq
      (conjugate_eq_self_of_mem (B ⊔ K) ((show B ≤ B ⊔ K from le_sup_left) b.property))

theorem conjugate_of_mutual_inclusions (H K : Subgroup G)
    (hHK : ∃ g : G, conjugate g H ≤ K) (hKH : ∃ g : G, conjugate g K ≤ H) :
    Conjugate H K := by
  obtain ⟨g, hg⟩ := hHK
  obtain ⟨k, hk⟩ := hKH
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  have hcard : Nat.card (conjugate k K) ≤ Nat.card H :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hk) (Subgroup.inclusion_injective hk)
  have hgcard : Nat.card (conjugate g H) = Nat.card H :=
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  have hkcard : Nat.card (conjugate k K) = Nat.card K :=
    Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
  rwa [hgcard, ← hkcard]

omit [Finite G] in
theorem quotient_conjugator_from_factor (A B N H K : Subgroup G) [A.Normal]
    (hs : Supplements N H) (hAB : A ⊔ B = N)
    (hc : Conjugate (H.map (QuotientGroup.mk' A)) (K.map (QuotientGroup.mk' A))) :
    ∃ b : B, conjugate (QuotientGroup.mk' A b) (H.map (QuotientGroup.mk' A)) =
      K.map (QuotientGroup.mk' A) := by
  let π := QuotientGroup.mk' A
  have ha : A.map π = ⊥ := QuotientGroup.map_mk'_self A
  have hn : N.map π = B.map π := by rw [← hAB, Subgroup.map_sup, ha, bot_sup_eq]
  have hs' := supplements_map N H hs π (QuotientGroup.mk'_surjective A)
  rw [hn] at hs'
  obtain ⟨⟨_, b, hb, rfl⟩, he⟩ := normal_conjugator (B.map π) (H.map π) (K.map π) hs' hc
  exact ⟨⟨b, hb⟩, he⟩

end Finite
end LocalConjugacy
