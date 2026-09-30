module

public import LocalConjugacy.StructuralQuotients
public import LocalConjugacy.PGroupSupplementReduction
public import LocalConjugacy.SupplementInductionTools

@[expose] public section

/-! The reductions needed to run Proposition 3.2's induction on `|N|`
while the ambient profinite group is allowed to be infinite. -/

namespace LocalConjugacy

section Algebra
variable {G : Type*} [Group G]

theorem finiteIndex_of_finite_supplement (N H : Subgroup G) [Finite N]
    (hs : Supplements N H) : H.FiniteIndex := by
  let f : N → G ⧸ H := fun n => QuotientGroup.mk (n : G)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn, h, hh, rfl⟩ := hs x
    refine ⟨⟨n, hn⟩, QuotientGroup.eq.mpr ?_⟩
    simpa only [inv_mul_cancel_left] using hh
  letI : Finite (G ⧸ H) := Finite.of_surjective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

theorem card_subgroupOf_lt_finite_kernel (N L : Subgroup G) [Finite N] (h : ¬ N ≤ L) :
    Nat.card (N.subgroupOf L) < Nat.card N := by
  let f : N.subgroupOf L → N := fun x => ⟨x.val.val, x.property⟩
  have hi : Function.Injective f := by
    intro x y h
    have hv : x.val.val = y.val.val := congrArg (fun z : N => (z : G)) h
    exact Subtype.ext (Subtype.ext hv)
  letI := Finite.of_injective f hi
  apply lt_of_le_of_ne (Nat.card_le_card_of_injective f hi)
  intro he
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi, he⟩).2
  apply h
  intro n hn
  obtain ⟨x, hx⟩ := hs ⟨n, hn⟩
  have hv : x.val.val = n := congrArg (fun z : N => (z : G)) hx
  exact hv ▸ x.val.property

theorem card_map_quotient_lt_finite_kernel (N D : Subgroup G) [Finite N] [D.Normal]
    (hDN : D ≤ N) (hD : D ≠ ⊥) :
    Nat.card (N.map (QuotientGroup.mk' D)) < Nat.card N := by
  let f : N →* N.map (QuotientGroup.mk' D) :=
    ((QuotientGroup.mk' D).comp N.subtype).codRestrict _
      (fun x => Subgroup.mem_map_of_mem _ x.property)
  have hs : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  letI := Finite.of_surjective f hs
  have hi : ¬ Function.Injective f := by
    intro hi
    apply hD
    apply eq_bot_iff.mpr
    intro x hx
    change x = 1
    have he : f ⟨x, hDN hx⟩ = f 1 := by
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff x).mpr hx
    exact congrArg Subtype.val (hi he)
  apply lt_of_le_of_ne (Nat.card_le_card_of_surjective f hs)
  intro he
  exact hi ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hs, he.symm⟩).1

theorem conjugate_of_mutual_inclusions_finiteIndex (H K : Subgroup G) [H.FiniteIndex]
    [K.FiniteIndex] (hHK : ∃ g : G, conjugate g H ≤ K)
    (hKH : ∃ g : G, conjugate g K ≤ H) : Conjugate H K := by
  obtain ⟨g, hg⟩ := hHK
  obtain ⟨k, hk⟩ := hKH
  have hgi : (conjugate g H).index = H.index := Subgroup.index_map_equiv H (MulAut.conj g)
  have hki : (conjugate k K).index = K.index := Subgroup.index_map_equiv K (MulAut.conj k)
  letI : (conjugate g H).FiniteIndex := ⟨hgi ▸ Subgroup.FiniteIndex.index_ne_zero⟩
  letI : (conjugate k K).FiniteIndex := ⟨hki ▸ Subgroup.FiniteIndex.index_ne_zero⟩
  refine ⟨g, eq_of_le_of_not_lt hg ?_⟩
  intro hlt
  have h₁ := Subgroup.index_strictAnti hlt
  have h₂ := Subgroup.index_antitone hk
  rw [hgi] at h₁
  rw [hki] at h₂
  omega

end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Profinite F]

theorem locallyConjugate_map (H K : Subgroup G)
    (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (h : LocallyConjugate H K) (f : G →* F) (hf : Continuous f) :
    LocallyConjugate (H.map f) (K.map f) := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, Q, hP, hQ, g, hg⟩ := h p hp
  exact ⟨P.map f, Q.map f, sylowPro_map H P hH hP f hf,
    sylowPro_map K Q hK hQ f hf, f g,
    (conjugate_map f g P).symm.trans (congrArg (Subgroup.map f) hg)⟩

theorem pronilpotent_of_continuous_injective (hG : Pronilpotent G)
    (f : F →* G) (hf : Continuous f) (hi : Function.Injective f) : Pronilpotent F := by
  let e : F ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y he => hi (congrArg Subtype.val he), f.rangeRestrict_surjective⟩
  have he : Continuous e := hf.subtype_mk _
  have hei : Continuous e.symm := he.continuous_symm_of_equiv_compact_to_t2
  intro V
  exact nilpotent_of_pronilpotent_surjective (pronilpotent_subgroup hG f.range)
    ((QuotientGroup.mk' V.toSubgroup).comp e.symm.toMonoidHom)
    (continuous_quotient_mk'.comp hei)
    ((QuotientGroup.mk'_surjective V.toSubgroup).comp e.symm.surjective)

theorem profinite_conjugacy_case_map (N : Subgroup G) [N.Normal]
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) [(N.map f).Normal]
    (h : Prosupersolvable G ∨ Pronilpotent (G ⧸ N)) :
    Prosupersolvable F ∨ Pronilpotent (F ⧸ N.map f) := by
  rcases h with h | h
  · exact Or.inl (prosupersolvable_of_continuous_surjective h f hf hs)
  · exact Or.inr (pronilpotent_quotient_image N f hf hs h)

end Topology

section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

theorem closed_sup_normal (D H : Subgroup G) [D.Normal]
    (hD : IsClosed (D : Set G)) (hH : IsClosed (H : Set G)) :
    IsClosed ((D ⊔ H : Subgroup G) : Set G) := by
  rw [Subgroup.normal_mul]
  exact hH.mul_left_of_isCompact hD.isCompact

theorem profinite_conjugacy_case_subgroup (N L : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hL : IsClosed (L : Set G))
    (h : Prosupersolvable G ∨ Pronilpotent (G ⧸ N)) :
    Prosupersolvable L ∨ Pronilpotent (L ⧸ N.subgroupOf L) := by
  rcases h with h | h
  · exact Or.inl (prosupersolvable_subgroup h L)
  · letI := profinite_closed_subgroup L hL
    letI := profinite_quotient N hN
    letI := profinite_quotient (N.subgroupOf L) (hN.preimage continuous_subtype_val)
    let f := (QuotientGroup.mk' N).comp L.subtype
    let φ := QuotientGroup.lift (N.subgroupOf L) f (by
      intro x hx
      exact (QuotientGroup.eq_one_iff (x : G)).mpr hx)
    apply Or.inr
    apply pronilpotent_of_continuous_injective h φ
    · exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (continuous_quotient_mk'.comp continuous_subtype_val)
    · intro x y
      induction x using QuotientGroup.induction_on with | H x =>
        induction y using QuotientGroup.induction_on with | H y =>
          intro he
          change QuotientGroup.mk' N (x : G) = QuotientGroup.mk' N (y : G) at he
          have hm : (x : G)⁻¹ * (y : G) ∈ N := QuotientGroup.eq.mp he
          exact QuotientGroup.eq.mpr hm

/-- The coprime intersection identity, without finiteness of the ambient group. -/
theorem inf_sup_eq_of_coprime_profinite (A B H : Subgroup G) [A.Normal] [B.Normal]
    (hH : IsClosed (H : Set G)) (hcop : (Nat.card A).Coprime (Nat.card B)) :
    (A ⊔ H) ⊓ (B ⊔ H) = H := by
  apply le_antisymm _ (le_inf le_sup_right le_sup_right)
  apply subgroup_le_of_finite_images _ H hH
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  have hc : (Nat.card (A.map π)).Coprime (Nat.card (B.map π)) :=
    hcop.of_dvd (A.card_map_dvd π) (B.card_map_dvd π)
  rw [← inf_sup_eq_of_coprime (A.map π) (B.map π) (H.map π) hc]
  simpa only [Subgroup.map_sup] using
    (le_inf (Subgroup.map_mono (show (A ⊔ H) ⊓ (B ⊔ H) ≤ A ⊔ H from inf_le_left))
      (Subgroup.map_mono (show (A ⊔ H) ⊓ (B ⊔ H) ≤ B ⊔ H from inf_le_right)))

theorem merge_coprime_conjugators_profinite (A B H K : Subgroup G) [A.Normal] [B.Normal]
    (hK : IsClosed (K : Set G)) (hcop : (Nat.card A).Coprime (Nat.card B))
    (hdis : Disjoint A B) (a : A) (b : B)
    (hA : conjugate (b : G) H ≤ A ⊔ K) (hB : conjugate (a : G) H ≤ B ⊔ K) :
    conjugate ((a : G) * b) H ≤ K := by
  rw [← inf_sup_eq_of_coprime_profinite A B K hK hcop]
  apply le_inf
  · rw [← conjugate_comp]
    exact (conjugate_mono (a : G) hA).trans_eq
      (conjugate_eq_self_of_mem (A ⊔ K) ((show A ≤ A ⊔ K from le_sup_left) a.property))
  · have hc := Subgroup.commute_of_normal_of_disjoint A B inferInstance inferInstance hdis
      a b a.property b.property
    rw [hc.eq, ← conjugate_comp]
    exact (conjugate_mono (b : G) hB).trans_eq
      (conjugate_eq_self_of_mem (B ⊔ K) ((show B ≤ B ⊔ K from le_sup_left) b.property))

end Profinite
end LocalConjugacy
