module

public import LocalConjugacy.ComplementSupersolvable
public import LocalConjugacy.Supplements

@[expose] public section

namespace LocalConjugacy

section Algebra
variable {G F : Type*} [Group G] [Group F]

theorem Conjugate.symm {H K : Subgroup G} (h : Conjugate H K) : Conjugate K H := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g⁻¹, conjugate_inv_cancel g H⟩

theorem Conjugate.trans {H K L : Subgroup G} (h : Conjugate H K)
    (h' : Conjugate K L) : Conjugate H L := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨k, hk⟩ := h'
  exact ⟨k * g, (conjugate_comp k g H).symm.trans hk⟩

theorem conjugate_eq_self_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) :
    conjugate g H = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
  · intro x hx
    refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem normal_conjugator (N H K : Subgroup G) (hs : Supplements N H)
    (hc : Conjugate H K) : ∃ n : N, conjugate (n : G) H = K := by
  obtain ⟨g, hg⟩ := hc
  obtain ⟨n, hn, h, hh, rfl⟩ := hs g
  refine ⟨⟨n, hn⟩, ?_⟩
  rw [← conjugate_comp, conjugate_eq_self_of_mem H hh] at hg
  exact hg

theorem conjugate_of_map_eq (D H K : Subgroup G) [D.Normal]
    (hDH : D ≤ H) (hDK : D ≤ K)
    (hc : Conjugate (H.map (QuotientGroup.mk' D)) (K.map (QuotientGroup.mk' D))) :
    Conjugate H K := by
  obtain ⟨q, hq⟩ := hc
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
  refine ⟨g, ?_⟩
  have he := congrArg (Subgroup.comap (QuotientGroup.mk' D)) hq
  rw [← conjugate_map, Subgroup.comap_map_eq, Subgroup.comap_map_eq,
    QuotientGroup.ker_mk', sup_eq_left.mpr hDK] at he
  have hDg : D ≤ conjugate g H := by
    rw [← Subgroup.Normal.map_conj_eq D g]
    exact Subgroup.map_mono hDH
  rwa [sup_eq_left.mpr hDg] at he

theorem nilpotent_of_injective_hom (f : G →* F) (hi : Function.Injective f)
    [Group.IsNilpotent F] : Group.IsNilpotent G := by
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hi (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  exact Group.nilpotent_of_mulEquiv e.symm

theorem nilpotent_quotient_image (N : Subgroup G) [N.Normal]
    [Group.IsNilpotent (G ⧸ N)] (f : G →* F) (hs : Function.Surjective f)
    [(N.map f).Normal] :
    Group.IsNilpotent (F ⧸ N.map f) := by
  let φ := QuotientGroup.map N (N.map f) f (Subgroup.le_comap_map f N)
  apply Group.nilpotent_of_surjective φ
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (N.map f) y
  obtain ⟨x, rfl⟩ := hs z
  exact ⟨QuotientGroup.mk' N x, rfl⟩

theorem nilpotent_quotient_subgroup (N L : Subgroup G) [N.Normal]
    [Group.IsNilpotent (G ⧸ N)] : Group.IsNilpotent (L ⧸ N.subgroupOf L) := by
  let f := (QuotientGroup.mk' N).comp L.subtype
  let φ := QuotientGroup.lift (N.subgroupOf L) f (by
    intro x hx
    exact (QuotientGroup.eq_one_iff (x : G)).mpr hx)
  apply nilpotent_of_injective_hom φ
  intro x y
  induction x using QuotientGroup.induction_on with | H x =>
    induction y using QuotientGroup.induction_on with | H y =>
      intro h
      change QuotientGroup.mk' N (x : G) = QuotientGroup.mk' N (y : G) at h
      have hm : (x : G)⁻¹ * (y : G) ∈ N := QuotientGroup.eq.mp h
      exact QuotientGroup.eq.mpr hm

end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [Profinite G] [TopologicalSpace F] [Finite F] [DiscreteTopology F]

theorem locallyConjugate_map_finite (H K : Subgroup G)
    (hH : IsClosed (H : Set G)) (hK : IsClosed (K : Set G))
    (h : LocallyConjugate H K) (f : G →* F) (hf : Continuous f) :
    LocallyConjugate (H.map f) (K.map f) := by
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, Q, hP, hQ, g, hg⟩ := h p hp
  exact ⟨P.map f, Q.map f, sylowPro_map_finite H P hH hP f hf,
    sylowPro_map_finite K Q hK hQ f hf, f g,
    (conjugate_map f g P).symm.trans (congrArg (Subgroup.map f) hg)⟩

theorem LocallyConjugate.conjugate_left {H K : Subgroup G}
    (h : LocallyConjugate H K) (g : G) : LocallyConjugate (conjugate g H) K := by
  intro p hp
  obtain ⟨P, Q, hP, hQ, k, hk⟩ := h p hp
  refine ⟨conjugate g P, Q, isSylowPro_conjugate g H P hP, hQ, k * g⁻¹, ?_⟩
  rw [conjugate_comp, inv_mul_cancel_right]
  exact hk

end Topology

section Finite
variable {G : Type*} [Group G] [Finite G]

theorem index_eq_relIndex_of_supplements (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) : H.index = H.relIndex N := by
  have hi : N.relIndex H = N.index := by
    rw [← Subgroup.relIndex_sup_left H N, sup_eq_top_of_supplements N H hs,
      Subgroup.relIndex_top_right]
  have h1 := Subgroup.relIndex_inf_mul_relIndex (⊥ : Subgroup G) N H
  have h2 := Subgroup.relIndex_inf_mul_relIndex (⊥ : Subgroup G) H N
  simp only [Subgroup.relIndex_bot_left, bot_inf_eq] at h1 h2
  rw [inf_comm] at h2
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H))
  calc
    Nat.card H * H.index = Nat.card G := H.card_mul_index
    _ = Nat.card N * N.index := N.card_mul_index.symm
    _ = (Nat.card (N ⊓ H : Subgroup G) * H.relIndex N) * N.relIndex H := by rw [h2, hi]
    _ = (Nat.card (N ⊓ H : Subgroup G) * N.relIndex H) * H.relIndex N := by ac_rfl
    _ = Nat.card H * H.relIndex N := by rw [h1]

theorem index_dvd_card_of_supplements (N H : Subgroup G) [N.Normal]
    (hs : Supplements N H) : H.index ∣ Nat.card N := by
  rw [index_eq_relIndex_of_supplements N H hs]
  exact H.relIndex_dvd_card N

/-- Quotienting by a nontrivial subgroup of N decreases the induction parameter. -/
theorem card_map_quotient_lt (N D : Subgroup G) [D.Normal]
    (hDN : D ≤ N) (hD : D ≠ ⊥) :
    Nat.card (N.map (QuotientGroup.mk' D)) < Nat.card N := by
  let f : N →* N.map (QuotientGroup.mk' D) :=
    ((QuotientGroup.mk' D).comp N.subtype).codRestrict _
      (fun x => Subgroup.mem_map_of_mem _ x.property)
  have hs : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
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

end Finite
end LocalConjugacy
