module

public import LocalConjugacy.Definitions

@[expose] public section

/-! Algebraic quotient reduction from the earlier local development, rechecked here. -/

namespace LocalConjugacy

open Subgroup QuotientGroup

variable {G : Type*} [Group G]

/-- The repaired hypothesis: `N ⊓ H` is normalised by `N`.
For `H = G_α` a point stabiliser this says the stabiliser `N_α = N ⊓ G_α` is normal in `N`. -/
abbrev StabNormal := @IntersectionNormal

/-- **Step 1.** If `H` supplements the normal subgroup `N` and `N ⊓ H` is normalised by `N`,
then `N ⊓ H` is normal in the whole group.  (`N ⊓ H` is always normalised by `H`; the new
hypothesis supplies the other half, and `N ⊔ H = ⊤` glues them.) -/
theorem inf_normal_of_stabNormal (N H : Subgroup G) [hN : N.Normal]
    (hsup : N ⊔ H = ⊤) (hstab : StabNormal N H) : (N ⊓ H).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff, ← hsup]
  refine sup_le (le_normalizer_iff.mpr hstab) (le_normalizer_iff.mpr ?_)
  intro h hh d hd
  exact ⟨hN.conj_mem d hd.1 h, H.mul_mem (H.mul_mem hh hd.2) (H.inv_mem hh)⟩

/-- **Step 2.** Once `D = N ⊓ H` is normal, the image of `H` in `G ⧸ D` is a genuine complement
to the image of `N` — so the conjugacy theorem for complements becomes applicable. -/
theorem isComplement'_map_mk' (N H : Subgroup G) [N.Normal] [(N ⊓ H).Normal]
    (hsup : N ⊔ H = ⊤) :
    IsComplement' (N.map (mk' (N ⊓ H))) (H.map (mk' (N ⊓ H))) := by
  have hsurj : Function.Surjective (mk' (N ⊓ H)) := mk'_surjective _
  refine isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff_inf_le]
    rintro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx1
    obtain ⟨h, hh, hnh⟩ := Subgroup.mem_map.mp hx2
    obtain ⟨z, hz, hzz⟩ := (mk'_eq_mk' _).mp hnh.symm
    have hnH : n ∈ H := by
      have hz' : h * z⁻¹ ∈ H := H.mul_mem hh (H.inv_mem hz.2)
      rwa [← hzz, mul_inv_cancel_right] at hz'
    have : n ∈ N ⊓ H := ⟨hn, hnH⟩
    simpa using (QuotientGroup.eq_one_iff (N := N ⊓ H) n).mpr this
  · have hmap : (N.map (mk' (N ⊓ H))) ⊔ (H.map (mk' (N ⊓ H))) = ⊤ := by
      rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ hsurj]
    have := Subgroup.normal_mul (N.map (mk' (N ⊓ H))) (H.map (mk' (N ⊓ H)))
    rw [hmap] at this
    simpa using this.symm

/-- **Step 3.** A conjugacy statement in `G ⧸ (N ⊓ H)` descends to the inclusion `J^g ≤ H`,
because `N ⊓ H ≤ H`. -/
theorem le_of_map_mk'_eq (N J H : Subgroup G) [(N ⊓ H).Normal] (g : G)
    (hq : H.map (mk' (N ⊓ H)) = (J.map (MulAut.conj g)).map (mk' (N ⊓ H))) :
    J.map (MulAut.conj g) ≤ H := by
  intro x hx
  have hmem : (mk' (N ⊓ H)) x ∈ H.map (mk' (N ⊓ H)) := by
    rw [hq]; exact Subgroup.mem_map_of_mem _ hx
  obtain ⟨h, hh, hxh⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨z, hz, hzz⟩ := (mk'_eq_mk' _).mp hxh
  have : h * z ∈ H := H.mul_mem hh hz.2
  rwa [hzz] at this

/-- **The repaired theorem.**  With the new hypothesis `StabNormal N H`, the inclusion statement
follows from the conjugacy theorem for complements (Theorem 1.1 of the paper), applied in
`G ⧸ (N ⊓ H)`: no separate induction is needed. -/
theorem exists_conj_le_of_conjugacy (N J H : Subgroup G) [N.Normal]
    (hsup : N ⊔ H = ⊤) (hstab : StabNormal N H)
    (conjThm : ∀ _ : (N ⊓ H).Normal,
      IsComplement' (N.map (mk' (N ⊓ H))) (H.map (mk' (N ⊓ H))) →
        ∃ g : G, H.map (mk' (N ⊓ H)) = (J.map (MulAut.conj g)).map (mk' (N ⊓ H))) :
    ∃ g : G, J.map (MulAut.conj g) ≤ H := by
  have hD : (N ⊓ H).Normal := inf_normal_of_stabNormal N H hsup hstab
  obtain ⟨g, hg⟩ := conjThm hD (isComplement'_map_mk' N H hsup)
  exact ⟨g, le_of_map_mk'_eq N J H g hg⟩

end LocalConjugacy
