module

public import LocalConjugacy.SylowFiniteImages
public import LocalConjugacy.QuotientReduction

@[expose] public section

namespace LocalConjugacy
open scoped Pointwise

section Algebra
variable {G F : Type*} [Group G] [Group F]

theorem sup_eq_top_of_supplements (N H : Subgroup G) (h : Supplements N H) :
    N ⊔ H = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, hn, y, hy, rfl⟩ := h x
  exact (N ⊔ H).mul_mem ((show N ≤ N ⊔ H from le_sup_left) hn)
    ((show H ≤ N ⊔ H from le_sup_right) hy)

theorem supplements_of_sup_eq_top (N H : Subgroup G) [N.Normal]
    (h : N ⊔ H = ⊤) : Supplements N H := by
  intro x
  have he := Subgroup.normal_mul N H
  rw [h] at he
  have hx : x ∈ (N : Set G) * (H : Set G) := by rw [← he]; trivial
  exact hx

theorem supplements_map (N H : Subgroup G) (h : Supplements N H)
    (f : G →* F) (hf : Function.Surjective f) : Supplements (N.map f) (H.map f) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  obtain ⟨n, hn, z, hz, rfl⟩ := h x
  exact ⟨f n, Subgroup.mem_map_of_mem f hn, f z, Subgroup.mem_map_of_mem f hz,
    (map_mul f n z).symm⟩

theorem commutative_map (N : Subgroup G) (hcomm : ∀ n m : N, n * m = m * n)
    (f : G →* F) : ∀ n m : N.map f, n * m = m * n := by
  rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
  apply Subtype.ext
  change f x * f y = f y * f x
  rw [← map_mul, ← map_mul]
  exact congrArg f (congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩))

theorem intersectionNormal_of_commutative (N H : Subgroup G)
    (hcomm : ∀ n m : N, n * m = m * n) : IntersectionNormal N H := by
  intro n hn d hd
  have he := congrArg Subtype.val (hcomm ⟨n, hn⟩ ⟨d, hd.1⟩)
  change n * d = d * n at he
  rw [he, mul_inv_cancel_right]
  exact hd

theorem conjugate_le_of_quotient (D H K : Subgroup G) [D.Normal] (hDH : D ≤ H)
    (q : G ⧸ D) (hq : conjugate q (K.map (QuotientGroup.mk' D)) ≤
      H.map (QuotientGroup.mk' D)) : ∃ g : G, conjugate g K ≤ H := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
  refine ⟨g, ?_⟩
  intro x hx
  let π := QuotientGroup.mk' D
  have hm : π x ∈ H.map π := by
    apply hq
    rw [← conjugate_map]
    exact Subgroup.mem_map_of_mem π hx
  change x ∈ (H.map π).comap π at hm
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk', sup_eq_left.mpr hDH] using hm

end Algebra

end LocalConjugacy
