module

public import LocalConjugacy.StructuralImages
public import LocalConjugacy.SylowFiniteImages

@[expose] public section

namespace LocalConjugacy

variable {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]

theorem sylowPro_normal_of_pronilpotent (hJ : Pronilpotent J)
    {p : ℕ} [Fact p.Prime] (P : Subgroup J) (hP : IsSylowPro p ⊤ P) : P.Normal := by
  constructor
  intro x hx j
  apply mem_of_mem_sup_openNormal P hP.2.1
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  letI := hJ U
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  have hxS : π x ∈ S.toSubgroup := by
    rw [← hS]
    exact Subgroup.mem_map_of_mem π hx
  have hm : π (j * x * j⁻¹) ∈ P.map π := by
    rw [hS]
    simpa only [map_mul, map_inv] using
      (inferInstance : S.toSubgroup.Normal).conj_mem (π x) hxS (π j)
  change j * x * j⁻¹ ∈ (P.map π).comap π at hm
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using hm

/-- A Sylow at a prime absent from all finite quotient orders is trivial. -/
theorem sylowPro_eq_bot_of_not_primeDivisor {p : ℕ} [Fact p.Prime]
    (P : Subgroup J) (hP : IsSylowPro p ⊤ P)
    (hp : ∀ U : OpenNormalSubgroup J, ¬ p ∣ Nat.card (J ⧸ U.toSubgroup)) : P = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply mem_of_mem_sup_openNormal (⊥ : Subgroup J) (isClosed_singleton : IsClosed ({1} : Set J))
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  have hc : Nat.card S = 1 := S.isPGroup'.card_eq_or_dvd.resolve_right
    (fun h => hp U (h.trans (Subgroup.card_subgroup_dvd_card S.toSubgroup)))
  have hb : S.toSubgroup = ⊥ := Subgroup.card_eq_one.mp hc
  have hm : π x ∈ S.toSubgroup := by rw [← hS]; exact Subgroup.mem_map_of_mem π hx
  rw [hb, Subgroup.mem_bot] at hm
  have hu : x ∈ U := (QuotientGroup.eq_one_iff x).mp hm
  exact (show U.toSubgroup ≤ ⊥ ⊔ U.toSubgroup from le_sup_right) hu

end LocalConjugacy
