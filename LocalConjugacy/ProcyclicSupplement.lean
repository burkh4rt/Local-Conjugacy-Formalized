module

public import LocalConjugacy.SylowFiniteImages
public import LocalConjugacy.Supplements

@[expose] public section

namespace LocalConjugacy

variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

theorem procyclic_zpowers_closure (x : G) :
    Procyclic (Subgroup.zpowers x).topologicalClosure := by
  let Q := (Subgroup.zpowers x).topologicalClosure
  let y : Q := ⟨x, (Subgroup.zpowers x).le_topologicalClosure (Subgroup.mem_zpowers x)⟩
  refine ⟨y, ?_⟩
  rw [Subtype.dense_iff]
  have he : Subtype.val '' (Subgroup.zpowers y : Set Q) = (Subgroup.zpowers x : Set G) := by
    change ((Subgroup.zpowers y).map Q.subtype : Set G) = _
    rw [MonoidHom.map_zpowers]
    rfl
  change (Q : Set G) ⊆ closure (Subtype.val '' (Subgroup.zpowers y : Set Q))
  rw [he]
  exact fun _ hx => hx

/-- A closed normal subgroup of prime index has a closed procyclic pro-prime
supplement. The ambient profinite group need not be finite or solvable. -/
theorem exists_procyclic_supplement (K : Subgroup G) [K.Normal]
    (hK : IsClosed (K : Set G)) {q : ℕ} [Fact q.Prime] (hi : K.index = q) :
    ∃ Q : Subgroup G, IsClosed (Q : Set G) ∧ Procyclic Q ∧ IsProP q Q ∧ Supplements K Q := by
  letI : K.FiniteIndex := ⟨hi ▸ (Fact.out : q.Prime).ne_zero⟩
  letI : IsOpen (K : Set G) := K.isOpen_of_isClosed_of_finiteIndex hK
  letI : DiscreteTopology (G ⧸ K) := inferInstance
  have hc : Nat.card (G ⧸ K) = q := hi
  letI : IsCyclic (G ⧸ K) := isCyclic_of_prime_card hc
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G ⧸ K)
  obtain ⟨P, hP⟩ := exists_sylowPro (G := G) q
  let π := QuotientGroup.mk' K
  obtain ⟨S, hS⟩ := sylowPro_map_surjective_finite P hP π
    continuous_quotient_mk' (QuotientGroup.mk'_surjective K)
  have ht : S.toSubgroup = ⊤ := (S.is_maximal'
    ((IsPGroup.of_card (p := q) (n := 1) (by simpa using hc)).to_subgroup ⊤) le_top).symm
  have hzP : z ∈ P.map π := by rw [hS, ht]; trivial
  obtain ⟨x, hx, hπx⟩ := hzP
  let Q := (Subgroup.zpowers x).topologicalClosure
  have hQP : Q ≤ P := (Subgroup.zpowers x).topologicalClosure_minimal
    (Subgroup.zpowers_le.mpr hx) hP.2.1
  refine ⟨Q, (Subgroup.zpowers x).isClosed_topologicalClosure,
    procyclic_zpowers_closure x, isProP_mono hQP hP.2.2.1, ?_⟩
  intro g
  obtain ⟨n, hn⟩ := hz (π g)
  refine ⟨g * (x ^ n)⁻¹, ?_, x ^ n,
    (Subgroup.zpowers x).le_topologicalClosure (Subgroup.zpow_mem_zpowers x n), by group⟩
  rw [← QuotientGroup.eq_one_iff]
  change π (g * (x ^ n)⁻¹) = 1
  rw [map_mul, map_inv, map_zpow, hπx]
  change π g * (z ^ n)⁻¹ = 1
  change z ^ n = π g at hn
  rw [hn, mul_inv_cancel]

end LocalConjugacy
