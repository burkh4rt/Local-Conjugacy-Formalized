module

public import LocalConjugacy.HallCohomology
public import LocalConjugacy.ActionProductTopology

@[expose] public section

namespace LocalConjugacy

theorem HasProPrimes.map {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [IsTopologicalGroup F]
    {π : Set ℕ} (H : Subgroup G) (hH : HasProPrimes π H)
    (f : G →* F) (hf : Continuous f) : HasProPrimes π (H.map f) := by
  intro V
  let φ := subgroupImageHom H f
  let ψ := (QuotientGroup.mk' V.toSubgroup).comp φ
  exact hH.of_continuous_surjective ψ
    (continuous_quotient_mk'.comp ((hf.comp continuous_subtype_val).subtype_mk _))
    ((QuotientGroup.mk'_surjective V.toSubgroup).comp (subgroupImageHom_surjective H f))

section Action
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

theorem prosupersolvable_acting_group (hG : Prosupersolvable (ActionProduct J N)) :
    Prosupersolvable J := by
  intro U
  exact supersolvable_of_prosupersolvable_surjective hG
    ((QuotientGroup.mk' U.toSubgroup).comp SemidirectProduct.rightHom)
    (continuous_quotient_mk'.comp actionProduct_continuous_right)
    ((QuotientGroup.mk'_surjective U.toSubgroup).comp SemidirectProduct.rightHom_surjective)

/-- In the manuscript's semidirect product, the high-prime Hall factor
acts trivially on the p-group of coefficients. -/
theorem prosupersolvable_action_trivial_on_high_primes
    (hG : Prosupersolvable (ActionProduct J N)) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (M : Subgroup J) (hM : HasProPrimes {r | p < r} M) :
    ∀ (m : M) (n : N), (m : J) • n = n := by
  let i : N →* ActionProduct J N := SemidirectProduct.inl
  let j : J →* ActionProduct J N := SemidirectProduct.inr
  let A := i.range
  have hn : A.Normal := by
    change (SemidirectProduct.inl : N →* ActionProduct J N).range.Normal
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  letI := hn
  have hpA : IsProP p A := proP_of_isPGroup
    (hN.of_surjective i.rangeRestrict i.rangeRestrict_surjective)
  have hpM := hM.map M j actionProduct_continuous_inr
  intro m n
  have hc := prosupersolvable_commute_normal_proP hG A (M.map j) hpA hpM
    ⟨i n, n, rfl⟩ ⟨j m, Subgroup.mem_map_of_mem j m.property⟩
  have he := congrArg SemidirectProduct.left hc.eq
  change n * ((1 : J) • (1 : N)) = 1 * ((m : J) • n) at he
  simpa only [one_smul, mul_one, one_mul] using he.symm

/-- The two structural reductions needed by Zorn, with all Hall and
centralization facts derived from prosupersolvability of the semidirect product. -/
theorem supersolvable_hall_or_prime_index_reduction
    (hG : Prosupersolvable (ActionProduct J N)) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (P : Subgroup J) (hP : IsSylowPro p ⊤ P) (hproper : P ≠ ⊤) :
    (∃ M Q : Subgroup J, M.Normal ∧ IsHallPro {r | p < r} M ∧
      IsHallPro {r | r ≤ p} Q ∧ M.IsComplement' Q ∧ P ≤ Q ∧ Q < ⊤ ∧
      RestrictionIsomorphism (N := N) ⊤ Q le_top) ∨
    (P.Normal ∧ ∃ K : OpenNormalSubgroup J, P ≤ K.toSubgroup ∧
      K.toSubgroup.index.Prime ∧ K.toSubgroup.index ≠ p) := by
  classical
  have hJ := prosupersolvable_acting_group hG
  by_cases hlarge : ∃ (U : OpenNormalSubgroup J) (q : ℕ), q.Prime ∧
      q ∣ Nat.card (J ⧸ U.toSubgroup) ∧ p < q
  · obtain ⟨M, Q, hMn, hM, hQ, hMQ, hPQ⟩ :=
      prosupersolvable_hall_split_containing hJ le_rfl P hP
    letI := hMn
    have hact := prosupersolvable_action_trivial_on_high_primes hG hN M hM.hasProPrimes
    exact Or.inl ⟨M, Q, hMn, hM, hQ, hMQ, hPQ, lt_top_iff_ne_top.mpr
      (hall_complement_proper hQ hlarge),
      hall_complement_restriction hN M Q hM.1 hQ.1 hMQ hM.hasProPrimes hact⟩
  · have hprimes (U : OpenNormalSubgroup J) : HasPrimes {r | r ≤ p} (J ⧸ U.toSubgroup) := by
      intro q hq hd
      exact Nat.le_of_not_gt (fun hpq => hlarge ⟨U, q, hq, hd, hpq⟩)
    have hn := sylowPro_normal_of_prosupersolvable_largest hJ hprimes P hP
    letI := hn
    exact Or.inr ⟨hn, prosupersolvable_prime_index_above_normal_sylow hJ P hP hproper⟩

end Action
end LocalConjugacy
