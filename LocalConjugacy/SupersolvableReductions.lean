module

public import LocalConjugacy.ProfiniteHall
public import LocalConjugacy.CocycleDescent

@[expose] public section

namespace LocalConjugacy

theorem hasPrimes_singleton_iff_isPGroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] : HasPrimes {p} G ↔ IsPGroup p G := by
  constructor
  · intro h
    apply (isPGroup_iff_primeFactors_card_subset hp.out.ne_zero).mpr
    intro q hq
    obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    have he : q = p := h q hqprime hqdvd
    rw [he]
    exact Nat.mem_primeFactors.mpr ⟨hp.out, dvd_rfl, hp.out.ne_zero⟩
  · intro h q hq hd
    obtain ⟨k, hk⟩ := h.exists_card_eq
    rw [hk] at hd
    exact (Nat.prime_dvd_prime_iff_eq hq hp.out).mp (hq.dvd_of_dvd_pow hd)

/-- When no larger prime occurs, the Sylow subgroup at the cutoff is normal. -/
theorem supersolvable_largest_sylow_normal {G : Type*} [Group G] [Finite G]
    (hG : Supersolvable G) {p : ℕ} [hp : Fact p.Prime]
    (hprimes : HasPrimes {r | r ≤ p} G) (P : Sylow p G) : P.toSubgroup.Normal := by
  obtain ⟨M, hMn, hM⟩ := supersolvable_exists_normalHall hG (p - 1)
  letI := hMn
  have hp2 := hp.out.two_le
  have hMp : IsPGroup p M := hasPrimes_singleton_iff_isPGroup.mp (by
    intro r hr hd
    have hlo := hM.1 r hr hd
    have hhi := hprimes r hr (hd.trans M.card_subgroup_dvd_card)
    change r = p
    change p - 1 < r at hlo
    change r ≤ p at hhi
    omega)
  have hPprimes : HasPrimes {r | p - 1 < r} P := by
    intro r hr hd
    have he : r = p := hasPrimes_singleton_iff_isPGroup.mpr P.isPGroup' r hr hd
    change p - 1 < r
    omega
  have hPM := hPprimes.le_normalHall hM
  exact P.is_maximal' hMp hPM ▸ hMn

universe u

/-- A nontrivial finite supersolvable group has a normal subgroup of prime index. -/
theorem supersolvable_exists_prime_index {G : Type u} [Group G] [Finite G]
    [Nontrivial G] (hG : Supersolvable G) :
    ∃ K : Subgroup G, K.Normal ∧ K.index.Prime := by
  suffices h : ∀ k : ℕ, ∀ {G : Type u} [Group G] [Finite G] [Nontrivial G],
      Nat.card G = k → Supersolvable G → ∃ K : Subgroup G, K.Normal ∧ K.index.Prime by
    exact h (Nat.card G) rfl hG
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro G _ _ _ hcard hG
    obtain ⟨C, q, hCn, hq, hCcard⟩ := supersolvable_exists_prime_normal hG
    letI := hCn
    by_cases hC : C = ⊤
    · refine ⟨⊥, inferInstance, ?_⟩
      rw [hC, Subgroup.card_top] at hCcard
      simpa only [Subgroup.index_bot, hCcard] using hq
    · letI : Nontrivial (G ⧸ C) := QuotientGroup.nontrivial_iff.mpr hC
      have hquot : Nat.card (G ⧸ C) < k := by
        have hc := C.card_mul_index
        change Nat.card C * Nat.card (G ⧸ C) = Nat.card G at hc
        rw [hCcard, hcard] at hc
        have hpos := Nat.card_pos (α := G ⧸ C)
        have hq2 := hq.two_le
        nlinarith
      obtain ⟨K, hKn, hK⟩ := ih _ hquot rfl (supersolvable_of_surjective hG
        (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C))
      letI := hKn
      refine ⟨K.comap (QuotientGroup.mk' C), inferInstance, ?_⟩
      rwa [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective C)]

theorem supersolvable_prime_index_above_normal_sylow {G : Type*} [Group G] [Finite G]
    (hG : Supersolvable G) {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [P.toSubgroup.Normal] (hP : P.toSubgroup ≠ ⊤) :
    ∃ K : Subgroup G, K.Normal ∧ P.toSubgroup ≤ K ∧ K.index.Prime ∧ K.index ≠ p := by
  letI : Nontrivial (G ⧸ P.toSubgroup) := QuotientGroup.nontrivial_iff.mpr hP
  obtain ⟨D, hDn, hD⟩ := supersolvable_exists_prime_index
    (supersolvable_of_surjective hG (QuotientGroup.mk' P.toSubgroup)
      (QuotientGroup.mk'_surjective P.toSubgroup))
  letI := hDn
  let K := D.comap (QuotientGroup.mk' P.toSubgroup)
  have hPK : P.toSubgroup ≤ K := by
    simpa only [QuotientGroup.ker_mk'] using
      Subgroup.ker_le_comap (QuotientGroup.mk' P.toSubgroup) D
  have hKi : K.index = D.index := D.index_comap_of_surjective
    (QuotientGroup.mk'_surjective P.toSubgroup)
  refine ⟨K, inferInstance, hPK, hKi ▸ hD, fun he => ?_⟩
  have hd := Subgroup.index_dvd_of_le hPK
  rw [he] at hd
  exact P.not_dvd_index hd

section Profinite
variable {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]

/-- Every finite quotient of a subgroup factors through its image in an
ambient finite quotient. This also justifies inheritance of structural properties. -/
theorem subgroup_quotient_factors (H : Subgroup G) (V : OpenNormalSubgroup H) :
    ∃ U : OpenNormalSubgroup G,
      ∃ f : H.map (QuotientGroup.mk' U.toSubgroup) →* H ⧸ V.toSubgroup,
        Function.Surjective f := by
  classical
  obtain ⟨U, hU⟩ := exists_openNormal_le_subgroup_open H V
  let φ := subgroupImageHom H (QuotientGroup.mk' U.toSubgroup)
  let ψ := QuotientGroup.mk' V.toSubgroup
  have hker : φ.ker ≤ ψ.ker := by
    intro x hx
    apply (QuotientGroup.eq_one_iff (N := V.toSubgroup) x).mpr
    apply hU
    apply (QuotientGroup.eq_one_iff (N := U.toSubgroup) (x : G)).mp
    exact congrArg Subtype.val hx
  let f := φ.liftOfSurjective (subgroupImageHom_surjective H _) ⟨ψ, hker⟩
  refine ⟨U, f, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup y
  exact ⟨φ x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩

/-- Closed subgroups of prosupersolvable groups are prosupersolvable.
The algebraic conclusion even holds for the induced topology on any subgroup. -/
theorem prosupersolvable_subgroup (hG : Prosupersolvable G) (H : Subgroup G) :
    Prosupersolvable H := by
  intro V
  obtain ⟨U, f, hf⟩ := subgroup_quotient_factors H V
  exact supersolvable_of_surjective (supersolvable_subgroup (hG U) _) f hf

theorem sylowPro_normal_of_prosupersolvable_largest (hG : Prosupersolvable G)
    {p : ℕ} [Fact p.Prime] (hprimes : ∀ U : OpenNormalSubgroup G,
      HasPrimes {r | r ≤ p} (G ⧸ U.toSubgroup))
    (P : Subgroup G) (hP : IsSylowPro p ⊤ P) : P.Normal := by
  constructor
  intro x hx g
  apply mem_of_mem_sup_openNormal P hP.2.1
  intro U
  let π := QuotientGroup.mk' U.toSubgroup
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  have hn := supersolvable_largest_sylow_normal (hG U) (hprimes U) S
  have hxS : π x ∈ S.toSubgroup := hS ▸ Subgroup.mem_map_of_mem π hx
  have hh : π (g * x * g⁻¹) ∈ P.map π := by
    rw [hS]
    simpa only [map_mul, map_inv] using hn.conj_mem (π x) hxS (π g)
  change g * x * g⁻¹ ∈ (P.map π).comap π at hh
  simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using hh

/-- A proper normal Sylow subgroup in a prosupersolvable group is contained
in an open normal subgroup of prime index different from its own prime. -/
theorem prosupersolvable_prime_index_above_normal_sylow (hG : Prosupersolvable G)
    {p : ℕ} [Fact p.Prime] (P : Subgroup G) [P.Normal]
    (hP : IsSylowPro p ⊤ P) (hproper : P ≠ ⊤) :
    ∃ K : OpenNormalSubgroup G, P ≤ K.toSubgroup ∧ K.toSubgroup.index.Prime ∧
      K.toSubgroup.index ≠ p := by
  classical
  have hex : ∃ U : OpenNormalSubgroup G,
      P.map (QuotientGroup.mk' U.toSubgroup) ≠ ⊤ := by
    by_contra! h
    apply hproper
    apply top_unique
    exact subgroup_le_of_finite_images ⊤ P hP.2.1 (fun U => by rw [h U]; exact le_top)
  obtain ⟨U, hU⟩ := hex
  let π := QuotientGroup.mk' U.toSubgroup
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  letI : S.toSubgroup.Normal := by
    rw [← hS]
    exact (inferInstance : P.Normal).map π (QuotientGroup.mk'_surjective U.toSubgroup)
  obtain ⟨D, hDn, hSD, hDprime, hDne⟩ := supersolvable_prime_index_above_normal_sylow
    (hG U) S (hS ▸ hU)
  letI := hDn
  let K : OpenNormalSubgroup G :=
    { toSubgroup := D.comap π
      isOpen' := (isOpen_discrete (D : Set (G ⧸ U.toSubgroup))).preimage continuous_quotient_mk' }
  have hPK : P ≤ K.toSubgroup := by
    intro x hx
    exact hSD (hS ▸ Subgroup.mem_map_of_mem π hx)
  have hi : K.toSubgroup.index = D.index := D.index_comap_of_surjective
    (QuotientGroup.mk'_surjective U.toSubgroup)
  exact ⟨K, hPK, hi ▸ hDprime, hi ▸ hDne⟩

end Profinite
end LocalConjugacy
