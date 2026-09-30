module

public import LocalConjugacy.FiniteHall

@[expose] public section

namespace LocalConjugacy

theorem cyclic_step_comap {G H : Type*} [Group G] [Group H]
    (f : H →* G) (A B : Subgroup G) [A.Normal] (g : G)
    (hB : B = A ⊔ Subgroup.zpowers g) :
    ∃ h : H, B.comap f = A.comap f ⊔ Subgroup.zpowers h := by
  let π := QuotientGroup.mk' A
  let φ := π.comp f
  let T := B.comap f
  have hA : A ≤ B := hB ▸ le_sup_left
  have hBmap : B.map π = Subgroup.zpowers (π g) := by
    rw [hB, Subgroup.map_sup, MonoidHom.map_zpowers]
    have he : A.map π = ⊥ := by
      exact (Subgroup.map_eq_bot_iff A).mpr (le_of_eq (QuotientGroup.ker_mk' A).symm)
    rw [he, bot_sup_eq]
  have hle : T.map φ ≤ B.map π := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map_of_mem π hx
  letI : IsCyclic (B.map π) := hBmap ▸ inferInstance
  letI : IsCyclic (T.map φ) := Subgroup.isCyclic_of_le hle
  obtain ⟨y, hy⟩ := (T.map φ).isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hymem : y ∈ T.map φ := hy ▸ Subgroup.mem_zpowers y
  obtain ⟨h, hh, rfl⟩ := hymem
  refine ⟨h, ?_⟩
  have hker : φ.ker = A.comap f := by
    change (π.comp f).ker = _
    rw [← MonoidHom.comap_ker, show π.ker = A from QuotientGroup.ker_mk' A]
  have hmap : (A.comap f ⊔ Subgroup.zpowers h).map φ = T.map φ := by
    rw [Subgroup.map_sup, ← hker, Subgroup.map_ker_self, bot_sup_eq,
      MonoidHom.map_zpowers, hy]
  have hleft : (T.map φ).comap φ = T :=
    Subgroup.comap_map_eq_self (hker ▸ Subgroup.comap_mono hA)
  have hright : ((A.comap f ⊔ Subgroup.zpowers h).map φ).comap φ =
      A.comap f ⊔ Subgroup.zpowers h := Subgroup.comap_map_eq_self (hker ▸ le_sup_left)
  exact hleft.symm.trans ((congrArg (Subgroup.comap φ) hmap).symm.trans hright)

/-- Supersolvability passes to subgroups by intersecting the invariant series. -/
theorem supersolvable_subgroup {G : Type*} [Group G] (hG : Supersolvable G)
    (H : Subgroup G) : Supersolvable H := by
  obtain ⟨n, s, h0, hn, hm, hnormal, hstep⟩ := hG
  refine ⟨n, fun i => (s i).comap H.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [h0]
    exact H.subtype.ker_eq_bot Subtype.val_injective
  · simp only [hn, Subgroup.comap_top]
  · exact fun i j hij => Subgroup.comap_mono (hm hij)
  · intro i
    letI := hnormal i
    infer_instance
  · intro i hi
    letI := hnormal i
    obtain ⟨g, hg⟩ := hstep i hi
    exact cyclic_step_comap H.subtype (s i) (s (i + 1)) g hg

/-- A nontrivial supersolvable group contains a nontrivial cyclic normal subgroup. -/
theorem supersolvable_exists_cyclic_normal {G : Type*} [Group G] [Nontrivial G]
    (hG : Supersolvable G) :
    ∃ C : Subgroup G, C.Normal ∧ C ≠ ⊥ ∧ IsCyclic C := by
  classical
  obtain ⟨n, s, h0, hn, _, hnormal, hstep⟩ := hG
  have hex : ∃ i, s i ≠ ⊥ := ⟨n, hn ▸ top_ne_bot⟩
  let i := Nat.find hex
  have hi : s i ≠ ⊥ := Nat.find_spec hex
  have hi0 : i ≠ 0 := by intro he; exact hi (he ▸ h0)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hk0 : s k = ⊥ := by
    by_contra h
    have := Nat.find_min' hex h
    change i ≤ k at this
    omega
  have hin : i ≤ n := Nat.find_min' hex (hn ▸ top_ne_bot)
  obtain ⟨x, hx⟩ := hstep k (by omega)
  have hcyc : s i = Subgroup.zpowers x := by
    rw [hk, Nat.succ_eq_add_one, hx, hk0, bot_sup_eq]
  exact ⟨s i, hnormal i, hi, hcyc ▸ inferInstance⟩

/-- In the finite case one can choose the cyclic normal subgroup to have prime order. -/
theorem supersolvable_exists_prime_normal {G : Type*} [Group G] [Finite G]
    [Nontrivial G] (hG : Supersolvable G) :
    ∃ (C : Subgroup G) (q : ℕ), C.Normal ∧ q.Prime ∧ Nat.card C = q := by
  obtain ⟨B, hB, hB0, hcyc⟩ := supersolvable_exists_cyclic_normal hG
  letI := hB
  letI := hcyc
  letI : CommGroup B := IsCyclic.commGroup
  have hb : Nat.card B ≠ 1 := fun h => hB0 (B.eq_bot_iff_card.mpr h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hb
  let D : Subgroup B := (powMonoidHom q : B →* B).ker
  have hd : D.Characteristic := by
    apply Subgroup.characteristic_iff_le_comap.mpr
    intro e x hx
    change (e x) ^ q = 1
    change x ^ q = 1 at hx
    rw [← map_pow, hx, map_one]
  letI := hd
  refine ⟨D.map B.subtype, q, inferInstance, hq, ?_⟩
  rw [Subgroup.card_map_of_injective B.subtype_injective]
  change Nat.card (powMonoidHom q : B →* B).ker = q
  rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hqd]

universe u

/-- The finite Hall cutoff theorem, proved from an invariant cyclic series.
The normal Hall subgroup contains exactly the prime divisors above `n`. -/
theorem supersolvable_exists_normalHall {G : Type u} [Group G] [Finite G]
    (hG : Supersolvable G) (n : ℕ) :
    ∃ M : Subgroup G, M.Normal ∧ IsHall {p | n < p} M := by
  classical
  suffices h : ∀ k : ℕ, ∀ {G : Type u} [Group G] [Finite G], Nat.card G = k →
      Supersolvable G → ∃ M : Subgroup G, M.Normal ∧ IsHall {p | n < p} M by
    exact h (Nat.card G) rfl hG
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro G _ _ hcard hG
    rcases subsingleton_or_nontrivial G with htriv | hnontriv
    · letI := htriv
      refine ⟨⊥, inferInstance, ?_, ?_⟩
      · intro p hp hd
        have : p ∣ 1 := by simpa using hd
        exact (hp.not_dvd_one this).elim
      · intro p hp hd
        have : p ∣ 1 := by simpa using hd
        exact (hp.not_dvd_one this).elim
    · letI := hnontriv
      obtain ⟨C, q, hCnormal, hq, hCcard⟩ := supersolvable_exists_prime_normal hG
      letI := hCnormal
      let π := QuotientGroup.mk' C
      have hquot : Nat.card (G ⧸ C) < k := by
        have hc := C.card_mul_index
        change Nat.card C * Nat.card (G ⧸ C) = Nat.card G at hc
        rw [hCcard, hcard] at hc
        have hpos := Nat.card_pos (α := G ⧸ C)
        have hq2 := hq.two_le
        nlinarith
      obtain ⟨D, hDnormal, hD⟩ := ih _ hquot rfl
        (supersolvable_of_surjective hG π (QuotientGroup.mk'_surjective C))
      letI := hDnormal
      let K := D.comap π
      have hCK : C ≤ K := by
        simpa only [π, QuotientGroup.ker_mk'] using Subgroup.ker_le_comap π D
      have hKmap : K.map π = D := Subgroup.map_comap_eq_self (by
        rw [π.range_eq_top_of_surjective (QuotientGroup.mk'_surjective C)]
        exact le_top)
      have hKindex : K.index = D.index := D.index_comap_of_surjective (QuotientGroup.mk'_surjective C)
      have hCsubcard : Nat.card (C.subgroupOf K) = q :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK).toEquiv).trans hCcard
      have hCsubindex : (C.subgroupOf K).index = Nat.card D := by
        have hh := Subgroup.relIndex_ker K π
        simpa only [π, QuotientGroup.ker_mk', hKmap, Subgroup.relIndex] using hh
      have hKcard : Nat.card K = q * Nat.card D := by
        rw [← (C.subgroupOf K).card_mul_index, hCsubcard, hCsubindex]
      by_cases hqn : n < q
      · refine ⟨K, inferInstance, ?_, ?_⟩
        · intro p hp hd
          rw [hKcard] at hd
          rcases hp.dvd_mul.mp hd with hd | hd
          · exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd) ▸ hqn
          · exact hD.1 p hp hd
        · intro p hp hd
          exact hD.2 p hp (hKindex ▸ hd)
      · have hqn' : q ≤ n := Nat.le_of_not_gt hqn
        have hcop : (Nat.card (C.subgroupOf K)).Coprime (C.subgroupOf K).index := by
          rw [hCsubcard, hCsubindex]
          exact hq.coprime_iff_not_dvd.mpr (fun hd => hqn (hD.1 q hq hd))
        obtain ⟨M, hCM⟩ := Subgroup.exists_right_complement'_of_coprime hcop
        have hMcard : Nat.card M = Nat.card D := hCM.card_right.trans hCsubindex
        have hMprimes : HasPrimes {p | n < p} M := by
          intro p hp hd
          exact hD.1 p hp (hMcard ▸ hd)
        have hMnormal : M.Normal := normal_complement_of_commute hCM
          (commute_prime_normal_of_large_primes (C.subgroupOf K) M hq hCsubcard hqn' hMprimes)
        letI := hMnormal
        have hMindex : M.index = q := hCM.index_eq_card.trans hCsubcard
        have hMHall : IsHall {p | n < p} M := by
          refine ⟨hMprimes, fun p hp hd hn => ?_⟩
          rw [hMindex] at hd
          have he := (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
          exact hqn (he ▸ hn)
        letI := hMHall.characteristic_of_normal
        refine ⟨M.map K.subtype, inferInstance, hMprimes.map K.subtype, ?_⟩
        intro p hp hd hn
        rw [Subgroup.index_map_subtype, hMindex, hKindex] at hd
        rcases hp.dvd_mul.mp hd with hd | hd
        · exact hqn ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd ▸ hn)
        · exact hD.2 p hp hd hn

/-- The finite split Hall decomposition for a prime cutoff. -/
theorem supersolvable_hall_split {G : Type*} [Group G] [Finite G]
    (hG : Supersolvable G) (n : ℕ) :
    ∃ M Q : Subgroup G, M.Normal ∧ IsHall {p | n < p} M ∧
      M.IsComplement' Q ∧ IsHall {p | p ≤ n} Q := by
  obtain ⟨M, hMn, hM⟩ := supersolvable_exists_normalHall hG n
  letI := hMn
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime hM.coprime
  refine ⟨M, Q, hMn, hM, hQ, ?_, ?_⟩
  · intro p hp hd
    have hn := hM.2 p hp (hQ.card_right ▸ hd)
    exact Nat.le_of_not_gt hn
  · intro p hp hd hn
    have hh := hM.1 p hp (hQ.index_eq_card ▸ hd)
    exact Nat.not_lt_of_ge hn hh

/-- The Hall complement can be chosen to contain any prescribed Sylow
subgroup at a prime below the cutoff. -/
theorem supersolvable_hall_split_containing {G : Type*} [Group G] [Finite G]
    (hG : Supersolvable G) {n p : ℕ} [Fact p.Prime] (hpn : p ≤ n)
    (P : Sylow p G) (M : Subgroup G) [M.Normal] (hM : IsHall {r | n < r} M) :
    ∃ Q : Subgroup G, M.IsComplement' Q ∧ IsHall {r | r ≤ n} Q ∧ P.toSubgroup ≤ Q := by
  obtain ⟨M', Q, hM'n, hM', hMQ, hQ⟩ := supersolvable_hall_split hG n
  letI := hM'n
  have he : M' = M := hM'.eq_of_normal hM
  subst M'
  obtain ⟨g, hg⟩ := exists_conjugate_sylow_le_of_not_dvd_index P Q
    (fun hd => hQ.2 p Fact.out hd hpn)
  let e := (MulAut.conj g⁻¹).toMonoidHom
  have hMe : M.map e = M := Subgroup.Normal.map_conj_eq M g⁻¹
  have hQe := hQ.map_surjective e (MulAut.conj g⁻¹).surjective
  have hce := complement_map_of_disjoint hMQ e (MulAut.conj g⁻¹).surjective
    (disjoint_of_cutoff_primes (hM.1.map e) hQe.1)
  rw [hMe] at hce
  exact ⟨Q.map e, hce, hQe, (conjugate_le_iff g P.toSubgroup Q).mp hg⟩

end LocalConjugacy
