module

public import LocalConjugacy.SupersolvableReductions
public import LocalConjugacy.CocycleZorn

@[expose] public section

namespace LocalConjugacy

/-- Every finite continuous quotient has all its prime divisors in `π`. -/
def HasProPrimes (π : Set ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, HasPrimes π (G ⧸ U.toSubgroup)

theorem HasPrimes.of_surjective {G F : Type*} [Group G] [Group F] {π : Set ℕ}
    (hG : HasPrimes π G) (f : G →* F) (hf : Function.Surjective f) : HasPrimes π F :=
  fun p hp hd => hG p hp (hd.trans (Subgroup.card_dvd_of_surjective f hf))

theorem HasProPrimes.of_ambient_images {G : Type*} [Group G] [TopologicalSpace G]
    [Profinite G] {π : Set ℕ} (H : Subgroup G)
    (hH : ∀ U : OpenNormalSubgroup G, HasPrimes π (H.map (QuotientGroup.mk' U.toSubgroup))) :
    HasProPrimes π H := by
  intro V
  obtain ⟨U, f, hf⟩ := subgroup_quotient_factors H V
  exact (hH U).of_surjective f hf

theorem IsHallPro.hasProPrimes {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    {π : Set ℕ} {H : Subgroup G} (hH : IsHallPro π H) : HasProPrimes π H :=
  HasProPrimes.of_ambient_images H (fun U => (hH.2 U).1)

theorem HasProPrimes.of_continuous_surjective {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F] {π : Set ℕ}
    (hG : HasProPrimes π G) (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) :
    HasPrimes π F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  exact (hG U).of_surjective (QuotientGroup.kerLift f)
    (QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl)

theorem HasProPrimes.ambient_image {G F : Type*} [Group G] [Group F]
    [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F] {π : Set ℕ}
    (H : Subgroup G) (hH : HasProPrimes π H) (f : G →* F) (hf : Continuous f) :
    HasPrimes π (H.map f) :=
  hH.of_continuous_surjective (subgroupImageHom H f)
    ((hf.comp continuous_subtype_val).subtype_mk _) (subgroupImageHom_surjective H f)

/-- The high-prime Hall factor centralizes every normal pro-p subgroup.
Both normality assertions are justified in each finite supersolvable quotient. -/
theorem prosupersolvable_commute_normal_proP {G : Type*} [Group G]
    [TopologicalSpace G] [Profinite G] (hG : Prosupersolvable G)
    {p : ℕ} [Fact p.Prime] (N M : Subgroup G) [N.Normal]
    (hN : IsProP p N) (hM : HasProPrimes {r | p < r} M) :
    ∀ (n : N) (m : M), Commute (n : G) (m : G) := by
  intro n m
  have hcomm : (n : G) * m * (n : G)⁻¹ * (m : G)⁻¹ = 1 := by
    apply mem_of_mem_sup_openNormal (⊥ : Subgroup G)
      (isClosed_singleton : IsClosed ({1} : Set G))
    intro U
    let π := QuotientGroup.mk' U.toSubgroup
    let A := N.map π
    let B := finiteUpperHall hG p U
    letI : A.Normal := (inferInstance : N.Normal).map π (QuotientGroup.mk'_surjective U.toSubgroup)
    have hA : HasPrimes {r | r ≤ p} A := by
      intro r hr hd
      have he : r = p := hasPrimes_singleton_iff_isPGroup.mpr
        (isPGroup_quotient_image N hN U) r hr hd
      exact he.le
    have hMB : M.map π ≤ B :=
      (hM.ambient_image M π continuous_quotient_mk').le_normalHall (finiteUpperHall_hall hG p U)
    have hd : Disjoint A B := (disjoint_of_cutoff_primes (finiteUpperHall_hall hG p U).1 hA).symm
    have hc := Subgroup.commute_of_normal_of_disjoint A B inferInstance inferInstance hd
      (π n) (π m) (Subgroup.mem_map_of_mem π n.property)
      (hMB (Subgroup.mem_map_of_mem π m.property))
    have he : π ((n : G) * m * (n : G)⁻¹ * (m : G)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc.eq]
      group
    have hu := (QuotientGroup.eq_one_iff (N := U.toSubgroup) _).mp he
    exact (show U.toSubgroup ≤ ⊥ ⊔ U.toSubgroup from le_sup_right) hu
  change (n : G) * m = (m : G) * n
  calc
    (n : G) * m = ((n : G) * m * (n : G)⁻¹ * (m : G)⁻¹) * ((m : G) * n) := by group
    _ = (m : G) * n := by rw [hcomm, one_mul]

/-- The coprime homomorphism argument for a whole set of primes, with
possibly infinite discrete p-group coefficients. -/
theorem continuous_hom_eq_one_of_proPrimes {G N : Type*} [Group G] [Group N]
    [TopologicalSpace G] [TopologicalSpace N] [DiscreteTopology N]
    {π : Set ℕ} {p : ℕ} [hp : Fact p.Prime] (hG : HasProPrimes π G)
    (hpπ : p ∉ π) (hN : IsPGroup p N) (f : G →* N) (hf : Continuous f) (x : G) :
    f x = 1 := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  let φ := QuotientGroup.lift U.toSubgroup f (show U.toSubgroup ≤ f.ker from le_rfl)
  have hcop : p.Coprime (Nat.card (G ⧸ U.toSubgroup)) :=
    hp.out.coprime_iff_not_dvd.mpr (fun hd => hpπ (hG U p hp.out hd))
  obtain ⟨k, hk⟩ := hN (f x)
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) (orderOf_dvd_of_pow_eq_one hk)
  exact (orderOf_map_dvd φ (QuotientGroup.mk' U.toSubgroup x)).trans
    (orderOf_dvd_natCard (QuotientGroup.mk' U.toSubgroup x))

theorem hall_complement_proper {G : Type*} [Group G] [TopologicalSpace G] [Profinite G]
    {p : ℕ} {Q : Subgroup G} (hQ : IsHallPro {r | r ≤ p} Q)
    (hlarge : ∃ (U : OpenNormalSubgroup G) (q : ℕ), q.Prime ∧
      q ∣ Nat.card (G ⧸ U.toSubgroup) ∧ p < q) : Q ≠ ⊤ := by
  intro he
  obtain ⟨U, q, hq, hd, hpq⟩ := hlarge
  have hh := (hQ.2 U).1
  rw [he, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective U.toSubgroup)] at hh
  have hle := hh q hq (by simpa only [Subgroup.card_top] using hd)
  exact Nat.not_lt_of_ge hle hpq

section Cocycles
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- The explicit inflation `F(mq) = f(q)` used in the Hall branch. -/
theorem extend_cocycle_across_trivial_factor (M Q : Subgroup J) [M.Normal]
    (hM : IsClosed (M : Set J)) (hQ : IsClosed (Q : Set J)) (hs : M.IsComplement' Q)
    (hact : ∀ (m : M) (n : N), (m : J) • n = n) (f : Cocycle (N := N) Q) :
    ∃ F : Cocycle (N := N) (⊤ : Subgroup J), restrictCocycle le_top F = f := by
  letI := profinite_closed_subgroup M hM
  letI := profinite_closed_subgroup Q hQ
  let e : J ⧸ M ≃* Q := hs.symm.QuotientMulEquiv
  let r : J →* Q := e.toMonoidHom.comp (QuotientGroup.mk' M)
  have hr (m : M) (q : Q) : r ((m : J) * q) = q := by
    have hm1 : QuotientGroup.mk' M (m : J) = 1 :=
      (QuotientGroup.eq_one_iff (N := M) (m : J)).mpr m.property
    change e (QuotientGroup.mk' M ((m : J) * q)) = q
    rw [map_mul, hm1, one_mul]
    exact e.apply_symm_apply q
  have hm : Continuous hs.equiv.symm :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have he : Continuous hs.equiv := hm.continuous_symm_of_equiv_compact_to_t2
  have hre (x : J) : r x = (hs.equiv x).2 := by
    conv_lhs => rw [← hs.equiv_fst_mul_equiv_snd x]
    exact hr _ _
  have hc : Continuous r := (continuous_snd.comp he).congr (fun x => (hre x).symm)
  have haction (x : J) (n : N) : x • n = (r x : J) • n := by
    rw [hre]
    conv_lhs => rw [← hs.equiv_fst_mul_equiv_snd x]
    rw [mul_smul, hact]
  let F : Cocycle (N := N) (⊤ : Subgroup J) :=
    { toFun := fun x => f.toFun (r x)
      continuous_toFun := f.continuous_toFun.comp (hc.comp continuous_subtype_val)
      map_mul := fun x y => by
        change f.toFun (r ((x : J) * y)) = _
        rw [r.map_mul, f.map_mul, haction (x : J)] }
  refine ⟨F, Cocycle.ext (fun q => ?_)⟩
  change f.toFun (r q) = f.toFun q
  have hq := hr 1 q
  simpa only [Subgroup.coe_one, one_mul] using congrArg f.toFun hq

/-- Restriction to the Hall complement is injective and every cocycle on
the complement extends. The normal factor acts trivially and has no p-primes. -/
theorem hall_complement_restriction [DiscreteTopology N]
    {p : ℕ} [Fact p.Prime] (hN : IsPGroup p N)
    (M Q : Subgroup J) [M.Normal]
    (hM : IsClosed (M : Set J)) (hQ : IsClosed (Q : Set J)) (hs : M.IsComplement' Q)
    (hprimes : HasProPrimes {r | p < r} M)
    (hact : ∀ (m : M) (n : N), (m : J) • n = n) :
    RestrictionIsomorphism (N := N) ⊤ Q le_top := by
  have hzero (f : Cocycle (N := N) (⊤ : Subgroup J)) (m : M) :
      f.toFun ⟨m, trivial⟩ = 1 := by
    let φ : M →* N :=
      { toFun := fun x => f.toFun ⟨x, trivial⟩
        map_one' := cocycle_one f
        map_mul' := fun x y => by
          change f.toFun ((⟨x, trivial⟩ : (⊤ : Subgroup J)) * ⟨y, trivial⟩) = _
          rw [f.map_mul, hact] }
    exact continuous_hom_eq_one_of_proPrimes hprimes (Nat.lt_irrefl p) hN φ
      (f.continuous_toFun.comp (continuous_subtype_val.subtype_mk _)) m
  have hval (f : Cocycle (N := N) (⊤ : Subgroup J)) (m : M) (q : Q) :
      f.toFun ⟨(m : J) * q, trivial⟩ = f.toFun ⟨q, trivial⟩ := by
    change f.toFun ((⟨m, trivial⟩ : (⊤ : Subgroup J)) * ⟨q, trivial⟩) = _
    rw [f.map_mul, hzero, hact, one_mul]
  constructor
  · intro f g hfg
    obtain ⟨n, hn⟩ := hfg
    refine ⟨n, fun x => ?_⟩
    obtain ⟨⟨m, q⟩, hx⟩ := hs.2 (x : J)
    have hx' : x = (⟨(m : J) * q, trivial⟩ : (⊤ : Subgroup J)) := Subtype.ext hx.symm
    rw [hx', hval, hval]
    change g.toFun ⟨q, trivial⟩ = n⁻¹ * f.toFun ⟨q, trivial⟩ * (((m : J) * q) • n)
    rw [mul_smul, hact]
    exact hn q
  · intro f _
    obtain ⟨F, hF⟩ := extend_cocycle_across_trivial_factor M Q hM hQ hs hact f
    refine ⟨F, ?_⟩
    change Cohomologous (restrictCocycle le_top F) f
    rw [hF]
    exact cohomologous_refl f

end Cocycles
end LocalConjugacy
