module

public import LocalConjugacy.SupersolvableRestriction
public import LocalConjugacy.NilpotentRestriction
public import LocalConjugacy.PronilpotentSylow

@[expose] public section

/-! The pronilpotent branch of Lemma 1.2, using the manuscript's two Zorn
arguments: first a fixed pair of cocycles, then one stable class. -/

namespace LocalConjugacy

theorem pronilpotent_subgroup {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]
    (hJ : Pronilpotent J) (L : Subgroup J) : Pronilpotent L := by
  intro V
  obtain ⟨U, f, hf⟩ := subgroup_quotient_factors L V
  letI := hJ U
  exact Group.nilpotent_of_surjective f hf

/-- The proper Sylow lies in an open normal subgroup of prime index other
than `p`. No claim that this prime is the smallest prime is needed. -/
theorem pronilpotent_prime_index_above_sylow
    {J : Type*} [Group J] [TopologicalSpace J] [Profinite J]
    (hJ : Pronilpotent J) {p : ℕ} [Fact p.Prime]
    (P : Subgroup J) (hP : IsSylowPro p ⊤ P) (hproper : P ≠ ⊤) :
    ∃ K : OpenNormalSubgroup J, P ≤ K.toSubgroup ∧
      K.toSubgroup.index.Prime ∧ K.toSubgroup.index ≠ p := by
  classical
  have hex : ∃ U : OpenNormalSubgroup J,
      P.map (QuotientGroup.mk' U.toSubgroup) ≠ ⊤ := by
    by_contra! h
    apply hproper
    apply top_unique
    exact subgroup_le_of_finite_images ⊤ P hP.2.1 (fun U => by rw [h U]; exact le_top)
  obtain ⟨U, hU⟩ := hex
  let π := QuotientGroup.mk' U.toSubgroup
  letI := hJ U
  obtain ⟨S, hS⟩ := sylowPro_full_images P hP U
  obtain ⟨D, hD, hSD⟩ := (eq_top_or_exists_le_coatom S.toSubgroup).resolve_left (hS ▸ hU)
  obtain ⟨hDn, hprime⟩ := nilpotent_coatom_prime_index D hD
  letI := hDn
  have hne : D.index ≠ p := by
    intro he
    have hd := Subgroup.index_dvd_of_le hSD
    rw [he] at hd
    exact S.not_dvd_index hd
  let K : OpenNormalSubgroup J :=
    { toSubgroup := D.comap π
      isOpen' := (isOpen_discrete (D : Set (J ⧸ U.toSubgroup))).preimage continuous_quotient_mk' }
  have hPK : P ≤ K.toSubgroup := fun x hx => hSD (hS ▸ Subgroup.mem_map_of_mem π hx)
  have hi : K.toSubgroup.index = D.index := D.index_comap_of_surjective
    (QuotientGroup.mk'_surjective U.toSubgroup)
  exact ⟨K, hPK, hi ▸ hprime, hi ▸ hne⟩

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N] [Finite N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- Injectivity, by minimality for one inequivalent pair of cocycles. -/
theorem pronilpotent_sylow_restriction_injective_zorn
    (hJ : Pronilpotent J) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (P : Subgroup J) (hP : IsSylowPro p ⊤ P)
    (φ ψ : Cocycle (N := N) (⊤ : Subgroup J))
    (hφψ : Cohomologous (restrictCocycle (show P ≤ ⊤ from le_top) φ)
      (restrictCocycle le_top ψ)) : Cohomologous φ ψ := by
  apply cohomologous_of_zorn_step P φ ψ hφψ
  intro L hL hPL hmin
  letI := profinite_closed_subgroup L hL
  have hJL := pronilpotent_subgroup hJ L
  have hPLs := isSylowPro_subgroupOf L P hL (isSylowPro_of_intermediate hP hPL.le le_top)
  have hproper : P.subgroupOf L ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map L.subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le hPL.le, ← MonoidHom.range_eq_map, L.range_subtype] at hh
    exact hPL.ne hh
  obtain ⟨J₀, hPJ₀, hprime, hne⟩ :=
    pronilpotent_prime_index_above_sylow hJL (P.subgroupOf L) hPLs hproper
  letI : Fact J₀.toSubgroup.index.Prime := ⟨hprime⟩
  obtain ⟨hclosed, hle, hlt⟩ := closed_intermediate_image P L hL hPL.le
    J₀.toSubgroup J₀.isClosed hPJ₀ (openNormal_lt_top_of_prime_index J₀ hprime)
  obtain ⟨n, hn⟩ := hmin _ hclosed hle hlt
  have hsmall : Cohomologous
      (restrictCocycle (show J₀.toSubgroup ≤ ⊤ from le_top)
        (restrictCocycle (show L ≤ ⊤ from le_top) φ).subgroupTop)
      (restrictCocycle le_top (restrictCocycle le_top ψ).subgroupTop) :=
    ⟨n, fun x => hn ⟨x, Subgroup.mem_map_of_mem L.subtype x.property⟩⟩
  obtain ⟨m, hm⟩ := (coprime_prime_index_restriction hne hN J₀.toSubgroup
    J₀.isClosed rfl).1 (restrictCocycle (show L ≤ ⊤ from le_top) φ).subgroupTop
      (restrictCocycle (show L ≤ ⊤ from le_top) ψ).subgroupTop hsmall
  exact ⟨m, fun x => hm ⟨x, trivial⟩⟩

/-- Surjectivity, by minimality for the single prescribed stable class.
Injectivity makes its lift invariant before Proposition 2.2 is applied. -/
theorem pronilpotent_sylow_extension_zorn
    (hJ : Pronilpotent J) {p : ℕ} [Fact p.Prime]
    (hN : IsPGroup p N) (P : Subgroup J) (hP : IsSylowPro p ⊤ P)
    (τ : Cocycle (N := N) P) (hτ : InvariantUnder ⊤ P τ) : τ.ExtendsTo ⊤ := by
  apply extendsTo_of_zorn_step P τ
  intro L hL hPL hmin
  letI := profinite_closed_subgroup L hL
  have hJL := pronilpotent_subgroup hJ L
  have hPLs := isSylowPro_subgroupOf L P hL (isSylowPro_of_intermediate hP hPL.le le_top)
  have hproper : P.subgroupOf L ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map L.subtype) he
    rw [Subgroup.map_subgroupOf_eq_of_le hPL.le, ← MonoidHom.range_eq_map, L.range_subtype] at hh
    exact hPL.ne hh
  letI := sylowPro_normal_of_pronilpotent hJL (P.subgroupOf L) hPLs
  obtain ⟨J₀, hPJ₀, hprime, hne⟩ :=
    pronilpotent_prime_index_above_sylow hJL (P.subgroupOf L) hPLs hproper
  letI : Fact J₀.toSubgroup.index.Prime := ⟨hprime⟩
  have hτL : InvariantUnder ⊤ (P.subgroupOf L) (τ.onSubgroup (L := L)) := by
    intro j _
    obtain ⟨n, hn⟩ := hτ j trivial
    exact ⟨n, fun x hx hjx => hn x hx hjx⟩
  have hinj : ∀ φ ψ : Cocycle (J := L) (N := N) J₀.toSubgroup,
      Cohomologous (restrictCocycle hPJ₀ φ) (restrictCocycle hPJ₀ ψ) → Cohomologous φ ψ := by
    intro φ ψ hφψ
    letI := profinite_closed_subgroup J₀.toSubgroup J₀.isClosed
    have hJ₀ := pronilpotent_subgroup hJL J₀.toSubgroup
    have hPs := isSylowPro_subgroupOf J₀.toSubgroup (P.subgroupOf L) J₀.isClosed
      (isSylowPro_of_intermediate hPLs hPJ₀ le_top)
    have hh : Cohomologous φ.subgroupTop ψ.subgroupTop := by
      apply pronilpotent_sylow_restriction_injective_zorn hJ₀ hN _ hPs
      obtain ⟨n, hn⟩ := hφψ
      exact ⟨n, fun x => hn ⟨x, x.property⟩⟩
    obtain ⟨n, hn⟩ := hh
    exact ⟨n, fun x => hn ⟨x, trivial⟩⟩
  obtain ⟨hclosed, hle, hlt⟩ := closed_intermediate_image P L hL hPL.le
    J₀.toSubgroup J₀.isClosed hPJ₀ (openNormal_lt_top_of_prime_index J₀ hprime)
  have hext := (hmin _ hclosed hle hlt).on_mapped_subgroup J₀.toSubgroup hPJ₀
  exact Cocycle.ExtendsTo.of_subgroup_top hPL.le
    (extend_stable_class_across_prime_index (locallyFiniteGroup_of_finite N)
      hne hN J₀.toSubgroup (P.subgroupOf L) hPJ₀ J₀.isClosed rfl hinj
      (τ.onSubgroup (L := L)) hτL hext)

end LocalConjugacy
