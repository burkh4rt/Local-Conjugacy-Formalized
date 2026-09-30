module

public import LocalConjugacy.ProP
public import LocalConjugacy.FiniteQuotientConjugacy
public import LocalConjugacy.Conjugation

@[expose] public section

namespace LocalConjugacy

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [Profinite G]

theorem profinite_closed_subgroup (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    Profinite H := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  exact ⟨⟩

/-- Ambient open normal subgroups give a neighborhood basis in every subgroup. -/
theorem exists_openNormal_le_subgroup_open (H : Subgroup G) (V : OpenNormalSubgroup H) :
    ∃ U : OpenNormalSubgroup G, ∀ x : H, (x : G) ∈ U → x ∈ V := by
  obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.mp V.isOpen
  have h1 : (1 : G) ∈ O := by
    have h : (1 : H) ∈ Subtype.val ⁻¹' O := by rw [hpre]; exact V.one_mem
    exact h
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
  refine ⟨U, fun x hx => ?_⟩
  have h : x ∈ Subtype.val ⁻¹' O := hU hx
  rw [hpre] at h
  exact h

theorem isProP_of_quotient_images {p : ℕ} (H : Subgroup G)
    (h : ∀ U : OpenNormalSubgroup G,
      IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup))) : IsProP p H := by
  intro V z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup z
  obtain ⟨U, hU⟩ := exists_openNormal_le_subgroup_open H V
  let π := QuotientGroup.mk' U.toSubgroup
  obtain ⟨k, hk⟩ := h U ⟨π x, Subgroup.mem_map_of_mem π x.property⟩
  refine ⟨k, ?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff (N := V.toSubgroup) _).mpr
  apply hU
  apply (QuotientGroup.eq_one_iff (N := U.toSubgroup) _).mp
  have he := congrArg Subtype.val hk
  simpa [π] using he

theorem isPGroup_quotient_image {p : ℕ} (H : Subgroup G) (hH : IsProP p H)
    (U : OpenNormalSubgroup G) : IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup)) := by
  let π := QuotientGroup.mk' U.toSubgroup
  let f : H →* G ⧸ U.toSubgroup := π.comp H.subtype
  have hf : Continuous f := continuous_quotient_mk'.comp continuous_subtype_val
  intro x
  obtain ⟨y, hy, he⟩ := x.property
  obtain ⟨k, hk⟩ := image_pow hH f hf ⟨y, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  change x.val ^ p ^ k = 1
  change π y ^ p ^ k = 1 at hk
  rwa [show π y = x.val from he] at hk

theorem isProP_mono {p : ℕ} {P H : Subgroup G} (hPH : P ≤ H)
    (hH : IsProP p H) : IsProP p P := by
  apply isProP_of_quotient_images
  intro U
  exact (isPGroup_quotient_image H hH U).to_le (Subgroup.map_mono hPH)

namespace FiniteSylowSystem
open CategoryTheory

def transition {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (G ⧸ U.toSubgroup) →* (G ⧸ V.toSubgroup) :=
  QuotientGroup.map U.toSubgroup V.toSubgroup (MonoidHom.id G) h

@[simp] theorem transition_mk {U V : OpenNormalSubgroup G} (h : U ≤ V) (x : G) :
    transition h (QuotientGroup.mk' U.toSubgroup x) = QuotientGroup.mk' V.toSubgroup x := rfl

theorem transition_surjective {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    Function.Surjective (transition h) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup y
  exact ⟨QuotientGroup.mk' U.toSubgroup x, rfl⟩

@[simp] theorem transition_refl (U : OpenNormalSubgroup G) :
    transition (le_refl U) = MonoidHom.id _ := QuotientGroup.map_id _

@[simp] theorem transition_comp {U V W : OpenNormalSubgroup G} (h : U ≤ V) (k : V ≤ W) :
    (transition k).comp (transition h) = transition (h.trans k) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup x
  rfl

noncomputable def functor (p : ℕ) [Fact p.Prime] : OpenNormalSubgroup G ⥤ Type u where
  obj U := Sylow p (G ⧸ U.toSubgroup)
  map h := TypeCat.ofHom (fun P => Sylow.mapSurjective (transition_surjective (leOfHom h)) P)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro P
    apply Sylow.ext
    change (P : Subgroup _).map (transition (le_refl U)) = (P : Subgroup _)
    simp only [transition_refl, Subgroup.map_id]
  map_comp {U V W} h k := by
    apply ConcreteCategory.hom_ext
    intro P
    apply Sylow.ext
    change (P : Subgroup _).map (transition ((leOfHom h).trans (leOfHom k))) =
      ((P : Subgroup _).map (transition (leOfHom h))).map (transition (leOfHom k))
    rw [Subgroup.map_map, transition_comp]

theorem exists_compatible (p : ℕ) [Fact p.Prime] :
    ∃ P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup),
      ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
        (P U).mapSurjective (transition_surjective h) = P V := by
  let : ∀ U, Finite ((functor (G := G) p).obj U) := fun U =>
    inferInstanceAs (Finite (Sylow p (G ⧸ U.toSubgroup)))
  let : ∀ U, Nonempty ((functor (G := G) p).obj U) := fun U =>
    inferInstanceAs (Nonempty (Sylow p (G ⧸ U.toSubgroup)))
  obtain ⟨P, hP⟩ := nonempty_sections_of_finite_cofiltered_system (functor (G := G) p)
  exact ⟨P, fun U V h => hP (homOfLE h)⟩

variable {p : ℕ} [Fact p.Prime]
variable (P : (U : OpenNormalSubgroup G) → Sylow p (G ⧸ U.toSubgroup))
variable (hP : ∀ (U V : OpenNormalSubgroup G) (h : U ≤ V),
  (P U).mapSurjective (transition_surjective h) = P V)

def subgroup : Subgroup G :=
  ⨅ U : OpenNormalSubgroup G, (P U : Subgroup _).comap (QuotientGroup.mk' U.toSubgroup)

theorem mem_subgroup (x : G) :
    x ∈ subgroup P ↔ ∀ U, QuotientGroup.mk' U.toSubgroup x ∈ P U := by
  simp only [subgroup, Subgroup.mem_iInf, Subgroup.mem_comap]
  rfl

theorem subgroup_closed : IsClosed (subgroup P : Set G) := by
  rw [show (subgroup P : Set G) = ⋂ U : OpenNormalSubgroup G,
    (QuotientGroup.mk' U.toSubgroup) ⁻¹' (P U).toSubgroup.carrier by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage]
      exact mem_subgroup P x]
  apply isClosed_iInter
  intro U
  have hc : IsClosed (P U).toSubgroup.carrier := isClosed_discrete _
  exact hc.preimage (continuous_quotient_mk' : Continuous (QuotientGroup.mk' U.toSubgroup))

include hP

theorem map_transition (U V : OpenNormalSubgroup G) (h : U ≤ V) :
    (P U : Subgroup _).map (transition h) = (P V : Subgroup _) := by
  exact congrArg Sylow.toSubgroup (hP U V h)

theorem mem_of_le {U V : OpenNormalSubgroup G} (h : U ≤ V) (x : G)
    (hx : QuotientGroup.mk' U.toSubgroup x ∈ P U) :
    QuotientGroup.mk' V.toSubgroup x ∈ P V := by
  have hy := Subgroup.mem_map_of_mem (transition h) hx
  rw [map_transition P hP U V h] at hy
  exact hy

theorem map_subgroup (U : OpenNormalSubgroup G) :
    (subgroup P).map (QuotientGroup.mk' U.toSubgroup) = (P U : Subgroup _) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_subgroup P x).mp hx U
  · intro y hy
    let : Nonempty (OpenNormalSubgroup G) := ⟨U⟩
    let T : OpenNormalSubgroup G → Set G := fun V =>
      {x | QuotientGroup.mk' V.toSubgroup x ∈ P V ∧ QuotientGroup.mk' U.toSubgroup x = y}
    have hc : ∀ V, IsClosed (T V) := by
      intro V
      exact ((isClosed_discrete (P V).toSubgroup.carrier).preimage
        (continuous_quotient_mk' : Continuous (QuotientGroup.mk' V.toSubgroup))).inter
        (isClosed_eq (continuous_quotient_mk' : Continuous (QuotientGroup.mk' U.toSubgroup))
          continuous_const)
    have hn : ∀ V, (T V).Nonempty := by
      intro V
      have hymap : y ∈ (P (U ⊓ V)).toSubgroup.map
          (transition (show U ⊓ V ≤ U from inf_le_left)) := by
        rwa [map_transition P hP (U ⊓ V) U inf_le_left]
      obtain ⟨z, hz, hzy⟩ := hymap
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U ⊓ V).toSubgroup z
      exact ⟨x, mem_of_le P hP inf_le_right x hz, hzy⟩
    have hd : Directed (· ⊇ ·) T := by
      intro V W
      refine ⟨V ⊓ W, ?_, ?_⟩
      · intro x hx
        exact ⟨mem_of_le P hP inf_le_left x hx.1, hx.2⟩
      · intro x hx
        exact ⟨mem_of_le P hP inf_le_right x hx.1, hx.2⟩
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      T hd hn (fun V => (hc V).isCompact) hc
    have hx' : ∀ V, x ∈ T V := Set.mem_iInter.mp hx
    exact ⟨x, (mem_subgroup P x).mpr (fun V => (hx' V).1), (hx' U).2⟩

end FiniteSylowSystem

/-- A profinite group has a closed pro-`p` subgroup whose image in every
continuous finite quotient is a Sylow subgroup. -/
theorem exists_full_sylow (p : ℕ) [Fact p.Prime] :
    ∃ P : Subgroup G, IsClosed (P : Set G) ∧ IsProP p P ∧
      ∀ U : OpenNormalSubgroup G, ∃ S : Sylow p (G ⧸ U.toSubgroup),
        P.map (QuotientGroup.mk' U.toSubgroup) = (S : Subgroup _) := by
  obtain ⟨S, hS⟩ := FiniteSylowSystem.exists_compatible (G := G) p
  refine ⟨FiniteSylowSystem.subgroup S, FiniteSylowSystem.subgroup_closed S, ?_, ?_⟩
  · apply isProP_of_quotient_images
    intro U
    rw [FiniteSylowSystem.map_subgroup S hS U]
    exact (S U).isPGroup'
  · intro U
    exact ⟨S U, FiniteSylowSystem.map_subgroup S hS U⟩

/-- Every pro-`p` subgroup is conjugate into a subgroup having full Sylow
image in every finite quotient. -/
theorem conjugate_le_full_sylow {p : ℕ} [Fact p.Prime] (H P : Subgroup G)
    (hH : IsProP p H) (hP : IsClosed (P : Set G))
    (hfull : ∀ U : OpenNormalSubgroup G, ∃ S : Sylow p (G ⧸ U.toSubgroup),
      P.map (QuotientGroup.mk' U.toSubgroup) = (S : Subgroup _)) :
    ∃ g : G, conjugate g H ≤ P := by
  apply conjugate_le_of_finite_quotient_inclusions H P hP
  intro U
  obtain ⟨S, hS⟩ := hfull U
  obtain ⟨T, hT⟩ := (isPGroup_quotient_image H hH U).exists_le_sylow
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq (G ⧸ U.toSubgroup) T S
  refine ⟨q, ?_⟩
  rw [hS]
  have he : conjugate q (T : Subgroup _) = (S : Subgroup _) := by
    have he := congrArg Sylow.toSubgroup hq
    simpa only [sylow_smul_toSubgroup] using he
  exact (conjugate_mono q hT).trans he.le

theorem isSylowPro_of_full_images {p : ℕ} (P : Subgroup G)
    (hP : IsClosed (P : Set G))
    (hfull : ∀ U : OpenNormalSubgroup G, ∃ S : Sylow p (G ⧸ U.toSubgroup),
      P.map (QuotientGroup.mk' U.toSubgroup) = (S : Subgroup _)) :
    IsSylowPro p ⊤ P := by
  refine ⟨le_top, hP, isProP_of_quotient_images P ?_, ?_⟩
  · intro U
    obtain ⟨S, hS⟩ := hfull U
    rw [hS]
    exact S.isPGroup'
  · intro Q _ _ hQ hPQ
    apply le_antisymm _ hPQ
    intro x hx
    apply mem_of_mem_sup_openNormal P hP x
    intro U
    let π := QuotientGroup.mk' U.toSubgroup
    obtain ⟨S, hS⟩ := hfull U
    have he : Q.map π = (S : Subgroup _) := S.is_maximal'
      (isPGroup_quotient_image Q hQ U) (hS.symm.le.trans (Subgroup.map_mono hPQ))
    have hm : π x ∈ P.map π := by
      rw [hS, ← he]
      exact Subgroup.mem_map_of_mem π hx
    change x ∈ (P.map π).comap π at hm
    simpa only [Subgroup.comap_map_eq, π, QuotientGroup.ker_mk'] using hm

theorem exists_sylowPro (p : ℕ) [Fact p.Prime] :
    ∃ P : Subgroup G, IsSylowPro p ⊤ P := by
  obtain ⟨P, hc, _, hf⟩ := exists_full_sylow (G := G) p
  exact ⟨P, isSylowPro_of_full_images P hc hf⟩

theorem conjugate_closed (g : G) (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsClosed (conjugate g H : Set G) := by
  have hc : Continuous (fun x : G => g * x * g⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  exact (hH.isCompact.image hc).isClosed

theorem conjugate_isProP {p : ℕ} (g : G) (H : Subgroup G) (hH : IsProP p H) :
    IsProP p (conjugate g H) := by
  apply isProP_of_quotient_images
  intro U
  unfold conjugate
  rw [Subgroup.map_map]
  apply isPGroup_map_of_continuous H hH
  exact continuous_quotient_mk'.comp
    ((continuous_const.mul continuous_id).mul continuous_const)

theorem sylowPro_full_images {p : ℕ} [Fact p.Prime] (P : Subgroup G)
    (hP : IsSylowPro p ⊤ P) (U : OpenNormalSubgroup G) :
    ∃ S : Sylow p (G ⧸ U.toSubgroup),
      P.map (QuotientGroup.mk' U.toSubgroup) = (S : Subgroup _) := by
  obtain ⟨Q, hc, hp, hf⟩ := exists_full_sylow (G := G) p
  obtain ⟨g, hg⟩ := conjugate_le_full_sylow P Q hP.2.2.1 hc hf
  have he : conjugate g⁻¹ Q = P := hP.2.2.2 _ le_top
    (conjugate_closed g⁻¹ Q hc) (conjugate_isProP g⁻¹ Q hp)
    ((conjugate_le_iff g P Q).mp hg)
  obtain ⟨S, hS⟩ := hf U
  let π := QuotientGroup.mk' U.toSubgroup
  refine ⟨(π g⁻¹) • S, ?_⟩
  rw [← he, conjugate_map, hS]
  exact (sylow_smul_toSubgroup p (π g⁻¹) S).symm

theorem sylowPro_conjugate {p : ℕ} [Fact p.Prime] (P Q : Subgroup G)
    (hP : IsSylowPro p ⊤ P) (hQ : IsSylowPro p ⊤ Q) : Conjugate P Q := by
  obtain ⟨g, hg⟩ := conjugate_le_full_sylow P Q hP.2.2.1 hQ.2.1
    (sylowPro_full_images Q hQ)
  have he : conjugate g⁻¹ Q = P := hP.2.2.2 _ le_top
    (conjugate_closed g⁻¹ Q hQ.2.1) (conjugate_isProP g⁻¹ Q hQ.2.2.1)
    ((conjugate_le_iff g P Q).mp hg)
  refine ⟨g, ?_⟩
  rw [← he, conjugate_comp, mul_inv_cancel, conjugate_one]

theorem isProP_map {F : Type*} [Group F] [TopologicalSpace F]
    {p : ℕ} (H : Subgroup F) (hH : IsProP p H) (f : F →* G) (hf : Continuous f) :
    IsProP p (H.map f) := by
  apply isProP_of_quotient_images
  intro U
  rw [Subgroup.map_map]
  exact isPGroup_map_of_continuous H hH _ (continuous_quotient_mk'.comp hf)

theorem isSylowPro_map_subtype {p : ℕ} (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (P : Subgroup H) (hP : IsSylowPro p ⊤ P) :
    IsSylowPro p H (P.map H.subtype) := by
  letI := profinite_closed_subgroup H hH
  refine ⟨?_, ?_, isProP_map P hP.2.2.1 H.subtype continuous_subtype_val, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.property
  · exact (hP.2.1.isCompact.image continuous_subtype_val).isClosed
  · intro Q hQH hQc hQp hPQ
    have he : Q.subgroupOf H = P := hP.2.2.2 _ le_top
      (hQc.preimage continuous_subtype_val) (isProP_subgroupOf hQp hQH)
      (Subgroup.map_le_iff_le_comap.mp hPQ)
    rw [← he, Subgroup.map_subgroupOf_eq_of_le hQH]

theorem isSylowPro_subgroupOf {p : ℕ} (H P : Subgroup G)
    (hH : IsClosed (H : Set G)) (hP : IsSylowPro p H P) :
    IsSylowPro p ⊤ (P.subgroupOf H) := by
  letI := profinite_closed_subgroup H hH
  refine ⟨le_top, hP.2.1.preimage continuous_subtype_val,
    isProP_subgroupOf hP.2.2.1 hP.1, ?_⟩
  intro Q _ hQc hQp hPQ
  have he : Q.map H.subtype = P := hP.2.2.2 _
    (by rintro _ ⟨x, _, rfl⟩; exact x.property)
    (hQc.isCompact.image continuous_subtype_val).isClosed
    (isProP_map Q hQp H.subtype continuous_subtype_val)
    (by simpa only [Subgroup.map_subgroupOf_eq_of_le hP.1] using
      (Subgroup.map_mono hPQ : (P.subgroupOf H).map H.subtype ≤ Q.map H.subtype))
  apply le_antisymm _ hPQ
  intro x hx
  show (x : G) ∈ P
  rw [← he]
  exact Subgroup.mem_map_of_mem H.subtype hx

theorem exists_sylowPro_subgroup (p : ℕ) [Fact p.Prime] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) : ∃ P : Subgroup G, IsSylowPro p H P := by
  letI := profinite_closed_subgroup H hH
  obtain ⟨P, hP⟩ := exists_sylowPro (G := H) p
  exact ⟨P.map H.subtype, isSylowPro_map_subtype H hH P hP⟩

theorem isSylowPro_conjugate {p : ℕ} (g : G) (H P : Subgroup G)
    (hP : IsSylowPro p H P) : IsSylowPro p (conjugate g H) (conjugate g P) := by
  refine ⟨conjugate_mono g hP.1, conjugate_closed g P hP.2.1,
    conjugate_isProP g P hP.2.2.1, ?_⟩
  intro Q hQH hQc hQp hPQ
  have he : conjugate g⁻¹ Q = P := hP.2.2.2 _
    (by simpa only [conjugate_inv_cancel] using conjugate_mono g⁻¹ hQH)
    (conjugate_closed g⁻¹ Q hQc) (conjugate_isProP g⁻¹ Q hQp)
    ((conjugate_le_iff g P Q).mp hPQ)
  rw [← he, conjugate_comp, mul_inv_cancel, conjugate_one]

theorem locallyConjugate_of_conjugate (H K : Subgroup G)
    (hH : IsClosed (H : Set G)) (hconj : Conjugate H K) : LocallyConjugate H K := by
  obtain ⟨g, rfl⟩ := hconj
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := exists_sylowPro_subgroup p H hH
  exact ⟨P, conjugate g P, hP, isSylowPro_conjugate g H P hP, g, rfl⟩

end LocalConjugacy
