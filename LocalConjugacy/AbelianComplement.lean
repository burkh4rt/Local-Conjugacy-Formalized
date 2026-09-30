module

public import LocalConjugacy.FiniteAbelianCohomology
public import LocalConjugacy.SylowFiniteImages

@[expose] public section

namespace LocalConjugacy
namespace AbelianComplement

variable {G : Type*} [Group G] (N H : Subgroup G) [N.Normal]
  (hc : Subgroup.IsComplement' N H)

noncomputable def projection (x : G) : N := (hc.equiv x).1

theorem projection_mul_right (x : G) {h : G} (hh : h ∈ H) :
    projection N H hc (x * h) = projection N H hc x := by
  have he := congrArg Prod.fst (hc.equiv_mul_right_of_mem (g := x) hh)
  exact he

theorem projection_of_mem (n : N) : projection N H hc n = n :=
  hc.equiv_fst_eq_self_of_mem_of_one_mem H.one_mem n.property

theorem projection_eq_one_iff (x : G) : projection N H hc x = 1 ↔ x ∈ H := by
  rw [← Subtype.coe_inj]
  exact hc.coe_equiv_fst_eq_one_iff_mem N.one_mem

theorem projection_mul (hcomm : ∀ n m : N, n * m = m * n) (x y : G) :
    projection N H hc (x * y) = projection N H hc x *
      MulAut.conjNormal x (projection N H hc y) := by
  let nx := projection N H hc x
  let ny := projection N H hc y
  let hx : H := (hc.equiv x).2
  let hy : H := (hc.equiv y).2
  have hxe : (nx : G) * hx = x := hc.equiv_fst_mul_equiv_snd x
  have hye : (ny : G) * hy = y := hc.equiv_fst_mul_equiv_snd y
  have he : ((MulAut.conjNormal x ny * nx : N) : G) * (hx * hy : H) = x * y := by
    change (x * ny * x⁻¹ * nx) * (hx * hy) = x * y
    calc
      (x * ny * x⁻¹ * nx) * (hx * hy) = x * ny * x⁻¹ * ((nx : G) * hx) * hy := by group
      _ = x * y := by rw [hxe, ← hye]; group
  have hf := congrArg (fun z => (hc.equiv z).1) he
  rw [show ((MulAut.conjNormal x ny * nx : N) : G) * (hx * hy : H) =
      hc.equiv.symm (MulAut.conjNormal x ny * nx, hx * hy) from rfl,
    hc.equiv.apply_symm_apply] at hf
  exact hf.symm.trans (hcomm _ _)

theorem local_fixed_cocycle (hcomm : ∀ n m : N, n * m = m * n)
    (P : Subgroup G) (g : G) (hg : conjugate g P ≤ H) :
    ∃ n : N, ∀ x : P, projection N H hc x * MulAut.conjNormal (x : G) n = n := by
  refine ⟨projection N H hc g⁻¹, fun x => ?_⟩
  rw [← projection_mul N H hc hcomm]
  have hm : g * x * g⁻¹ ∈ H := hg (Subgroup.mem_map_of_mem _ x.property)
  have he : (x : G) * g⁻¹ = g⁻¹ * (g * x * g⁻¹) := by group
  rw [he]
  exact projection_mul_right N H hc g⁻¹ hm

theorem conjugate_le_of_coboundary (hcomm : ∀ n m : N, n * m = m * n)
    (K : Subgroup G) (b : N)
    (hb : ∀ x : K, projection N H hc x = b⁻¹ * MulAut.conjNormal (x : G) b) :
    conjugate (b : G) K ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  apply (projection_eq_one_iff N H hc _).mp
  change projection N H hc ((b : G) * x * (b : G)⁻¹) = 1
  rw [projection_mul N H hc hcomm, projection_mul N H hc hcomm,
    projection_of_mem N H hc b, hb ⟨x, hx⟩]
  have ht (n : N) : MulAut.conjNormal (b : G) n = n := by
    apply Subtype.ext
    change (b : G) * n * (b : G)⁻¹ = n
    have he := congrArg Subtype.val (hcomm b n)
    change (b : G) * n = (n : G) * b at he
    rw [he]
    group
  rw [ht]
  have hi : projection N H hc (b : G)⁻¹ = b⁻¹ := projection_of_mem N H hc b⁻¹
  rw [hi, map_mul, MulAut.mul_apply, ht, map_inv]
  group

include hc in
theorem finite_local_inclusion [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (hcomm : ∀ n m : N, n * m = m * n) (K : Subgroup G)
    (hloc : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H := by
  classical
  letI : Profinite G := ⟨⟩
  letI : CommGroup N := { (inferInstance : Group N) with mul_comm := hcomm }
  letI : Fintype K := Fintype.ofFinite K
  let a : K →* MulAut N := MulAut.conjNormal.comp K.subtype
  let f : K → N := fun x => projection N H hc x
  have hf : CocycleFn a f := fun x y => projection_mul N H hc hcomm x y
  have hl : ∀ p : ℕ, p.Prime → ∃ P : Sylow p K, ∃ n : N,
      ∀ x : P, f x * a x n = n := by
    intro p hp
    obtain ⟨P, hP, g, hg⟩ := hloc p hp
    obtain ⟨S, hS⟩ := sylow_of_isSylowPro (P.subgroupOf K)
      (isSylowPro_subgroupOf K P (isClosed_discrete _) hP)
    obtain ⟨n, hn⟩ := local_fixed_cocycle N H hc hcomm P g hg
    refine ⟨S, n, fun x => ?_⟩
    have hx : ((x : K) : G) ∈ P := by
      have hx := x.property
      change (x : K) ∈ S.toSubgroup at hx
      rw [hS] at hx
      exact hx
    exact hn ⟨x, hx⟩
  obtain ⟨b, hb⟩ := FiniteAbelianCohomology.local_coboundary a f hf hl
  exact ⟨b, conjugate_le_of_coboundary N H hc hcomm K b hb⟩

end AbelianComplement
end LocalConjugacy
