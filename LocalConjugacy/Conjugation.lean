module

public import LocalConjugacy.Definitions

@[expose] public section

namespace LocalConjugacy

variable {G F : Type*} [Group G] [Group F]

theorem conjugate_comp (g h : G) (H : Subgroup G) :
    conjugate g (conjugate h H) = conjugate (g * h) H := by
  unfold conjugate
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

@[simp] theorem conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  unfold conjugate
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  change H.map (MulAut.conj (1 : G)).toMonoidHom = H
  rw [he, Subgroup.map_id]

@[simp] theorem conjugate_inv_cancel (g : G) (H : Subgroup G) :
    conjugate g⁻¹ (conjugate g H) = H := by
  rw [conjugate_comp, inv_mul_cancel, conjugate_one]

theorem conjugate_mono (g : G) {H K : Subgroup G} (h : H ≤ K) :
    conjugate g H ≤ conjugate g K := Subgroup.map_mono h

theorem conjugate_map (f : G →* F) (g : G) (H : Subgroup G) :
    (conjugate g H).map f = conjugate (f g) (H.map f) := by
  unfold conjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem conjugate_le_iff (g : G) (H K : Subgroup G) :
    conjugate g H ≤ K ↔ H ≤ conjugate g⁻¹ K := by
  constructor
  · intro h
    simpa using conjugate_mono g⁻¹ h
  · intro h
    simpa only [conjugate_comp, mul_inv_cancel, conjugate_one] using conjugate_mono g h

theorem sylow_smul_toSubgroup (p : ℕ) (g : G) (P : Sylow p G) :
    (g • P).toSubgroup = conjugate g P.toSubgroup := by
  simp only [Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.pointwise_smul_def, conjugate]
  congr 1

end LocalConjugacy
