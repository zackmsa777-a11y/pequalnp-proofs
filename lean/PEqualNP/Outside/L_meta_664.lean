import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_664

variable {F : Type} [Field F]

private def form (b : F) (z : F × F) : F := z.1 ^ 2 + b * z.1 * z.2 + z.2 ^ 2

private def cross (b : F) (p d : F × F) : F := b * (p.1 * d.2 + p.2 * d.1)

private def linearPart [CharP F 2] (a c : F) : F →+ F where
  toFun t := a * t ^ 2 + c * t
  map_zero' := by simp
  map_add' x y := by rw [CharTwo.add_sq]; ring

private theorem line_value [CharP F 2] (b : F) (p d : F × F) (t : F) :
    form b (p + t • d) = form b p + linearPart (form b d) (cross b p d) t := by
  change (p.1 + t * d.1) ^ 2 + b * (p.1 + t * d.1) * (p.2 + t * d.2) + (p.2 + t * d.2) ^ 2 = _
  rw [CharTwo.add_sq, CharTwo.add_sq]
  change _ = form b p + (form b d * t ^ 2 + cross b p d * t)
  unfold form cross
  ring

private theorem anisotropic (b : F) (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0)
    (z : F × F) (hz : form b z = 0) : z = 0 := by
  obtain ⟨x,y⟩ := z
  change x ^ 2 + b * x * y + y ^ 2 = 0 at hz
  by_cases hy : y = 0
  · subst y
    have hx : x = 0 := by simpa using hz
    simp [hx]
  · exfalso
    apply hb (x / y)
    field_simp [hy]
    linear_combination hz

-- The two roots of the additive part determine the index of its image.
private theorem kernel_index [Fintype F] [CharP F 2] (a c : F) (ha : a ≠ 0) (hc : c ≠ 0) :
    (linearPart a c).range.index = 2 := by
  let f := linearPart a c
  have mem (t : F) : t ∈ f.ker ↔ t = 0 ∨ t = c / a := by
    change a * t ^ 2 + c * t = 0 ↔ _
    rw [show a * t ^ 2 + c * t = t * (a * t + c) by ring, mul_eq_zero,
      CharTwo.add_eq_zero, eq_div_iff ha, mul_comm a t]
  change f.range.index = 2
  rw [AddSubgroup.index_range, Nat.card_eq_two_iff' (0 : f.ker)]
  let r : f.ker := ⟨c/a, (mem _).2 (Or.inr rfl)⟩
  refine ⟨r, ?_, ?_⟩
  · intro h
    exact div_ne_zero hc ha (congrArg Subtype.val h)
  · intro x hx
    apply Subtype.ext
    exact ((mem x.val).1 x.property).resolve_left (fun h => hx (Subtype.ext h))

-- A point in the subgroup supplies the missing coset whenever the image is proper.
private theorem spans [Fintype F] [CharP F 2] (b : F) (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0)
    (p d : F × F) (hd : d ≠ 0) (A : AddSubgroup F) (t₀ : F)
    (ht : form b (p + t₀ • d) ∈ A) :
    (linearPart (form b d) (cross b p d)).range ⊔ A = ⊤ := by
  let a := form b d
  let c := cross b p d
  let f := linearPart a c
  have ha : a ≠ 0 := fun h => hd (anisotropic b hb d h)
  change f.range ⊔ A = ⊤
  by_cases hc : c = 0
  · have hinj : Function.Injective f := by
      intro x y h
      change a * x ^ 2 + c * x = a * y ^ 2 + c * y at h
      simp only [hc, zero_mul, add_zero] at h
      exact CharTwo.sq_inj.mp (mul_left_cancel₀ ha h)
    rw [f.range_eq_top_of_surjective (Finite.surjective_of_injective hinj), top_sup_eq]
  · have hindex : f.range.index = 2 := kernel_index a c ha hc
    apply (f.range.isCoatom_of_index_prime (hindex ▸ Nat.prime_two)).lt_iff.mp
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hin : form b (p + t₀ • d) ∈ f.range := by
      rw [he]
      exact (show A ≤ f.range ⊔ A from le_sup_right) ht
    have hbase : form b p ∈ f.range := by
      rw [line_value] at hin
      exact (f.range.add_mem_cancel_right (show f t₀ ∈ f.range from ⟨t₀,rfl⟩)).mp hin
    obtain ⟨u,hu⟩ := hbase
    have hzero : form b (p + u • d) = 0 := by
      rw [line_value]
      change form b p + f u = 0
      rw [hu, CharTwo.add_self_eq_zero]
    have hv := anisotropic b hb _ hzero
    have hx : p.1 = u * d.1 := CharTwo.add_eq_zero.mp (congrArg Prod.fst hv)
    have hy : p.2 = u * d.2 := CharTwo.add_eq_zero.mp (congrArg Prod.snd hv)
    apply hc
    change b * (p.1 * d.2 + p.2 * d.1) = 0
    rw [hx, hy, show u * d.2 * d.1 = u * d.1 * d.2 by ring, CharTwo.add_self_eq_zero, mul_zero]

private theorem count_hit [Fintype F] [CharP F 2] (b : F) (hb : ∀ x : F, x ^ 2 + b * x + 1 ≠ 0)
    (p d : F × F) (hd : d ≠ 0) (A : AddSubgroup F) [DecidablePred (· ∈ A)]
    (t₀ : F) (ht : form b (p + t₀ • d) ∈ A) :
    (Finset.univ.filter (fun t : F => form b (p + t • d) ∈ A)).card = Nat.card A := by
  classical
  let f := linearPart (form b d) (cross b p d)
  have hspan : f.range ⊔ A = ⊤ := spans b hb p d hd A t₀ ht
  have hi : (A.comap f).index = A.index := by
    rw [AddSubgroup.index_comap, ← AddSubgroup.relIndex_sup_right f.range A, hspan,
      AddSubgroup.relIndex_top_right]
  have hcard : Nat.card (A.comap f) = Nat.card A := by
    apply Nat.eq_of_mul_eq_mul_right A.index_pos
    calc
      Nat.card (A.comap f) * A.index = Nat.card F := by rw [← hi, AddSubgroup.card_mul_index]
      _ = Nat.card A * A.index := A.card_mul_index.symm
  let hits := fun t : F => form b (p + t • d) ∈ A
  have shift (u : F) : u ∈ A.comap f ↔ hits (u + t₀) := by
    have ht' : form b p + f t₀ ∈ A := (line_value b p d t₀) ▸ ht
    change f u ∈ A ↔ form b (p + (u + t₀) • d) ∈ A
    rw [line_value]
    change f u ∈ A ↔ form b p + f (u + t₀) ∈ A
    rw [map_add, show form b p + (f u + f t₀) = f u + (form b p + f t₀) by abel]
    exact (A.add_mem_cancel_right ht').symm
  let e : (A.comap f) ≃ {t : F // hits t} := (Equiv.addRight t₀).subtypeEquiv shift
  calc
    _ = Nat.card {t : F // hits t} := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_of_subtype _ (fun t => by simp [hits])).symm
    _ = Nat.card (A.comap f) := (Nat.card_congr e).symm
    _ = Nat.card A := hcard

end PEqualNP.Outside.L_meta_664

theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  let N := (Finset.univ.filter (fun t : F => PEqualNP.Outside.L_meta_664.form b (p + t • d) ∈ A)).card
  change (N = 0 ∨ N = Nat.card A) ∧ (p = 0 → N = Nat.card A)
  have hit (t : F) (ht : PEqualNP.Outside.L_meta_664.form b (p + t • d) ∈ A) : N = Nat.card A :=
    PEqualNP.Outside.L_meta_664.count_hit b hb p d hd A t ht
  constructor
  · by_cases h : ∃ t : F, PEqualNP.Outside.L_meta_664.form b (p + t • d) ∈ A
    · obtain ⟨t,ht⟩ := h
      exact Or.inr (hit t ht)
    · left
      apply Finset.card_eq_zero.mpr
      exact Finset.filter_eq_empty_iff.mpr (fun t _ ht => h ⟨t,ht⟩)
  · intro hp
    apply hit 0
    simp [hp, PEqualNP.Outside.L_meta_664.form]
