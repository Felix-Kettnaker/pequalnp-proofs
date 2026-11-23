import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1462 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (X B : Finset (Fin n))
    (r : Fin n → Fin n → Prop) (f : Fin m → Fin n),
    (∀ a b : Fin n, r a b → ¬ r b a) →
    (∀ i : Fin m, ¬ S i ⊆ X → f i ∈ B ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ B, r (f i) y) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i →
      (if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S i = {p}) ∧
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j,
        ((if p ∈ X then ({p} : Finset (Fin n)) else {p, f i}) ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, ((if s ∈ X then ({s} : Finset (Fin n)) else {s, f j}) ∩ S i).Nonempty))) := by
  intro n m S X B r f hr hf
  refine ⟨?_, ?_⟩
  · intro i p hp
    by_cases hX : p ∈ X
    · rw [if_pos hX]
      ext q
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨h, -⟩
        exact h
      · rintro rfl
        exact ⟨rfl, hp⟩
    · rw [if_neg hX]
      have hnot : ¬ S i ⊆ X := fun h => hX (h hp)
      have hfi := (hf i hnot).2.1
      ext q
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h | h, hq⟩
        · exact h
        · exact absurd (h ▸ hq) hfi
      · rintro rfl
        exact ⟨Or.inl rfl, hp⟩
  · rintro i j - ⟨⟨p, hp, hpne⟩, ⟨s, hs, hsne⟩⟩
    have key : ∀ (a b : Fin m) (t : Fin n), t ∈ S a \ S b →
        ((if t ∈ X then ({t} : Finset (Fin n)) else {t, f a}) ∩ S b).Nonempty →
        ¬ S a ⊆ X ∧ f a ∈ S b := by
      intro a b t ht hne
      rw [Finset.mem_sdiff] at ht
      obtain ⟨q, hq⟩ := hne
      by_cases hX : t ∈ X
      · rw [if_pos hX] at hq
        simp only [Finset.mem_inter, Finset.mem_singleton] at hq
        exact absurd (hq.1 ▸ hq.2) ht.2
      · rw [if_neg hX] at hq
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq
        refine ⟨fun h => hX (h ht.1), ?_⟩
        rcases hq.1 with h | h
        · exact absurd (h ▸ hq.2) ht.2
        · exact h ▸ hq.2
    obtain ⟨hi, hfi⟩ := key i j p hp hpne
    obtain ⟨hj, hfj⟩ := key j i s hs hsne
    have h1 := (hf i hi).2.2 (f j) (Finset.mem_inter.mpr ⟨hfj, (hf j hj).1⟩)
    have h2 := (hf j hj).2.2 (f i) (Finset.mem_inter.mpr ⟨hfi, (hf i hi).1⟩)
    exact hr _ _ h1 h2
