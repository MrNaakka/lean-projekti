import Mathlib.Data.Set.Countable


-- Auxiliary set-theoretic results

variable {α β : Type*}

namespace Set

theorem sInter_countable {s : Set (Set α)} {t : Set α} (ht : t ∈ s) (hf : t.Countable) :
    (⋂₀ s).Countable := Countable.mono (fun ⦃_⦄ a_1 ↦ a_1 t ht) hf

theorem countable_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) :
    (f '' s).Countable ↔ s.Countable := by
  constructor
  · exact fun a ↦ countable_of_injective_of_countable_image hi a
  · exact fun a ↦ Countable.image a f

theorem Countable.not_countable_compl [Uncountable α] {s : Set α} (hs : s.Countable) : ¬ sᶜ.Countable := by
  intro h
  have h_unCount : Uncountable α := by infer_instance
  rw [← not_countable_iff] at h_unCount
  apply h_unCount
  have h_wholeSpace : s ∪ sᶜ = univ := union_compl_self s
  have h_count : (s ∪ sᶜ).Countable := by exact union hs h
  rw [h_wholeSpace] at h_count
  exact countable_univ_iff.mp h_count
-- This is probably way too long of a way to prove this I don't care atm

end Set
