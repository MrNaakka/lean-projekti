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

end Set
