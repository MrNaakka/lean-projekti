import Mathlib.Topology.Constructions


theorem sInter_countable {α : Type*} {s : Set (Set α)} {t : Set α} (ht : t ∈ s) (hf : t.Countable) :
    (⋂₀ s).Countable := by
    exact Set.Countable.mono (fun ⦃a⦄ a_1 ↦ a_1 t ht) hf

@[implicit_reducible]
def TopologicalSpace.Cocountable {X : Type} : TopologicalSpace X where
    IsOpen s := s.Nonempty → Set.Countable sᶜ
    isOpen_univ := by simp
    isOpen_inter s t := by
        rintro hs ht ⟨x, hxs, hxt⟩
        rw [Set.compl_inter]
        exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
    isOpen_sUnion := by
        rintro s h ⟨x, t, hts, hzt⟩
        rw [Set.compl_sUnion]
        exact sInter_countable (Set.mem_image_of_mem _ hts) (h t hts ⟨x, hzt⟩)
