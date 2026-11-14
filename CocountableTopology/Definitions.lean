import Mathlib.Topology.Constructions

#check CofiniteTopology


-- Auxiliary results
theorem sInter_countable {α : Type*} {s : Set (Set α)} {t : Set α} (ht : t ∈ s) (hf : t.Countable) :
    (⋂₀ s).Countable := Set.Countable.mono (fun ⦃_⦄ a_1 ↦ a_1 t ht) hf


-- Definition of cocountable topology
@[implicit_reducible]
def TopologicalSpace.Cocountable {X : Type*} : TopologicalSpace X where
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

abbrev CocountableTopology (X : Type*) :=
    WithTopology X .Cocountable

-- What do these even do they are just copied from cofinite topology
universe u v u' v'
variable {X : Type u}
variable {α : Type u} {β : Type v}


-- More auxiliary results
theorem countable_image_iff {s : Set α} {f : α → β} (hi : Set.InjOn f s) :
    (f '' s).Countable ↔ s.Countable := by
  constructor
  · exact fun a ↦ Set.countable_of_injective_of_countable_image hi a
  · exact fun a ↦ Set.Countable.image a f


-- Actual results and API for the cocountable topology
theorem isOpen_iff {s : Set (CocountableTopology X)} : IsOpen s ↔ s.Nonempty → sᶜ.Countable := by
  simp_rw [isOpen_coinduced, TopologicalSpace.Cocountable, isOpen_mk, ← Set.preimage_compl,
    WithTopology.preimage_toTopology, Set.image_nonempty,
    countable_image_iff (WithTopology.ofTopology_injective _).injOn]

theorem isOpen_iff' {s : Set (CocountableTopology X)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Countable := by
  simp only [isOpen_iff, Set.nonempty_iff_ne_empty, or_iff_not_imp_left]

theorem isClosed_iff {s : Set (CocountableTopology X)} : IsClosed s ↔ s = Set.univ ∨ s.Countable := by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_compl, Set.compl_empty_iff]
