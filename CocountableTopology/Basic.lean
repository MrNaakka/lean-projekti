import CocountableTopology.Auxiliary
import Mathlib.Order.Filter.Cocardinal
import Mathlib.Topology.Constructions
#check CofiniteTopology


-- Here we define the cocountable topology, prove it is a topology and provide some basic results

open Set
open Topology
open Filter

variable {X : Type*}

-- Definition of cocountable topology
@[implicit_reducible]
def TopologicalSpace.Cocountable : TopologicalSpace X where
    IsOpen s := s.Nonempty → sᶜ.Countable
    isOpen_univ := by simp
    isOpen_inter s t := by
        rintro hs ht ⟨x, hxs, hxt⟩
        rw [compl_inter]
        exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
    isOpen_sUnion := by
        rintro s h ⟨x, t, hts, hzt⟩
        rw [compl_sUnion]
        exact sInter_countable (mem_image_of_mem _ hts) (h t hts ⟨x, hzt⟩)

abbrev CocountableTopology (X : Type*) :=
    WithTopology X .Cocountable

namespace CocountableTopology

-- Basic results and API for the cocountable topology
def of : X ≃ CocountableTopology X := (WithTopology.equiv _ _).symm

theorem isOpen_iff {s : Set (CocountableTopology X)} : IsOpen s ↔ s.Nonempty → sᶜ.Countable := by
  simp_rw [isOpen_coinduced, TopologicalSpace.Cocountable, isOpen_mk, ← preimage_compl,
    WithTopology.preimage_toTopology, image_nonempty,
    countable_image_iff (WithTopology.ofTopology_injective _).injOn]

theorem isOpen_iff' {s : Set (CocountableTopology X)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Countable := by
  simp only [isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]

theorem isClosed_iff {s : Set (CocountableTopology X)} : IsClosed s ↔ s = univ ∨ s.Countable := by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_compl, compl_empty_iff]

theorem nhds_eq (x : CocountableTopology X) : 𝓝 x = pure x ⊔ cocountable := by
  ext U
  simp_rw [mem_nhds_iff, isOpen_iff, mem_sup, mem_pure, mem_cocountable]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    constructor
    · exact hVU haV
    · have hVc : Vᶜ.Countable := V_op ⟨x, haV⟩
      have hUV : Uᶜ ⊆ Vᶜ := compl_subset_compl_of_subset hVU
      exact Countable.mono hUV hVc
  · rintro ⟨hU : x ∈ U, hU' : Uᶜ.Countable⟩
    exact ⟨U, Subset.rfl, fun _ => hU', hU⟩

theorem mem_nhds_iff {x : CocountableTopology X} {s : Set (CocountableTopology X)} :
    s ∈ 𝓝 x ↔ x ∈ s ∧ sᶜ.Countable := by
  rw [nhds_eq, mem_sup, mem_pure, mem_cocountable]

end CocountableTopology
