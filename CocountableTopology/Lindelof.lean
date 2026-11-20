import CocountableTopology.Basic
import Mathlib.Topology.Compactness.Lindelof


-- Proving that any space with the cocountable topology is a Lindelöf space

open Set
open CocountableTopology

variable {X : Type*}

namespace CocountableTopology

instance : LindelofSpace (CocountableTopology X) := by
  rw [← isLindelof_univ_iff, isLindelof_iff_countable_subcover]
  intro I B hBo h_cover
  by_cases h : IsEmpty (CocountableTopology X)
  · use ∅
    constructor
    · exact countable_empty
    · exact le_of_subsingleton
  · have h' : ∀x : CocountableTopology X, ∃i : I, x ∈ B i := by
      intro _
      exact mem_iUnion.mp (h_cover trivial)
    choose f hf using h'
    rw [not_isEmpty_iff] at h
    obtain ⟨x⟩ := h
    let i₀ := f x
    let I₀ := f '' (B i₀)ᶜ
    have hI₀ : I₀.Countable := by
      suffices (B i₀)ᶜ.Countable by exact Countable.image this f
      have hBi : (B i₀).Nonempty := by exact nonempty_of_mem (hf x)
      exact isOpen_iff.mp (hBo i₀) hBi
    let I' := {i₀} ∪ I₀
    use I'
    constructor
    · exact Countable.union (countable_singleton i₀) (hI₀)
    · intro y hy
      by_cases hyB : y ∈ B i₀
      · rw [mem_iUnion]
        use i₀
        rw [mem_iUnion]
        constructor
        · assumption
        · exact mem_union_left I₀ rfl
      · rw [mem_iUnion]
        use f y
        rw [mem_iUnion]
        constructor
        · exact hf y
        · grind

end CocountableTopology
