import CocountableTopology.Definitions
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Set.Countable
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Data.Set.Disjoint

universe u
variable {X : Type u}



theorem not_t2_space [Uncountable X] : ¬ T2Space (CocountableTopology X) := by
    intro h1

    have h2 : ∃ a b : (CocountableTopology X), a ≠ b := by exact exists_pair_ne (CocountableTopology X)
    obtain ⟨a, b, hab⟩ := h2

    obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := h1.t2 hab 

    have h3 : (Uᶜ ∪ Vᶜ).Countable := Set.Countable.union (isOpen_iff.mp hU ⟨a, haU⟩) (isOpen_iff.mp hV ⟨b, hbV⟩)

    rw[Set.disjoint_iff_inter_eq_empty] at hUV
    rw[<-Set.compl_inter, hUV, Set.compl_empty, Set.countable_univ_iff] at h3

    have h4 : Countable X := (WithTopology.equiv X TopologicalSpace.Cocountable).countable_iff.mp h3
    simp only [not_countable] at h4














