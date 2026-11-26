import CocountableTopology.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Set.Countable
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Data.Set.Disjoint


-- Proving that any countable set with the cocountable topology is a Hausdorff (T2) space and
-- that an uncountable set is not

open Set

variable {X : Type*}

namespace CocountableTopology

instance [Countable X] : T2Space (CocountableTopology X) := by
  let : DiscreteTopology (CocountableTopology X) :=
    discreteTopology_iff.mpr inferInstance
  exact DiscreteTopology.toT2Space

theorem uncountable_not_T2Space [Uncountable X] : ¬ T2Space (CocountableTopology X) := by
  intro h1

  have h2 : ∃ a b : (CocountableTopology X), a ≠ b := by
    exact exists_pair_ne (CocountableTopology X)
  obtain ⟨a, b, hab⟩ := h2

  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := h1.t2 hab

  have h3 : (Uᶜ ∪ Vᶜ).Countable :=
    Countable.union (isOpen_iff.mp hU ⟨a, haU⟩) (isOpen_iff.mp hV ⟨b, hbV⟩)

  rw[disjoint_iff_inter_eq_empty] at hUV
  rw[<-compl_inter, hUV, compl_empty, countable_univ_iff] at h3

  have h4 : Countable X := (WithTopology.equiv X TopologicalSpace.Cocountable).countable_iff.mp h3
  simp only [not_countable] at h4

end CocountableTopology
