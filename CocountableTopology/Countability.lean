import CocountableTopology.Basic
import CocountableTopology.Separability
import CocountableTopology.Limits
import Mathlib.Topology.Bases
import Mathlib.Topology.Sequences


-- Proving that an uncountable space with the cocountable topology is not second-countable or first-countable
-- Also proving that a countable space is both, trivially

open TopologicalSpace
open Set

variable {X : Type*}

namespace CocountableTopology

theorem uncountable_not_secondCountable [Uncountable X] : ¬ SecondCountableTopology (CocountableTopology X) := by
  intro _
  have h : ¬ SeparableSpace (CocountableTopology X) := uncountable_not_separableSpace
  apply h
  exact SecondCountableTopology.to_separableSpace

theorem uncountable_not_firstCountable [Uncountable X] : ¬ FirstCountableTopology (CocountableTopology X) := by
  intro h_firstCount
  have h_nonEmpt : Nonempty (CocountableTopology X) := by infer_instance
  obtain ⟨x⟩ := h_nonEmpt
  let U : Set (CocountableTopology X) := {x}ᶜ
  have hX_unCount : Uncountable (CocountableTopology X) := of.injective.uncountable
  have hU_unCount : ¬ U.Countable := Countable.not_countable_compl (countable_singleton x)
  have hUX : closure U = univ := by
    have hi : IsClosed (closure U) := isClosed_closure
    rw [isClosed_iff] at hi
    rcases hi with hi' | hi'
    · assumption
    · exfalso
      apply hU_unCount
      exact Countable.mono (subset_closure) (hi')
  have hUx : x ∈ closure U := by
    rw [hUX]
    exact mem_univ x
  rw [mem_closure_iff_seq_limit] at hUx
  obtain ⟨s, hs, hs'⟩ := hUx
  rw [tendsto_iff_eventually_eq] at hs'
  obtain ⟨n, hn⟩ := hs'.exists
  specialize hs n
  exact (iff_false_intro hs).mp hn

instance [Countable X] : SecondCountableTopology (CocountableTopology X) := by
  have h : Countable (CocountableTopology X) := of.symm.injective.countable
  have h' : DiscreteTopology (CocountableTopology X) := discreteTopology_iff.mpr inferInstance
  infer_instance

instance [Countable X] : FirstCountableTopology (CocountableTopology X) := by
  infer_instance

end CocountableTopology
