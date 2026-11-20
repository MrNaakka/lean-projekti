import CocountableTopology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff

-- Proving that any countable set with the cocountable topology is a Hausdorff (T2) space

open CocountableTopology

variable {X Y : Type*}

namespace CocountableTopology

instance [Countable X] : T2Space (CocountableTopology X) := by
  let : DiscreteTopology (CocountableTopology X) :=
    discreteTopology_iff.mpr inferInstance
  exact DiscreteTopology.toT2Space

variable [Uncountable X] [TopologicalSpace Y] [T2Space Y]

theorem continuous_implies_constant (f : CocountableTopology X → Y) (hf : Continuous f) :
  ∀ a b, f a = f b := by
  intro a b
  by_contra h
  obtain ⟨U, V, hU, hV,ha,hb, hd⟩ := t2_separation h
  let A := f ⁻¹' U
  let B := f ⁻¹' V

  have hA : IsOpen A := by
    exact hf.isOpen_preimage U hU

  have hB : IsOpen B := by
    exact hf.isOpen_preimage V hV

  have hAn : (f ⁻¹' U).Nonempty := ⟨a, ha⟩
  have hBn : (f ⁻¹' V).Nonempty := ⟨b, hb⟩

  apply not_disjoint_of_isOpen hA hB hAn hBn
  exact Disjoint.preimage f hd

end CocountableTopology
