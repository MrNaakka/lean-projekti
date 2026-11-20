import CocountableTopology.Basic
import Mathlib.Topology.Separation.Hausdorff


-- Proving that a continuous function from an uncountable space with the cocountable topology to a Hausdorff space is constant

open CocountableTopology

variable {X Y : Type*} [Uncountable X] [TopologicalSpace Y] [T2Space Y]

namespace CocountableTopology

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
