import CocountableTopology.Basic
import Mathlib.Topology.Separation.Hausdorff


-- Proving that any countable set with the cocountable topology is a Hausdorff (T2) space

open CocountableTopology

variable {X : Type*}

namespace CocountableTopology

instance [Countable X] : T2Space (CocountableTopology X) := by
  let : DiscreteTopology (CocountableTopology X) :=
    discreteTopology_iff.mpr inferInstance
  exact DiscreteTopology.toT2Space

end CocountableTopology
