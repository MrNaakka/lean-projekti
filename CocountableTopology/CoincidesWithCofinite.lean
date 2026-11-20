import CocountableTopology.Basic


-- Proving that when the underlying space is finite, the cocountable topology and the cofinite topology coincide
-- Note: this was made before "discreteTopology_iff", which could also be used to show this

variable {X : Type*} [Finite X]

namespace CocountableTopology

theorem cocountable_is_cofinite : (TopologicalSpace.Cocountable : TopologicalSpace X)
    = TopologicalSpace.cofinite := by
  ext x
  constructor
  · intro hx1 hx2
    exact Set.toFinite xᶜ
  · intro hx1 hx2
    exact Set.Finite.countable (hx1 hx2)

end CocountableTopology
