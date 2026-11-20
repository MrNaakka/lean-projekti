import CocountableTopology.Basic


-- Proving that when the underlying space is finite, the cocountable topology and the cofinite topology coincide

variable {X : Type*} [Finite X]

theorem cocountable_is_cofinite : (TopologicalSpace.Cocountable : TopologicalSpace X) = TopologicalSpace.cofinite := by
  ext x
  constructor
  · intro hx1 hx2
    exact Set.toFinite xᶜ
  · intro hx1 hx2
    exact Set.Finite.countable (hx1 hx2)
