import CocountableTopology.Basic


-- Proving that in the cocountable topology, a sequence converging to a limit is equivalent to it being eventually constant

open Filter
open Topology

variable {X : Type*}

namespace CocountableTopology

theorem tendsto_iff_eventually_eq (s : ℕ → CocountableTopology X) (x : CocountableTopology X) :
    Tendsto s atTop (𝓝 x) ↔ ∀ᶠ n in atTop, s n = x := by
  constructor
  · intro h
    let U : Set (CocountableTopology X) :=
      {y | y = x ∨ y ∉ Set.range s}
    have hx : x ∈ U := by
      grind

    have hc : Uᶜ.Countable := by
      have hsub : Uᶜ ⊆ Set.range s := by
        intro y hy
        change ¬(y = x ∨ y ∉ Set.range s) at hy
        push Not at hy
        apply hy.2
      apply Set.Countable.mono hsub
      exact Set.countable_range s

    have hU : U ∈ 𝓝 x := by
      apply mem_nhds_iff.mpr
      exact And.symm ⟨hc, hx⟩

    have he : ∀ᶠ n in atTop, s n ∈ U := by
      exact eventually_map.mp (h hU)

    filter_upwards [he] with n hn
    grind

  · intro h
    rw [tendsto_def]
    intro U hU

    filter_upwards [h] with n hn
    rw [mem_nhds_iff] at hU
    grind

end CocountableTopology
