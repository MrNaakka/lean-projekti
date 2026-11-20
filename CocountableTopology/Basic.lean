import CocountableTopology.Auxiliary
import Mathlib.Order.Filter.Cocardinal
import Mathlib.Topology.Constructions
#check CofiniteTopology


-- Here we define the cocountable topology, prove it is a topology and provide some basic results

open Set
open Topology
open Filter

variable {X : Type*}

-- Definition of cocountable topology
@[implicit_reducible]
def TopologicalSpace.Cocountable : TopologicalSpace X where
    IsOpen s := s.Nonempty → sᶜ.Countable
    isOpen_univ := by simp
    isOpen_inter s t := by
        rintro hs ht ⟨x, hxs, hxt⟩
        rw [compl_inter]
        exact (hs ⟨x, hxs⟩).union (ht ⟨x, hxt⟩)
    isOpen_sUnion := by
        rintro s h ⟨x, t, hts, hzt⟩
        rw [compl_sUnion]
        exact sInter_countable (mem_image_of_mem _ hts) (h t hts ⟨x, hzt⟩)

abbrev CocountableTopology (X : Type*) :=
    WithTopology X .Cocountable

namespace CocountableTopology

-- Basic results and API for the cocountable topology
def of : X ≃ CocountableTopology X := (WithTopology.equiv _ _).symm

theorem isOpen_iff {s : Set (CocountableTopology X)} : IsOpen s ↔ s.Nonempty → sᶜ.Countable := by
  simp_rw [isOpen_coinduced, TopologicalSpace.Cocountable, isOpen_mk, ← preimage_compl,
    WithTopology.preimage_toTopology, image_nonempty,
    countable_image_iff (WithTopology.ofTopology_injective _).injOn]

theorem isOpen_iff' {s : Set (CocountableTopology X)} : IsOpen s ↔ s = ∅ ∨ sᶜ.Countable := by
  simp only [isOpen_iff, nonempty_iff_ne_empty, or_iff_not_imp_left]

theorem isClosed_iff {s : Set (CocountableTopology X)} : IsClosed s ↔ s = univ ∨ s.Countable := by
  simp only [← isOpen_compl_iff, isOpen_iff', compl_compl, compl_empty_iff]

theorem nhds_eq (x : CocountableTopology X) : 𝓝 x = pure x ⊔ cocountable := by
  ext U
  simp_rw [mem_nhds_iff, isOpen_iff, mem_sup, mem_pure, mem_cocountable]
  constructor
  · rintro ⟨V, hVU, V_op, haV⟩
    constructor
    · exact hVU haV
    · have hVc : Vᶜ.Countable := V_op ⟨x, haV⟩
      have hUV : Uᶜ ⊆ Vᶜ := compl_subset_compl_of_subset hVU
      exact Countable.mono hUV hVc
  · rintro ⟨hU : x ∈ U, hU' : Uᶜ.Countable⟩
    exact ⟨U, Subset.rfl, fun _ => hU', hU⟩

theorem mem_nhds_iff {x : CocountableTopology X} {s : Set (CocountableTopology X)} :
    s ∈ 𝓝 x ↔ x ∈ s ∧ sᶜ.Countable := by
  rw [nhds_eq, mem_sup, mem_pure, mem_cocountable]

theorem discreteTopology_iff : DiscreteTopology (CocountableTopology X) ↔ Countable X := by
  constructor
  · intro h
    by_cases hX : Nonempty X
    · obtain ⟨x⟩ := hX
      let x' : CocountableTopology X := CocountableTopology.of x
      have hcompl : ({x'}ᶜ  : Set (CocountableTopology X)).Countable :=
        CocountableTopology.isOpen_iff.mp (isOpen_discrete _) ⟨x', rfl⟩
      have huniv : (univ : Set (CocountableTopology X)).Countable := by
        rw [show (univ : Set (CocountableTopology X)) = {x'} ∪ {x'}ᶜ by
          simp]
        exact Countable.union (countable_singleton x') hcompl

      have hcount : Countable (CocountableTopology X) := by
        rwa [← countable_univ_iff]

      exact CocountableTopology.of.countable_iff.mpr hcount
    · exact not_uncountable_iff.mp fun a ↦ hX Nontrivial.to_nonempty
  · intro h
    have hcount : Countable (CocountableTopology X) := by
      rwa [← CocountableTopology.of.countable_iff]
    rw [discreteTopology_iff_isOpen_singleton]
    intro x
    exact CocountableTopology.isOpen_iff'.mpr (Or.inr (Set.to_countable _))

theorem not_disjoint_of_isOpen [Uncountable X]
    {U V : Set (CocountableTopology X)}
    (hU : IsOpen U) (hV : IsOpen V)
    (hneU : U.Nonempty) (hneV : V.Nonempty) :
    ¬ Disjoint U V := by
  intro hd
  have hcU : Uᶜ.Countable := CocountableTopology.isOpen_iff.mp hU hneU
  have hcV : Vᶜ.Countable := CocountableTopology.isOpen_iff.mp hV hneV
  have hinter : U ∩ V = ∅ := by
    exact Disjoint.inter_eq hd
  have hunion : Uᶜ ∪ Vᶜ = univ := by
    rw [← compl_inter]
    exact compl_univ_iff.mpr hinter
  have hc : (univ : Set (CocountableTopology X)).Countable := by
    rw [← hunion]
    exact hcU.union hcV
  have hcount : Countable X :=
    CocountableTopology.of.countable_iff.mpr (countable_univ_iff.mp hc)
  exact (not_uncountable_iff.mpr hcount) (inferInstance : Uncountable X)


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
