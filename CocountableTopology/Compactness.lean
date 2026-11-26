import CocountableTopology.Basic
import Mathlib.Topology.Separation.Hausdorff


-- Proving that subset of a cocountable space is compact if and only if it is finite

namespace CocountableTopology

theorem subset_isCompact_iff_finite {X : Type*} {s: Set (CocountableTopology X)} :
  CompactSpace s ↔ s.Finite := by
    constructor
    · intro hS
      by_contra
      have hsCompact : IsCompact s := by exact isCompact_iff_compactSpace.mpr hS
      have hsInfinite : s.Infinite := this
      obtain ⟨t,hts, htCountable, htInfinite⟩ := hsInfinite.exists_subset_countable_infinite

      have hTClosed : IsClosed t := by
        apply isClosed_iff.mpr (Or.inr htCountable)

      have htCompact : IsCompact t := IsCompact.of_isClosed_subset hsCompact hTClosed hts

      have htDiscrete : DiscreteTopology t := by
        apply discreteTopology_iff_forall_isClosed.mpr
        intro u
        let v : Set (CocountableTopology X) := Subtype.val '' u
        have hVT : v ⊆ t := by exact Subtype.coe_image_subset t u
        have hvCountable : v.Countable := by exact Set.Countable.mono hVT htCountable
        have hvClosed : IsClosed v := by
          apply isClosed_iff.mpr (Or.inr hvCountable)

        have hPreimage : Subtype.val ⁻¹'v = u := by
          ext x
          change (x.val ∈ Subtype.val '' u) ↔ x ∈ u
          constructor
          · rintro ⟨ y, hy,hx ⟩
            grind
          · intro hx
            simpa

        rw [←hPreimage]
        exact IsClosed.preimage_val hvClosed


      have htFinite : t.Finite := by
        let dT : DiscreteTopology t := htDiscrete
        have hUnivCompact : IsCompact (Set.univ : Set t) :=
          isCompact_iff_isCompact_univ.mp htCompact
        have hUnivFinite : (Set.univ : Set t).Finite := _root_.isCompact_iff_finite.mp hUnivCompact
        let fT : Finite t := Set.finite_univ_iff.mp hUnivFinite
        exact Set.not_infinite.mp fun a ↦ htInfinite fT

      exact (iff_false_intro htInfinite).mp htFinite

    · intro h
      have hS : IsCompact s := Set.Finite.isCompact h
      exact isCompact_iff_compactSpace.mp hS

theorem compactSpace_iff_finite {X : Type*} : CompactSpace (CocountableTopology X) ↔ Finite X := by
  calc
    CompactSpace (CocountableTopology X) ↔ IsCompact (Set.univ : Set (CocountableTopology X)) :=
      isCompact_univ_iff.symm
    _ ↔ CompactSpace (Set.univ : Set (CocountableTopology X)) := isCompact_iff_compactSpace
    _ ↔ (Set.univ : Set (CocountableTopology X)).Finite := subset_isCompact_iff_finite
    _ ↔ Finite (CocountableTopology X) :=Set.finite_univ_iff
    _ ↔ Finite X := (CocountableTopology.of (X := X)).symm.finite_iff

end CocountableTopology
