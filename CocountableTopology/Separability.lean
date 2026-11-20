import CocountableTopology.Basic
import Mathlib.Topology.Bases


-- Proving that an uncountable space with the cocountable topolgy is not separable, while a countable space is

open TopologicalSpace
open Set

variable {X : Type*}

theorem countable_separable [Countable X] : SeparableSpace (CocountableTopology X) := by
  have h : Countable (CocountableTopology X) := by
    rw [← CocountableTopology.of.countable_iff]
    infer_instance
  exact Countable.to_separableSpace

theorem uncountable_not_separable [Uncountable X] : ¬ SeparableSpace (CocountableTopology X) := by
  intro h
  rw [separableSpace_iff] at h
  obtain ⟨A, hAcount, hAdense⟩ := h
  have hAclosed : IsClosed A := by
    apply CocountableTopology.isClosed_iff.mpr
    right
    assumption
  have hAnotX : A ≠ univ := by
    intro hAX
    rw [hAX, countable_univ_iff, ← CocountableTopology.of.countable_iff] at hAcount
    exact not_countable (hAcount)
  have hAclousure : closure A = A := closure_eq_iff_isClosed.mpr hAclosed
  rw [dense_iff_closure_eq, hAclousure] at hAdense
  exact hAnotX hAdense
