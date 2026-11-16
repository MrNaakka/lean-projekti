import CocountableTopology.Definitions
import Mathlib.Topology.Separation.Basic

universe u
variable {X : Type u}

instance : T1Space (CocountableTopology X) := by
  apply t1Space_iff_exists_open.mpr
  intro a b hab

  let U : Set (CocountableTopology X) := {b}ᶜ 

  have h1 : IsOpen U := by 
    rw [isOpen_iff]
    intro _

    have h1 : Uᶜ = {b} := by
      exact compl_compl ({b} : Set (CocountableTopology X))

    rw [h1]
    exact Set.countable_singleton b
  use U

  exact ⟨h1, by exact Set.mem_compl_singleton_iff.mpr hab, by exact Set.notMem_compl_iff.mpr rfl⟩ 

