import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24039_aux
open PEqualNP.CircuitLowerBounds
def C : Circuit := ⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [0, 4]⟩, ⟨.not, [8]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩
end PEqualNP.Outside.L_meta_24039_aux

theorem PEqualNP.Outside.L_meta_24039 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4438 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24039_aux.C, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_24039_aux.C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
