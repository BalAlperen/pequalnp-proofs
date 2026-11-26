import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24963_aux
open PEqualNP.CircuitLowerBounds
def C : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 8]⟩, ⟨.not, [4]⟩, ⟨.not, [7]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [12, 13]⟩], 14⟩
end PEqualNP.Outside.L_meta_24963_aux

theorem PEqualNP.Outside.L_meta_24963 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6375343 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24963_aux.C, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_24963_aux.C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
