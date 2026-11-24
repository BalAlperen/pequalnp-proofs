import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2776_aux

open PEqualNP.CircuitLowerBounds

def opV : GateOp → List (BitVec 24) → BitVec 24
  | GateOp.and, l => l.foldr (fun a b => a &&& b) (BitVec.allOnes 24)
  | GateOp.or, l => l.foldr (fun a b => a ||| b) 0
  | _, _ => 0

def stepV (w : List (BitVec 24)) (g : Gate) : List (BitVec 24) :=
  w ++ [opV g.op (g.inputs.map fun i => w.getD i 0)]

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def IsAO (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

theorem getD_map_bit (w : List (BitVec 24)) (j i : ℕ) :
    (w.map fun v => v.getLsbD i).getD j false = (w.getD j 0).getLsbD i := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? <;> simp

theorem opV_bit (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List (BitVec 24)) (i : ℕ) (hi : i < 24) :
    (opV op l).getLsbD i = op.eval (l.map fun v => v.getLsbD i) := by
  rcases hop with rfl | rfl
  · induction l with
    | nil =>
      simp only [opV, GateOp.eval, List.foldr_nil, List.map_nil, BitVec.getLsbD_allOnes]
      simp [hi]
    | cons a l ih =>
      simp only [opV, GateOp.eval] at ih ⊢
      rw [List.foldr_cons, BitVec.getLsbD_and, ih] <;> rfl
  · induction l with
    | nil => simp [opV, GateOp.eval]
    | cons a l ih =>
      simp only [opV, GateOp.eval] at ih ⊢
      rw [List.foldr_cons, BitVec.getLsbD_or, ih] <;> rfl

theorem fold_bit (gs : List Gate) (hgs : ∀ g ∈ gs, IsAO g) (i : ℕ) (hi : i < 24) :
    ∀ init : List (BitVec 24),
      (gs.foldl stepV init).map (fun v => v.getLsbD i)
        = gs.foldl stepB (init.map fun v => v.getLsbD i) := by
  induction gs with
  | nil => intro init; rfl
  | cons g gs ih =>
    intro init
    simp only [List.foldl_cons]
    rw [ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))]
    congr 1
    simp only [stepV, stepB, List.map_append, List.map_cons, List.map_nil]
    congr 2
    rw [opV_bit _ (hgs g (by simp)) _ i hi]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp, getD_map_bit]

def extStep (X4 : List (BitVec 24)) (s : List (BitVec 24) × List (BitVec 24)) (g : Gate) :
    List (BitVec 24) × List (BitVec 24) :=
  (s.1 ++ [opV g.op (g.inputs.map fun i => s.1.getD i 0)],
    if opV g.op (g.inputs.map fun i => s.1.getD i 0) ∈ X4 ++ s.2 then s.2
    else s.2 ++ [opV g.op (g.inputs.map fun i => s.1.getD i 0)])

theorem ext_fst (X4 : List (BitVec 24)) (gs : List Gate) :
    ∀ w acc : List (BitVec 24), (gs.foldl (extStep X4) (w, acc)).1 = gs.foldl stepV w := by
  induction gs with
  | nil => intro w acc; rfl
  | cons g gs ih =>
    intro w acc
    simp only [List.foldl_cons]
    exact ih _ _

def Chain (X4 acc : List (BitVec 24)) : Prop :=
  ∀ (n : ℕ) (h : n < acc.length), acc[n] ∉ X4 ++ List.take n acc ∧
    ∃ a ∈ X4 ++ List.take n acc, ∃ b ∈ X4 ++ List.take n acc,
      acc[n] = a &&& b ∨ acc[n] = a ||| b

def Cover (X4 w acc : List (BitVec 24)) : Prop := ∀ j : ℕ, w.getD j 0 ∈ X4 ++ acc

theorem getD_snoc (w : List (BitVec 24)) (v : BitVec 24) (j : ℕ) :
    (w ++ [v]).getD j 0 = w.getD j 0 ∨ (w ++ [v]).getD j 0 = v := by
  rcases lt_trichotomy j w.length with h | h | h
  · left; rw [List.getD_append _ _ _ _ h]
  · right; subst h; simp
  · left
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem or0 (x : BitVec 24) : (x ||| 0) = x := by simp

theorem opV_shape (X4 w acc : List (BitVec 24)) (h0 : (0 : BitVec 24) ∈ X4)
    (h1 : BitVec.allOnes 24 ∈ X4) (hc : Cover X4 w acc) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (hl : l.length ≤ 2) :
    opV op (l.map fun i => w.getD i 0) ∉ X4 ++ acc →
    ∃ a ∈ X4 ++ acc, ∃ b ∈ X4 ++ acc,
      opV op (l.map fun i => w.getD i 0) = a &&& b ∨
        opV op (l.map fun i => w.getD i 0) = a ||| b := by
  match l, hl with
  | [], _ =>
    intro hm
    exfalso
    apply hm
    rcases hop with rfl | rfl
    · simp only [List.map_nil, opV, List.foldr_nil]
      exact List.mem_append_left _ h1
    · simp only [List.map_nil, opV, List.foldr_nil]
      exact List.mem_append_left _ h0
  | [a], _ =>
    intro hm
    exfalso
    apply hm
    rcases hop with rfl | rfl
    · simp only [List.map_cons, List.map_nil, opV, List.foldr_cons, List.foldr_nil,
        BitVec.and_allOnes]
      exact hc a
    · simp only [List.map_cons, List.map_nil, opV, List.foldr_cons, List.foldr_nil,
        or0]
      exact hc a
  | [a, b], _ =>
    intro _
    refine ⟨w.getD a 0, hc a, w.getD b 0, hc b, ?_⟩
    rcases hop with rfl | rfl
    · left
      simp only [List.map_cons, List.map_nil, opV, List.foldr_cons, List.foldr_nil,
        BitVec.and_allOnes]
    · right
      simp only [List.map_cons, List.map_nil, opV, List.foldr_cons, List.foldr_nil,
        or0]
  | _ :: _ :: _ :: _, h => simp at h

theorem step_inv (X4 : List (BitVec 24)) (h0 : (0 : BitVec 24) ∈ X4)
    (h1 : BitVec.allOnes 24 ∈ X4) (w acc : List (BitVec 24)) (g : Gate)
    (hg : IsAO g) (hlen : g.inputs.length ≤ 2)
    (hc : Cover X4 w acc) (hch : Chain X4 acc) :
    Cover X4 (extStep X4 (w, acc) g).1 (extStep X4 (w, acc) g).2 ∧
      Chain X4 (extStep X4 (w, acc) g).2 ∧
      (extStep X4 (w, acc) g).2.length ≤ acc.length + 1 := by
  have hshape := opV_shape X4 w acc h0 h1 hc g.op hg g.inputs hlen
  have hext : extStep X4 (w, acc) g =
      (w ++ [opV g.op (g.inputs.map fun i => w.getD i 0)],
        if opV g.op (g.inputs.map fun i => w.getD i 0) ∈ X4 ++ acc then acc
        else acc ++ [opV g.op (g.inputs.map fun i => w.getD i 0)]) := rfl
  rw [hext]
  generalize opV g.op (g.inputs.map fun i => w.getD i 0) = v at hshape ⊢
  by_cases hm : v ∈ X4 ++ acc
  · rw [if_pos hm]
    refine ⟨?_, hch, by simp⟩
    intro j
    rcases getD_snoc w v j with e | e <;> rw [e]
    · exact hc j
    · exact hm
  · rw [if_neg hm]
    have hsub : ∀ x, x ∈ X4 ++ acc → x ∈ X4 ++ (acc ++ [v]) := by
      intro x hx
      rw [← List.append_assoc]
      exact List.mem_append_left _ hx
    refine ⟨?_, ?_, by simp⟩
    · intro j
      rcases getD_snoc w v j with e | e <;> rw [e]
      · exact hsub _ (hc j)
      · simp
    · intro n hn
      have hn2 : n < acc.length + 1 := by simpa using hn
      rcases Nat.lt_or_ge n acc.length with hlt | hge
      · have ht : List.take n (acc ++ [v]) = List.take n acc :=
          List.take_append_of_le_length (by omega)
        have hgt : (acc ++ [v])[n] = acc[n] := List.getElem_append_left hlt
        rw [ht, hgt]
        exact hch n hlt
      · have hn' : n = acc.length := by omega
        subst hn'
        have ht : List.take acc.length (acc ++ [v]) = acc := by simp
        have hgt : (acc ++ [v])[acc.length] = v := by simp
        rw [ht, hgt]
        exact ⟨hm, hshape hm⟩

theorem fold_inv (X4 : List (BitVec 24)) (h0 : (0 : BitVec 24) ∈ X4)
    (h1 : BitVec.allOnes 24 ∈ X4) (gs : List Gate)
    (hgs : ∀ g ∈ gs, IsAO g ∧ g.inputs.length ≤ 2) :
    ∀ w acc : List (BitVec 24), Cover X4 w acc → Chain X4 acc →
      Cover X4 (gs.foldl (extStep X4) (w, acc)).1 (gs.foldl (extStep X4) (w, acc)).2 ∧
        Chain X4 (gs.foldl (extStep X4) (w, acc)).2 ∧
        (gs.foldl (extStep X4) (w, acc)).2.length ≤ acc.length + gs.length := by
  induction gs with
  | nil => intro w acc hc hch; exact ⟨hc, hch, by simp⟩
  | cons g gs ih =>
    intro w acc hc hch
    obtain ⟨hc', hch', hl'⟩ :=
      step_inv X4 h0 h1 w acc g (hgs g (by simp)).1 (hgs g (by simp)).2 hc hch
    have hrest := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      (extStep X4 (w, acc) g).1 (extStep X4 (w, acc) g).2 hc' hch'
    simp only [List.foldl_cons]
    have e : extStep X4 (w, acc) g = ((extStep X4 (w, acc) g).1, (extStep X4 (w, acc) g).2) := rfl
    rw [e]
    refine ⟨hrest.1, hrest.2.1, ?_⟩
    have hl3 := hrest.2.2
    simp only [List.length_cons]
    omega

def X4c : List (BitVec 24) :=
  [0, 16777215, 4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296, 12709888,
    16646144, 13339321]

def initV : List (BitVec 24) := X4c.drop 2

def pts : List ℕ :=
  [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288,
    320, 385, 402]

def pos : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

theorem init_bits : ∀ i : Fin 24, initV.map (fun v => v.getLsbD i) =
    List.ofFn (fun j : Fin 9 => (pts.getD i 0).testBit j) ++
      [(pts.getD i 0).testBit ((0 : Fin 9) : ℕ) || (pts.getD i 0).testBit ((4 : Fin 9) : ℕ)] := by
  decide +kernel

theorem target_bits : ∀ i : Fin 24,
    (3428671 : BitVec 24).getLsbD i = decide (pts.getD i 0 ∈ pos) := by
  decide +kernel

theorem init_sub : ∀ v ∈ initV, v ∈ X4c := fun _ h => List.mem_of_mem_drop h

theorem all24 : BitVec.allOnes 24 = (16777215 : BitVec 24) := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem main (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hev : ∀ x3 ∈ pts,
      C.eval (List.ofFn (fun j : Fin 9 => x3.testBit j) ++
        [x3.testBit ((0 : Fin 9) : ℕ) || x3.testBit ((4 : Fin 9) : ℕ)]) = decide (x3 ∈ pos)) :
    ∃ x5 : List (BitVec 24), x5.length ≤ C.size ∧ Chain X4c x5 ∧
      (3428671 : BitVec 24) ∈ X4c ++ x5 := by
  have hgs : ∀ g ∈ C.gates, IsAO g ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hl⟩ := hm g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, hl⟩
  have h0 : (0 : BitVec 24) ∈ X4c := by
    unfold X4c
    exact List.Mem.head _
  have h1 : BitVec.allOnes 24 ∈ X4c := by
    rw [all24]
    unfold X4c
    exact List.Mem.tail _ (List.Mem.head _)
  have hcov0 : Cover X4c initV [] := by
    intro j
    rw [List.append_nil, List.getD_eq_getElem?_getD]
    rcases hj : initV[j]? with _ | v
    · exact h0
    · exact init_sub v (List.mem_of_getElem? hj)
  have hch0 : Chain X4c [] := by
    intro n hn
    simp at hn
  obtain ⟨hcov, hch, hlen⟩ := fold_inv X4c h0 h1 C.gates hgs initV [] hcov0 hch0
  refine ⟨_, by simpa [Circuit.size] using hlen, hch, ?_⟩
  have key : (C.gates.foldl stepV initV).getD C.output 0 = 3428671 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hp : pts.getD i 0 ∈ pts := by
      rw [List.getD_eq_getElem _ _ (by simp [pts]; omega)]
      exact List.getElem_mem _
    have hb : initV.map (fun v => v.getLsbD i) =
        List.ofFn (fun j : Fin 9 => (pts.getD i 0).testBit j) ++
          [(pts.getD i 0).testBit ((0 : Fin 9) : ℕ) || (pts.getD i 0).testBit ((4 : Fin 9) : ℕ)] :=
      init_bits ⟨i, hi⟩
    have ht : (3428671 : BitVec 24).getLsbD i = decide (pts.getD i 0 ∈ pos) :=
      target_bits ⟨i, hi⟩
    have hw : C.wires (initV.map fun v => v.getLsbD i) =
        (C.gates.foldl stepV initV).map (fun v => v.getLsbD i) :=
      (fold_bit C.gates (fun g hg => (hgs g hg).1) i hi initV).symm
    rw [ht, ← hev _ hp, ← getD_map_bit, ← hw, hb]
    rfl
  have hmem := hcov C.output
  rw [ext_fst, key] at hmem
  exact hmem

end PEqualNP.Outside.L_meta_2776_aux

open PEqualNP.Outside.L_meta_2776_aux in
theorem PEqualNP.Outside.L_meta_2776 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       have x4 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))];       ∃ (x5 : List (BitVec (24 : ℕ))), x5.length ≤ x1.size ∧ (∀ (x6 : ℕ) (x7 : x6 < x5.length), x5[x6] ∉ x4 ++ List.take x6 x5 ∧ ∃ x8 ∈ x4 ++ List.take x6 x5, ∃ x9 ∈ x4 ++ List.take x6 x5, x5[x6] = x8 &&& x9 ∨ x5[x6] = x8 ||| x9) ∧ (3428671 : BitVec (24 : ℕ)) ∈ x4 ++ x5 := by
  intro x1 hm hev
  exact main x1 hm hev
