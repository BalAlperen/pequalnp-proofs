import Mathlib
import PEqualNP.Defs

-- Fix the line. Call a wire clean when it is false on the complement of the point set.
-- A clean OR gate whose two children accept distinct single points gives one edge vector
-- e_p - e_q. By induction on wires, any two single points accepted by a clean wire differ
-- by a vector in the span of these edges. The output accepts every point of the set, so the
-- span has rank at least the set size minus one, which bounds the number of such gates.

namespace PEqualNP.Outside.L_meta_3256_aux

open PEqualNP.CircuitLowerBounds

abbrev step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl step w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: t, ?_⟩
    rw [List.foldl_cons, ht]
    simp [step]

theorem fold_length (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem wires_lt (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  rw [wires_eq]
  obtain ⟨t, ht⟩ := fold_prefix C.gates x
  rw [ht, List.getD_append _ _ _ _ h]

theorem wires_ge (C : Circuit) (x : List Bool) (i : ℕ) (h : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false := by
  rw [wires_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [fold_length]; exact h

theorem gen (pre : List Gate) (g : Gate) (post : List Gate) (x : List Bool)
    (hb : ∀ j ∈ g.inputs, j < x.length + pre.length) :
    ((pre ++ g :: post).foldl step x).getD (x.length + pre.length) false =
      g.op.eval (g.inputs.map fun j => ((pre ++ g :: post).foldl step x).getD j false) := by
  rw [List.foldl_append, List.foldl_cons]
  have hW : (pre.foldl step x).length = x.length + pre.length := fold_length pre x
  obtain ⟨t, ht⟩ := fold_prefix post (step (pre.foldl step x) g)
  rw [ht]
  have key : ∀ j, j < x.length + pre.length →
      (step (pre.foldl step x) g ++ t).getD j false = (pre.foldl step x).getD j false := by
    intro j hj
    rw [List.getD_append _ _ _ _ (by simp [step]; omega)]
    rw [List.getD_append _ _ _ _ (by omega)]
  rw [List.getD_append _ _ _ _ (by simp [step]; omega)]
  rw [← hW]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [key j (hb j hj)]

theorem wires_gate (C : Circuit) (x : List Bool) (k : ℕ) (hk : k < C.gates.length)
    (hb : ∀ j ∈ (C.gates[k]).inputs, j < x.length + k) :
    (C.wires x).getD (x.length + k) false =
      (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun j => (C.wires x).getD j false) := by
  have hsplit : C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) = C.gates := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hlen : (C.gates.take k).length = k := by simp; omega
  have := gen (C.gates.take k) (C.gates[k]) (C.gates.drop (k + 1)) x (by rw [hlen]; exact hb)
  rw [hsplit, hlen] at this
  rw [wires_eq]
  exact this

def val (C : Circuit) (N : ℕ) (l : Fin N) (P : Finset (Fin N)) (i : ℕ) : Bool :=
  (C.wires (PEqualNP.GenericRejection.incidenceInput P {l})).getD i false

theorem inp_len (N : ℕ) (l : Fin N) (P : Finset (Fin N)) :
    (PEqualNP.GenericRejection.incidenceInput P {l}).length = N + N := by
  simp [PEqualNP.GenericRejection.incidenceInput]

theorem val_point (C : Circuit) (N : ℕ) (l : Fin N) (P : Finset (Fin N)) (i : ℕ) (h : i < N) :
    val C N l P i = decide ((⟨i, h⟩ : Fin N) ∈ P) := by
  unfold val
  rw [wires_lt _ _ _ (by rw [inp_len]; omega)]
  simp only [PEqualNP.GenericRejection.incidenceInput, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [h])]
  simp [h]

theorem val_line (C : Circuit) (N : ℕ) (l : Fin N) (P Q : Finset (Fin N)) (i : ℕ)
    (h1 : N ≤ i) (h2 : i < N + N) : val C N l P i = val C N l Q i := by
  unfold val
  rw [wires_lt _ _ _ (by rw [inp_len]; omega), wires_lt _ _ _ (by rw [inp_len]; omega)]
  simp [PEqualNP.GenericRejection.incidenceInput, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (show (List.ofFn fun p : Fin N => decide (p ∈ P)).length ≤ i
      by simpa using h1),
    List.getElem?_append_right (show (List.ofFn fun p : Fin N => decide (p ∈ Q)).length ≤ i
      by simpa using h1)]

theorem val_ge (C : Circuit) (N : ℕ) (l : Fin N) (P : Finset (Fin N)) (i : ℕ)
    (h : N + N + C.size ≤ i) : val C N l P i = false := by
  unfold val
  exact wires_ge _ _ _ (by rw [inp_len]; exact h)

theorem gate_shape (C : Circuit) (N : ℕ) (l : Fin N)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C) (k : ℕ) (hk : k < C.size) :
    (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 0 0 < N + N + k ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 1 0 < N + N + k ∧
    (((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and ∧
      ∀ P, val C N l P (N + N + k) =
        (val C N l P ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 0 0) &&
         val C N l P ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 1 0))) ∨
     ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or ∧
      ∀ P, val C N l P (N + N + k) =
        (val C N l P ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 0 0) ||
         val C N l P ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 1 0)))) := by
  obtain ⟨hop, hrb, h2⟩ := hAO
  have hk' : k < C.gates.length := hk
  have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    rfl
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk'
  have hrb' := hrb k hk'
  rw [hga] at hrb' ⊢
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h2 _ hmem)
  have ha : a < N + N + k := hrb' a (by rw [hab]; simp)
  have hb : b < N + N + k := hrb' b (by rw [hab]; simp)
  have hev : ∀ P, val C N l P (N + N + k) =
      (C.gates[k]).op.eval [val C N l P a, val C N l P b] := by
    intro P
    unfold val
    have := wires_gate C (PEqualNP.GenericRejection.incidenceInput P {l}) k hk'
      (by rw [inp_len]; intro j hj; exact hrb' j hj)
    rw [inp_len] at this
    rw [this, hab]
    rfl
  rw [hab]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨ha, hb, ?_⟩
  rcases hop _ hmem with ho | ho
  · left
    refine ⟨ho, fun P => ?_⟩
    rw [hev P, ho]
    simp [GateOp.eval]
  · right
    refine ⟨ho, fun P => ?_⟩
    rw [hev P, ho]
    simp [GateOp.eval]

theorem mono (C : Circuit) (N : ℕ) (l : Fin N) (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (P Q : Finset (Fin N)) (hPQ : P ⊆ Q) :
    ∀ i, val C N l P i = true → val C N l Q i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hP
    by_cases h1 : i < N
    · rw [val_point _ _ _ _ _ h1] at hP ⊢
      simp only [decide_eq_true_eq] at hP ⊢
      exact hPQ hP
    by_cases h2 : i < N + N
    · rw [val_line C N l Q P i (by omega) h2]; exact hP
    by_cases h3 : i < N + N + C.size
    · obtain ⟨k, rfl⟩ : ∃ k, i = N + N + k := ⟨i - (N + N), by omega⟩
      obtain ⟨ha, hb, hc | hc⟩ := gate_shape C N l hAO k (by omega)
      · rw [hc.2] at hP ⊢
        simp only [Bool.and_eq_true] at hP ⊢
        exact ⟨ih _ ha hP.1, ih _ hb hP.2⟩
      · rw [hc.2] at hP ⊢
        simp only [Bool.or_eq_true] at hP ⊢
        rcases hP with hP | hP
        · exact Or.inl (ih _ ha hP)
        · exact Or.inr (ih _ hb hP)
    · rw [val_ge _ _ _ _ _ (by omega)] at hP
      exact absurd hP (by simp)

open Classical in
noncomputable def vec (C : Circuit) (N : ℕ) (l : Fin N) (k : ℕ) : Fin N → ℚ :=
  if h : ∃ pq : Fin N × Fin N, pq.1 ≠ pq.2 ∧
      val C N l {pq.1} ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 0 0)
        = true ∧
      val C N l {pq.2} ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 1 0)
        = true
  then Pi.single (Classical.choose h).1 1 - Pi.single (Classical.choose h).2 1
  else 0

theorem span_inv (C : Circuit) (N : ℕ) (l : Fin N) (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (S : Finset (Fin N)) (F : Finset ℕ)
    (hF : ∀ k < C.size, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or →
      val C N l Sᶜ (N + N + k) = false →
      (∃ p q : Fin N, p ≠ q ∧ val C N l {p} (N + N + k) = true ∧
        val C N l {q} (N + N + k) = true) → k ∈ F) :
    ∀ i, val C N l Sᶜ i = false → ∀ p q : Fin N, val C N l {p} i = true →
      val C N l {q} i = true →
      (Pi.single p 1 - Pi.single q 1 : Fin N → ℚ) ∈
        Submodule.span ℚ ((F.image (vec C N l) : Finset (Fin N → ℚ)) : Set (Fin N → ℚ)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hc p q hp hq
    by_cases hpq : p = q
    · subst hpq; simp
    by_cases h1 : i < N
    · rw [val_point _ _ _ _ _ h1] at hp hq
      simp only [decide_eq_true_eq, Finset.mem_singleton] at hp hq
      exact absurd (hp.symm.trans hq) hpq
    by_cases h2 : i < N + N
    · rw [val_line C N l {p} Sᶜ i (by omega) h2] at hp
      rw [hp] at hc
      exact absurd hc (by simp)
    by_cases h3 : i < N + N + C.size
    · obtain ⟨k, rfl⟩ : ∃ k, i = N + N + k := ⟨i - (N + N), by omega⟩
      obtain ⟨ha, hb, hg | hg⟩ := gate_shape C N l hAO k (by omega)
      · rw [hg.2] at hc hp hq
        simp only [Bool.and_eq_true] at hp hq
        rcases Bool.and_eq_false_iff.mp hc with hca | hcb
        · exact ih _ ha hca p q hp.1 hq.1
        · exact ih _ hb hcb p q hp.2 hq.2
      · have hc0 := hc
        rw [hg.2] at hc hp hq
        obtain ⟨hca, hcb⟩ := Bool.or_eq_false_iff.mp hc
        simp only [Bool.or_eq_true] at hp hq
        have cross : ∀ p' q' : Fin N, p' ≠ q' →
            val C N l {p'} ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 0 0)
              = true →
            val C N l {q'} ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 1 0)
              = true →
            (Pi.single p' 1 - Pi.single q' 1 : Fin N → ℚ) ∈
              Submodule.span ℚ ((F.image (vec C N l) : Finset (Fin N → ℚ)) :
                Set (Fin N → ℚ)) := by
          intro p' q' hne hp' hq'
          have hkF : k ∈ F := by
            apply hF k (by omega) hg.1 hc0
            refine ⟨p', q', hne, ?_, ?_⟩
            · rw [hg.2, hp', Bool.true_or]
            · rw [hg.2, hq', Bool.or_true]
          have hex : ∃ pq : Fin N × Fin N, pq.1 ≠ pq.2 ∧
              val C N l {pq.1} ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 0 0)
                = true ∧
              val C N l {pq.2} ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs.getD 1 0)
                = true := ⟨(p', q'), hne, hp', hq'⟩
          have hv : vec C N l k = Pi.single (Classical.choose hex).1 1 -
              Pi.single (Classical.choose hex).2 1 := by
            unfold vec
            rw [dif_pos hex]
          obtain ⟨-, h0a, h0b⟩ := Classical.choose_spec hex
          have hmem : vec C N l k ∈
              Submodule.span ℚ ((F.image (vec C N l) : Finset (Fin N → ℚ)) :
                Set (Fin N → ℚ)) := by
            apply Submodule.subset_span
            simp only [Finset.coe_image]
            exact ⟨k, hkF, rfl⟩
          rw [hv] at hmem
          have e1 := ih _ ha hca p' (Classical.choose hex).1 hp' h0a
          have e2 := ih _ hb hcb (Classical.choose hex).2 q' h0b hq'
          have := Submodule.add_mem _ (Submodule.add_mem _ e1 hmem) e2
          convert this using 1
          abel
        rcases hp with hp | hp <;> rcases hq with hq | hq
        · exact ih _ ha hca p q hp hq
        · exact cross p q hpq hp hq
        · have := Submodule.neg_mem _ (cross q p (Ne.symm hpq) hq hp)
          rw [neg_sub] at this
          exact this
        · exact ih _ hb hcb p q hp hq
    · rw [val_ge _ _ _ _ _ (by omega)] at hp
      exact absurd hp (by simp)

theorem indep (N : ℕ) (S : Finset (Fin N)) (p0 : Fin N) :
    LinearIndependent ℚ (fun p : (S.erase p0) =>
      (Pi.single (p : Fin N) 1 - Pi.single p0 1 : Fin N → ℚ)) := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have h := congrFun hs (i : Fin N)
  have hne : (i : Fin N) ≠ p0 := Finset.ne_of_mem_erase i.2
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i] at h
  · simpa [Pi.single_apply, hne] using h
  · intro j _ hji
    have : (i : Fin N) ≠ (j : Fin N) := fun e => hji (Subtype.ext e.symm)
    simp [this, hne]
  · intro hn; exact absurd hi hn

end PEqualNP.Outside.L_meta_3256_aux

open PEqualNP.Outside.L_meta_3256_aux in
theorem PEqualNP.Outside.L_meta_3256 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             x3.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  intro N C S l hAO hout hacc hrej
  classical
  let F : Finset ℕ := (Finset.range C.size).filter (fun k =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      val C N l Sᶜ (N + N + k) = false ∧
      ∃ p q : Fin N, p ≠ q ∧ val C N l {p} (N + N + k) = true ∧ val C N l {q} (N + N + k) = true)
  have hF : ∀ k < C.size,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      val C N l Sᶜ (N + N + k) = false →
      (∃ p q : Fin N, p ≠ q ∧ val C N l {p} (N + N + k) = true ∧
        val C N l {q} (N + N + k) = true) → k ∈ F := by
    intro k hk h1 h2 h3
    simp only [F, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, h1, h2, h3⟩
  refine ⟨F, ?_, ?_⟩
  · rcases S.eq_empty_or_nonempty with hS | ⟨p0, hp0⟩
    · simp [hS]
    have hclean : val C N l Sᶜ C.output = false := hrej
    have hspan : ∀ p ∈ S, (Pi.single p 1 - Pi.single p0 1 : Fin N → ℚ) ∈
        Submodule.span ℚ ((F.image (vec C N l) : Finset (Fin N → ℚ)) :
          Set (Fin N → ℚ)) := by
      intro p hp
      exact span_inv C N l hAO S F hF C.output hclean p p0 (hacc p hp) (hacc p0 hp0)
    let W := Submodule.span ℚ ((F.image (vec C N l) : Finset (Fin N → ℚ)) : Set (Fin N → ℚ))
    let v : (S.erase p0) → W := fun p =>
      ⟨Pi.single (p : Fin N) 1 - Pi.single p0 1, hspan p (Finset.mem_of_mem_erase p.2)⟩
    have hli : LinearIndependent ℚ v :=
      LinearIndependent.of_comp W.subtype (indep N S p0)
    have h1 := hli.fintype_card_le_finrank
    have h2 := finrank_span_finset_le_card (R := ℚ) (F.image (vec C N l))
    have h3 := Finset.card_image_le (s := F) (f := vec C N l)
    have h4 := Finset.card_erase_of_mem hp0
    have h5 : 0 < S.card := Finset.card_pos.mpr ⟨p0, hp0⟩
    simp only [Fintype.card_coe] at h1
    have h6 : Module.finrank ℚ W ≤ (F.image (vec C N l)).card := h2
    omega
  · intro k hk
    have hk' := hk
    simp only [F, Finset.mem_filter, Finset.mem_range] at hk'
    obtain ⟨hks, hop, hcl, hex⟩ := hk'
    refine ⟨hks, hop, ?_⟩
    dsimp only
    refine ⟨hcl, hex, fun x13 hx => ?_⟩
    by_contra hn
    have hsub : ({x13} : Finset (Fin N)) ⊆ Sᶜ := by
      intro y hy
      rw [Finset.mem_singleton] at hy
      subst hy
      exact Finset.mem_compl.mpr hn
    have := mono C N l hAO {x13} Sᶜ hsub _ hx
    rw [hcl] at this
    exact absurd this (by simp)
