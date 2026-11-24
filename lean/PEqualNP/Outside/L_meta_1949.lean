import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1949_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

private abbrev Binary (C : Circuit) :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

private abbrev pointDegree (N : ℕ) (C : Circuit) (i : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.range N)).getD i 0

private abbrev lineDegreeAt (N : ℕ) (C : Circuit) (i : ℕ) : ℕ :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0

private abbrev Mixed (N : ℕ) (C : Circuit) (i : ℕ) :=
  0 < pointDegree N C i ∧ 0 < lineDegreeAt N C i

private abbrev KM (N : ℕ) (C : Circuit) :=
  ∀ j < C.gates.length, (gateAt C j).op = .and →
    (∃ i ∈ (gateAt C j).inputs, lineDegreeAt N C i = 0) ∨
    (∀ i ∈ (gateAt C j).inputs, pointDegree N C i = 0)

private abbrev ReadEdge (N : ℕ) (C : Circuit) (a b : ℕ) :=
  a < b ∧ ∃ f : Fin C.gates.length, b = N + N + f.val ∧ a ∈ (C.gates.get f).inputs

private abbrev Cone (N : ℕ) (C : Circuit) (j : ℕ) :=
  j < C.gates.length ∧ Mixed N C (N + N + j) ∧
    Relation.ReflTransGen (ReadEdge N C) (N + N + j) C.output

private def accumulate {α : Type} (d : α) (f : Gate → List α → α)
    (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun ws g => ws ++ [f g (g.inputs.map fun i => ws.getD i d)]) w

private theorem accumulate_old {α : Type} (d : α) (f : Gate → List α → α)
    (gs : List Gate) (w : List α) (i : ℕ) (hi : i < w.length) :
    (accumulate d f gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [accumulate, List.foldl_cons]
    change (accumulate d f gs (w ++ [_])).getD i d = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private theorem accumulate_gate {α : Type} (d : α) (f : Gate → List α → α)
    (gs : List Gate) (w : List α) (j : ℕ) (hj : j < gs.length)
    (back : ∀ i ∈ gs[j].inputs, i < w.length + j) :
    (accumulate d f gs w).getD (w.length + j) d =
      f gs[j] (gs[j].inputs.map fun i => (accumulate d f gs w).getD i d) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    let v := f g (g.inputs.map fun i => w.getD i d)
    let w' := w ++ [v]
    have hw : w'.length = w.length + 1 := by simp [w']
    cases j with
    | zero =>
      change (accumulate d f gs w').getD w.length d =
        f g (g.inputs.map fun i => (accumulate d f gs w').getD i d)
      rw [accumulate_old d f gs w' w.length (by omega)]
      have hv : w'.getD w.length d = v := by simp [w', List.getD_eq_getElem?_getD]
      rw [hv]
      unfold v
      congr 1
      apply List.map_congr_left
      intro i hi
      have hwi : i < w.length := back i hi
      rw [accumulate_old d f gs w' i (by omega)]
      exact (List.getD_append _ _ _ _ hwi).symm
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have hback : ∀ i ∈ gs[j].inputs, i < w'.length + j := by
        intro i hi
        have h := back i hi
        omega
      have h := ih w' j hj' hback
      have hindex : w'.length + j = w.length + (j + 1) := by omega
      rw [hindex] at h
      exact h

private theorem gateAt_elem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] :=
  List.getD_eq_getElem _ _ hj

private theorem gate_info {C : Circuit} (hC : Binary C) (j : ℕ) (hj : j < C.gates.length) :
    ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧
      (gateAt C j).inputs.length = 2 := by
  rw [gateAt_elem C j hj]
  exact hC _ (List.getElem_mem hj)

private theorem gate_pair {C : Circuit} (hC : Binary C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] := by
  have hl := (gate_info hC j hj).2
  generalize (gateAt C j).inputs = l at hl ⊢
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at hl
  · simp at hl
  · have ht : t = [] := by simpa using hl
    exact ⟨a, b, by rw [ht]⟩

private def degreeEval (g : Gate) (ds : List ℕ) : ℕ :=
  letI := lineDegreeGateOpDecEq
  if g.op = .and then ds.sum else ds.foldr max 0

private theorem degree_input (C : Circuit) (n : ℕ) (S : Finset ℕ) (i : ℕ) (hi : i < n) :
    (C.lineDegrees n S).getD i 0 = if i ∈ S then 1 else 0 := by
  let start := (List.range n).map fun k => if k ∈ S then 1 else 0
  change (accumulate 0 degreeEval C.gates start).getD i 0 = _
  have his : i < start.length := by simpa [start]
  rw [accumulate_old _ _ _ _ _ his, List.getD_eq_getElem _ _ his]
  simp [start]

private theorem degree_gate {C : Circuit} {n : ℕ} (back : ReadsBack n C)
    (S : Finset ℕ) (j : ℕ) (hj : j < C.gates.length) :
    (C.lineDegrees n S).getD (n + j) 0 =
      degreeEval (gateAt C j) ((gateAt C j).inputs.map fun i =>
        (C.lineDegrees n S).getD i 0) := by
  let start := (List.range n).map fun k => if k ∈ S then 1 else 0
  have hl : start.length = n := by simp [start]
  have hb : ∀ i ∈ C.gates[j].inputs, i < start.length + j := by
    rw [← gateAt_elem C j hj, hl]
    exact back j hj
  have h := accumulate_gate 0 degreeEval C.gates start j hj hb
  rw [hl, ← gateAt_elem C j hj] at h
  exact h

private theorem degree_positive {C : Circuit} {n : ℕ} (binary : Binary C) (back : ReadsBack n C)
    (S : Finset ℕ) (j : ℕ) (hj : j < C.gates.length) :
    0 < (C.lineDegrees n S).getD (n + j) 0 ↔
      ∃ i ∈ (gateAt C j).inputs, 0 < (C.lineDegrees n S).getD i 0 := by
  obtain ⟨a, b, hp⟩ := gate_pair binary j hj
  rcases (gate_info binary j hj).1 with ha | ho
  · rw [degree_gate back S j hj, hp]
    simp [degreeEval, ha]
  · have hn : (gateAt C j).op ≠ GateOp.and := by rw [ho]; intro he; cases he
    rw [degree_gate back S j hj, hp]
    simp [degreeEval, hn, lt_max_iff]

private def valueEval (g : Gate) (vs : List Bool) : Bool := g.op.eval vs

private abbrev pointInput (N : ℕ) : List Bool :=
  List.ofFn (Fin.append (fun _ : Fin N => true) (fun _ : Fin N => false))

private abbrev value (N : ℕ) (C : Circuit) (i : ℕ) : Bool :=
  (C.wires (pointInput N)).getD i false

private theorem eval_gate {N : ℕ} {C : Circuit} (back : ReadsBack (N + N) C)
    (j : ℕ) (hj : j < C.gates.length) :
    value N C (N + N + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (value N C)) := by
  have hb : ∀ i ∈ C.gates[j].inputs, i < (pointInput N).length + j := by
    rw [← gateAt_elem C j hj, List.length_ofFn]
    exact back j hj
  have h := accumulate_gate false valueEval C.gates (pointInput N) j hj hb
  rw [List.length_ofFn, ← gateAt_elem C j hj] at h
  exact h

private theorem eval_and {N : ℕ} {C : Circuit} (back : ReadsBack (N + N) C)
    {j : ℕ} (hj : j < C.gates.length) (ha : (gateAt C j).op = .and)
    (h : ∀ i ∈ (gateAt C j).inputs, value N C i = true) :
    value N C (N + N + j) = true := by
  rw [eval_gate back j hj, ha]
  simpa [GateOp.eval] using h

private theorem eval_or {N : ℕ} {C : Circuit} (back : ReadsBack (N + N) C)
    {j : ℕ} (hj : j < C.gates.length) (ho : (gateAt C j).op = .or)
    {i : ℕ} (hi : i ∈ (gateAt C j).inputs) (h : value N C i = true) :
    value N C (N + N + j) = true := by
  rw [eval_gate back j hj, ho]
  simpa [GateOp.eval] using
    (show ∃ a ∈ (gateAt C j).inputs, value N C a = true from ⟨i, hi, h⟩)

private theorem line_free_true {N : ℕ} {C : Circuit} (binary : Binary C)
    (back : ReadsBack (N + N) C) (w : ℕ)
    (bound : w < N + N + C.gates.length) (free : lineDegreeAt N C w = 0) :
    value N C w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < N + N
    · have hp : w < N := by
        by_contra hn
        have hm : w ∈ Finset.Ico N (N + N) := Finset.mem_Ico.mpr ⟨by omega, hw⟩
        change (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0 = 0 at free
        rw [degree_input C _ _ _ hw, ite_eq_left hm] at free
        omega
      change (accumulate false valueEval C.gates (pointInput N)).getD w false = true
      rw [accumulate_old _ _ _ _ _ (by simpa using hw)]
      simp only [pointInput, List.ofFn_fin_append, List.ofFn_const]
      have hrep : w < (List.replicate N true).length := by simpa using hp
      rw [List.getD_append _ _ _ _ hrep, List.getD_eq_getElem _ _ hrep]
      simp
    · let j := w - (N + N)
      have he : N + N + j = w := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      have earlier (i : ℕ) (hi : i ∈ (gateAt C j).inputs) : value N C i = true := by
        have hiw := back j hj i hi
        apply ih i (by omega) (by omega)
        by_contra hn
        have hpos := (degree_positive binary back (Finset.Ico N (N + N)) j hj).2
          ⟨i, hi, Nat.pos_of_ne_zero hn⟩
        change 0 < lineDegreeAt N C (N + N + j) at hpos
        rw [he, free] at hpos
        exact (Nat.lt_irrefl 0 hpos)
      rw [← he]
      rcases (gate_info binary j hj).1 with ha | ho
      · exact eval_and back hj ha earlier
      · obtain ⟨a, b, hab⟩ := gate_pair binary j hj
        have ha : a ∈ (gateAt C j).inputs := by simp [hab]
        exact eval_or back hj ho ha (earlier a ha)

private theorem and_line_free {N : ℕ} {C : Circuit} (binary : Binary C)
    (back : ReadsBack (N + N) C) (km : KM N C) {j : ℕ} (hj : j < C.gates.length)
    (hmix : Mixed N C (N + N + j)) (ha : (gateAt C j).op = .and) :
    ∃ i ∈ (gateAt C j).inputs, lineDegreeAt N C i = 0 := by
  rcases km j hj ha with hfree | hno
  · exact hfree
  · obtain ⟨i, hi, hp⟩ := (degree_positive binary back (Finset.range N) j hj).1 hmix.1
    exact False.elim ((Nat.ne_of_gt hp) (hno i hi))

private theorem mixed_from_read {N : ℕ} {C : Circuit} (binary : Binary C)
    (back : ReadsBack (N + N) C) {a j : ℕ} (hj : j < C.gates.length)
    (ha : a ∈ (gateAt C j).inputs) (hm : Mixed N C a) :
    Mixed N C (N + N + j) :=
  ⟨(degree_positive binary back (Finset.range N) j hj).2 ⟨a, ha, hm.1⟩,
    (degree_positive binary back (Finset.Ico N (N + N)) j hj).2 ⟨a, ha, hm.2⟩⟩

private theorem mixed_true_step {N : ℕ} {C : Circuit} (binary : Binary C)
    (back : ReadsBack (N + N) C) (km : KM N C) {a b : ℕ}
    (edge : ReadEdge N C a b) (hm : Mixed N C a) (ht : value N C a = true) :
    Mixed N C b ∧ value N C b = true := by
  obtain ⟨_, f, rfl, hf⟩ := edge
  have ha : a ∈ (gateAt C f.val).inputs := by
    rw [gateAt_elem C f.val f.isLt]
    exact hf
  have hmix := mixed_from_read binary back f.isLt ha hm
  refine ⟨hmix, ?_⟩
  rcases (gate_info binary f.val f.isLt).1 with hand | hor
  · obtain ⟨i, hi, hz⟩ := and_line_free binary back km f.isLt hmix hand
    have hia : i ≠ a := fun he => (Nat.ne_of_gt hm.2) (he ▸ hz)
    have hiv := line_free_true binary back i (by have := back f.val f.isLt i hi; omega) hz
    apply eval_and back f.isLt hand
    intro k hk
    obtain ⟨u, v, huv⟩ := gate_pair binary f.val f.isLt
    rw [huv] at hi ha hk
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi ha hk
    rcases hi with rfl | rfl <;> rcases ha with rfl | rfl <;>
      rcases hk with rfl | rfl <;> first | contradiction | exact ht | exact hiv
  · exact eval_or back f.isLt hor ha ht

private theorem or_no_line_free {N : ℕ} {C : Circuit} (binary : Binary C)
    (back : ReadsBack (N + N) C) (km : KM N C) (out : value N C C.output = false)
    {j : ℕ} (hc : Cone N C j) (ho : (gateAt C j).op = .or)
    (i : ℕ) (hi : i ∈ (gateAt C j).inputs) : 0 < lineDegreeAt N C i := by
  by_contra hn
  have hz : lineDegreeAt N C i = 0 := by omega
  have hiv := line_free_true binary back i (by have := back j hc.1 i hi; omega) hz
  have hjv := eval_or back hc.1 ho hi hiv
  have htrav {a b : ℕ} (path : Relation.ReflTransGen (ReadEdge N C) a b)
      (h : Mixed N C a ∧ value N C a = true) : Mixed N C b ∧ value N C b = true := by
    induction path with
    | refl => exact h
    | tail _ edge ih => exact mixed_true_step binary back km edge ih.1 ih.2
  have ht := (htrav hc.2.2 ⟨hc.2.1, hjv⟩).2
  rw [out] at ht
  contradiction

private theorem valid_wire_support {N : ℕ} {C : Circuit} (binary : Binary C)
    (back : ReadsBack (N + N) C) (w : ℕ) (bound : w < N + N + C.gates.length) :
    0 < pointDegree N C w ∨ 0 < lineDegreeAt N C w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < N + N
    · by_cases hp : w < N
      · left
        change 0 < (C.lineDegrees (N + N) (Finset.range N)).getD w 0
        rw [degree_input C _ _ _ hw, ite_eq_left (Finset.mem_range.mpr hp)]
        decide
      · right
        change 0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0
        rw [degree_input C _ _ _ hw, ite_eq_left (Finset.mem_Ico.mpr ⟨by omega, hw⟩)]
        decide
    · let j := w - (N + N)
      have he : N + N + j = w := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      obtain ⟨a, b, hab⟩ := gate_pair binary j hj
      have ha : a ∈ (gateAt C j).inputs := by simp [hab]
      have haw := back j hj a ha
      rcases ih a (by omega) (by omega) with hp | hl
      · left
        rw [← he]
        exact (degree_positive binary back (Finset.range N) j hj).2 ⟨a, ha, hp⟩
      · right
        rw [← he]
        exact (degree_positive binary back (Finset.Ico N (N + N)) j hj).2 ⟨a, ha, hl⟩

private abbrev slotWire (C : Circuit) (p : ℕ × ℕ) : ℕ :=
  (gateAt C p.1).inputs.getD p.2 0

private theorem slot_mem {C : Circuit} (binary : Binary C) {j k : ℕ}
    (hj : j < C.gates.length) (hk : k < 2) :
    slotWire C (j, k) ∈ (gateAt C j).inputs := by
  have hl : k < (gateAt C j).inputs.length := by
    rwa [(gate_info binary j hj).2]
  change (gateAt C j).inputs.getD k 0 ∈ (gateAt C j).inputs
  rw [List.getD_eq_getElem _ _ hl]
  exact List.getElem_mem hl

private theorem unique_free_slot {N : ℕ} {C : Circuit} (binary : Binary C)
    (back : ReadsBack (N + N) C) (km : KM N C) {j : ℕ}
    (hc : Cone N C j) (ha : (gateAt C j).op = .and) :
    ∃! k : ℕ, k < 2 ∧ lineDegreeAt N C (slotWire C (j, k)) = 0 := by
  obtain ⟨a, b, hab⟩ := gate_pair binary j hc.1
  have free : lineDegreeAt N C a = 0 ∨ lineDegreeAt N C b = 0 := by
    simpa [hab] using and_line_free binary back km hc.1 hc.2.1 ha
  have pos : 0 < lineDegreeAt N C a ∨ 0 < lineDegreeAt N C b := by
    simpa [hab] using
      (degree_positive binary back (Finset.Ico N (N + N)) j hc.1).1 hc.2.1.2
  have h0 : slotWire C (j, 0) = a := by simp [slotWire, hab]
  have h1 : slotWire C (j, 1) = b := by simp [slotWire, hab]
  rcases free with ha0 | hb0
  · refine ⟨0, ⟨by decide, h0.symm ▸ ha0⟩, ?_⟩
    intro k hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · rfl
    · have hz := hk.2
      rw [h1] at hz
      omega
  · refine ⟨1, ⟨by decide, h1.symm ▸ hb0⟩, ?_⟩
    intro k hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · have hz := hk.2
      rw [h0] at hz
      omega
    · rfl

private abbrev ConeSet (N : ℕ) (C : Circuit) : Set ℕ :=
  {j | Cone N C j}

private abbrev OrSet (N : ℕ) (C : Circuit) : Set ℕ :=
  {j | Cone N C j ∧ (gateAt C j).op = .or}

private abbrev AndSet (N : ℕ) (C : Circuit) : Set ℕ :=
  {j | Cone N C j ∧ (gateAt C j).op = .and}

private abbrev SlotSet (N : ℕ) (C : Circuit) : Set (ℕ × ℕ) :=
  {p | Cone N C p.1 ∧ p.2 < 2}

private abbrev MixedSlots (N : ℕ) (C : Circuit) : Set (ℕ × ℕ) :=
  {p | Cone N C p.1 ∧ p.2 < 2 ∧ Mixed N C (slotWire C p)}

private abbrev LineOnlySlots (N : ℕ) (C : Circuit) : Set (ℕ × ℕ) :=
  {p | Cone N C p.1 ∧ p.2 < 2 ∧ pointDegree N C (slotWire C p) = 0}

private abbrev LineFreeSlots (N : ℕ) (C : Circuit) : Set (ℕ × ℕ) :=
  {p | Cone N C p.1 ∧ p.2 < 2 ∧ lineDegreeAt N C (slotWire C p) = 0}

private theorem cone_finite (N : ℕ) (C : Circuit) : (ConeSet N C).Finite :=
  (Set.finite_lt_nat C.gates.length).subset fun _ hj => hj.1

private theorem slots_finite (N : ℕ) (C : Circuit) : (SlotSet N C).Finite :=
  (cone_finite N C).prod (Set.finite_lt_nat 2)

private theorem free_is_and {N : ℕ} {C : Circuit} (binary : Binary C)
    (noFree : ∀ j, Cone N C j → (gateAt C j).op = .or →
      ∀ i ∈ (gateAt C j).inputs, 0 < lineDegreeAt N C i)
    {p : ℕ × ℕ} (hp : p ∈ LineFreeSlots N C) : p.1 ∈ AndSet N C := by
  refine ⟨hp.1, ?_⟩
  rcases (gate_info binary p.1 hp.1.1).1 with ha | ho
  · exact ha
  · exact False.elim ((Nat.ne_of_gt (noFree p.1 hp.1 ho _ (slot_mem binary hp.1.1 hp.2.1))) hp.2.2)

private theorem card_free_slots {N : ℕ} {C : Circuit} (binary : Binary C)
    (back : ReadsBack (N + N) C) (km : KM N C)
    (noFree : ∀ j, Cone N C j → (gateAt C j).op = .or →
      ∀ i ∈ (gateAt C j).inputs, 0 < lineDegreeAt N C i) :
    (LineFreeSlots N C).ncard = (AndSet N C).ncard := by
  apply Set.BijOn.ncard_eq (f := Prod.fst)
  refine ⟨fun _ hp => free_is_and binary noFree hp, ?_, ?_⟩
  · rintro ⟨j, k⟩ hk ⟨j', k'⟩ hk' he
    change j = j' at he
    subst j'
    obtain ⟨l, _, hl⟩ :=
      unique_free_slot binary back km hk.1 (free_is_and binary noFree hk).2
    have hkk' := (hl k hk.2).trans (hl k' hk'.2).symm
    exact Prod.ext rfl hkk'
  · intro j hj
    obtain ⟨k, hk, _⟩ := unique_free_slot binary back km hj.1 hj.2
    exact ⟨(j, k), ⟨hj.1, hk⟩, rfl⟩

private theorem card_slots {N : ℕ} {C : Circuit} (binary : Binary C)
    (back : ReadsBack (N + N) C) (km : KM N C)
    (noFree : ∀ j, Cone N C j → (gateAt C j).op = .or →
      ∀ i ∈ (gateAt C j).inputs, 0 < lineDegreeAt N C i) :
    (OrSet N C).ncard + (ConeSet N C).ncard =
      (LineOnlySlots N C).ncard + (MixedSlots N C).ncard := by
  have andFin : (AndSet N C).Finite :=
    (cone_finite N C).subset fun _ hj => hj.1
  have orFin : (OrSet N C).Finite :=
    (cone_finite N C).subset fun _ hj => hj.1
  have gatesPart : AndSet N C ∪ OrSet N C = ConeSet N C := by
    ext j
    constructor
    · rintro (ha | ho)
      · exact ha.1
      · exact ho.1
    · intro hj
      rcases (gate_info binary j hj.1).1 with ha | ho
      · exact Or.inl ⟨hj, ha⟩
      · exact Or.inr ⟨hj, ho⟩
  have gatesDisj : Disjoint (AndSet N C) (OrSet N C) := Set.disjoint_left.mpr (by
    intro j ha ho
    have he := ha.2.symm.trans ho.2
    cases he)
  have gatesCount := Set.ncard_union_eq gatesDisj andFin orFin
  rw [gatesPart] at gatesCount
  let slots := SlotSet N C
  let F := LineFreeSlots N C
  let L := LineOnlySlots N C
  let M := MixedSlots N C
  have fFin : F.Finite := (slots_finite N C).subset fun _ hp => ⟨hp.1, hp.2.1⟩
  have lFin : L.Finite := (slots_finite N C).subset fun _ hp => ⟨hp.1, hp.2.1⟩
  have mFin : M.Finite := (slots_finite N C).subset fun _ hp => ⟨hp.1, hp.2.1⟩
  have hasSupport {p : ℕ × ℕ} (hp : p ∈ slots) :
      0 < pointDegree N C (slotWire C p) ∨ 0 < lineDegreeAt N C (slotWire C p) :=
    valid_wire_support binary back _ (by
      have h := back p.1 hp.1.1 _ (slot_mem binary hp.1.1 hp.2)
      change slotWire C p < N + N + p.1 at h
      have h' := hp.1.1
      omega)
  have positionPart : F ∪ (L ∪ M) = slots := by
    ext p
    constructor
    · rintro (hp | hp | hp) <;> exact ⟨hp.1, hp.2.1⟩
    · intro hp
      by_cases hl : lineDegreeAt N C (slotWire C p) = 0
      · exact Or.inl ⟨hp.1, hp.2, hl⟩
      · by_cases hpt : pointDegree N C (slotWire C p) = 0
        · exact Or.inr (Or.inl ⟨hp.1, hp.2, hpt⟩)
        · exact Or.inr (Or.inr ⟨hp.1, hp.2, Nat.pos_of_ne_zero hpt, Nat.pos_of_ne_zero hl⟩)
  have lDisj : Disjoint L M := Set.disjoint_left.mpr (by
    intro p hp hm
    exact (Nat.ne_of_gt hm.2.2.1) hp.2.2)
  have fDisj : Disjoint F (L ∪ M) := Set.disjoint_left.mpr (by
    intro p hf h
    rcases h with hl | hm
    · rcases hasSupport ⟨hf.1, hf.2.1⟩ with hpt | hln
      · exact (Nat.ne_of_gt hpt) hl.2.2
      · exact (Nat.ne_of_gt hln) hf.2.2
    · exact (Nat.ne_of_gt hm.2.2.2) hf.2.2)
  have positionsCount := Set.ncard_union_eq fDisj fFin (lFin.union mFin)
  rw [positionPart, Set.ncard_union_eq lDisj lFin mFin] at positionsCount
  have two : ({k : ℕ | k < 2} : Set ℕ).ncard = 2 := by
    rw [show ({k : ℕ | k < 2} : Set ℕ) = ↑(Finset.range 2) by ext k; simp,
      Set.ncard_coe_finset, Finset.card_range]
  have allCount : slots.ncard = (ConeSet N C).ncard * 2 := by
    change (ConeSet N C ×ˢ {k : ℕ | k < 2}).ncard = _
    rw [Set.ncard_prod, two]
  have freeCount : F.ncard = (AndSet N C).ncard := card_free_slots binary back km noFree
  change (OrSet N C).ncard + (ConeSet N C).ncard = L.ncard + M.ncard
  omega

private theorem count_cone_from_reads {N : ℕ} {C : Circuit} (binary : Binary C)
    (back : ReadsBack (N + N) C) :
    (ConeSet N C).ncard ≤ (MixedSlots N C).ncard + 1 := by
  classical
  let others : Set ℕ := {j | Cone N C j ∧ N + N + j ≠ C.output}
  let slots := MixedSlots N C
  have slotFin : slots.Finite := (slots_finite N C).subset fun _ hp => ⟨hp.1, hp.2.1⟩
  have otherFin : others.Finite := (cone_finite N C).subset fun _ hj => hj.1
  have hasReader (j : ℕ) (hj : j ∈ others) :
      ∃ p : ℕ × ℕ, p ∈ slots ∧ slotWire C p = N + N + j := by
    rcases hj.1.2.2.cases_head with he | ⟨b, hedge, hpath⟩
    · exact False.elim (hj.2 he)
    · obtain ⟨_, f, rfl, hf⟩ := hedge
      have ha : N + N + j ∈ (gateAt C f.val).inputs := by
        rw [gateAt_elem C f.val f.isLt]
        exact hf
      have hcone : Cone N C f.val := ⟨f.isLt,
        mixed_from_read binary back f.isLt ha hj.1.2.1, hpath⟩
      obtain ⟨k, hk, hread⟩ := List.mem_iff_getElem.mp ha
      have hk' : k < 2 := by simpa only [(gate_info binary f.val f.isLt).2] using hk
      have hwire : slotWire C (f.val, k) = N + N + j := by
        change (gateAt C f.val).inputs.getD k 0 = _
        exact (List.getD_eq_getElem _ _ hk).trans hread
      refine ⟨(f.val, k), ⟨hcone, hk', ?_⟩, hwire⟩
      rw [hwire]
      exact hj.1.2.1
  let pick (j : ℕ) : ℕ × ℕ :=
    if hj : j ∈ others then Classical.choose (hasReader j hj) else (0, 0)
  have pickSpec (j : ℕ) (hj : j ∈ others) :
      pick j ∈ slots ∧ slotWire C (pick j) = N + N + j := by
    simpa only [pick, dite_eq_left hj] using Classical.choose_spec (hasReader j hj)
  have hle : others.ncard ≤ slots.ncard := by
    apply Set.ncard_le_ncard_of_injOn pick (fun j hj => (pickSpec j hj).1) _ slotFin
    intro a ha b hb hab
    have he := (pickSpec a ha).2.symm.trans ((congrArg (slotWire C) hab).trans (pickSpec b hb).2)
    omega
  let outIndex := C.output - (N + N)
  have hsubset : ConeSet N C ⊆ insert outIndex others := by
    intro j hj
    by_cases he : N + N + j = C.output
    · apply Set.mem_insert_iff.mpr
      exact Or.inl (by dsimp [outIndex]; omega)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨hj, he⟩)
  exact (Set.ncard_le_ncard hsubset (otherFin.insert _)).trans
    ((Set.ncard_insert_le outIndex others).trans (Nat.add_le_add_right hle 1))

theorem main (N : ℕ) (C : Circuit) (binary : Binary C)
    (back : ReadsBack (N + N) C) (km : KM N C) (out : value N C C.output = false) :
    (∀ j, Cone N C j → (gateAt C j).op = .or →
      ∀ i ∈ (gateAt C j).inputs, 0 < lineDegreeAt N C i) ∧
    (OrSet N C).ncard + (ConeSet N C).ncard =
      (LineOnlySlots N C).ncard + (MixedSlots N C).ncard ∧
    (ConeSet N C).ncard ≤ (MixedSlots N C).ncard + 1 := by
  have hor := fun j hc => or_no_line_free binary back km out (j := j) hc
  exact ⟨hor, card_slots binary back km hor, count_cone_from_reads binary back⟩

end PEqualNP.Outside.L_meta_1949_aux

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.L_meta_1949 : (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → ∀ (N230 : ℕ) (C230 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g230 ∈ C230.gates, (g230.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g230.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g230.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N230 + N230) C230) → (∀ j230x2 < C230.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i230x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x2 0 = 0) ∨ (∀ h230 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x2).inputs, (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD h230 0 = 0)) → PEqualNP.MetaComplexity.circuitFun (N230 + N230) C230 (Fin.append (fun u230 : Fin N230 => true) (fun u230x1 : Fin N230 => false)) = false → ∀ mixed230 : ℕ → Prop, mixed230 = (fun i230 : ℕ => 0 < (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD i230 0 ∧ 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230 0) → ∀ cone230 : ℕ → Prop, cone230 = (fun j230 : ℕ => j230 < C230.gates.length ∧ mixed230 (N230 + N230 + j230) ∧ Relation.ReflTransGen (fun a230 b230 : ℕ => a230 < b230 ∧ ∃ f230 : Fin C230.gates.length, b230 = N230 + N230 + f230.val ∧ a230 ∈ (C230.gates.get f230).inputs) (N230 + N230 + j230) C230.output) → (∀ j230x1 : ℕ, cone230 j230x1 → (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ i230x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x1).inputs, 0 < (C230.lineDegrees (N230 + N230) (Finset.Ico N230 (N230 + N230))).getD i230x1 0) ∧ Set.ncard {j230x3 : ℕ | cone230 j230x3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C230 j230x3).op = PEqualNP.CircuitLowerBounds.GateOp.or} + Set.ncard {j230x4 : ℕ | cone230 j230x4} = Set.ncard {js230 : ℕ × ℕ | cone230 js230.1 ∧ js230.2 < 2 ∧ (C230.lineDegrees (N230 + N230) (Finset.range N230)).getD ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230.1).inputs.getD js230.2 0) 0 = 0} + Set.ncard {js230x1 : ℕ × ℕ | cone230 js230x1.1 ∧ js230x1.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230x1.1).inputs.getD js230x1.2 0)} ∧ Set.ncard {j230x5 : ℕ | cone230 j230x5} ≤ Set.ncard {js230x2 : ℕ × ℕ | cone230 js230x2.1 ∧ js230x2.2 < 2 ∧ mixed230 ((PEqualNP.MetaComplexity.NestedCover.gateAt C230 js230x2.1).inputs.getD js230x2.2 0)} + 1 := by
  rintro _ N C ⟨binary, back⟩ km out mixed rfl cone rfl
  exact PEqualNP.Outside.L_meta_1949_aux.main N C binary back km out
