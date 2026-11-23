import Mathlib
import PEqualNP.Defs

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

-- Endpoint and encoding bounds follow the argument in L-meta-479.

private theorem memVars {φ : CNF} {x : ℕ} :
    x ∈ vars φ ↔ ∃ c ∈ φ, ∃ l ∈ c, l.1 = x := by
  simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]

private theorem clauseAtIndex {φ : CNF} {i : ℕ} (h : 0 < (clauseAt φ i).length) :
    i < φ.length := by
  by_contra! hi
  rw [clauseAt, List.getD_eq_default _ _ hi] at h
  simp at h

private theorem adjacentEndpoint {φ : CNF} {u v : Vertex}
    (h : (satGraph φ).Adj u v) :
    match u with
    | .inl l => l.1 ∈ vars φ
    | .inr (i, j) => i < φ.length ∧ j < (clauseAt φ i).length := by
  change satAdj φ u v at h
  cases u with
  | inl l =>
      cases v with
      | inl l' => exact h.2.2
      | inr ij =>
          obtain ⟨i, j⟩ := ij
          change (clauseAt φ i)[j]? = some l at h
          obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp h
          have hi := clauseAtIndex (Nat.zero_lt_of_lt hj)
          have hc : clauseAt φ i ∈ φ := by
            rw [clauseAt, List.getD_eq_getElem _ _ hi]
            exact List.getElem_mem hi
          exact memVars.mpr ⟨_, hc, l, List.mem_of_getElem? h, rfl⟩
  | inr ij =>
      obtain ⟨i, j⟩ := ij
      cases v with
      | inl l =>
          change (clauseAt φ i)[j]? = some l at h
          obtain ⟨hj, _⟩ := List.getElem?_eq_some_iff.mp h
          exact ⟨clauseAtIndex (Nat.zero_lt_of_lt hj), hj⟩
      | inr kl =>
          obtain ⟨k, l⟩ := kl
          exact ⟨clauseAtIndex (Nat.zero_lt_of_lt h.2.2.1), h.2.2.1⟩

private theorem cvcVar {φ : CNF} {x : ℕ} (h : x ∈ vars (cvcFormula φ)) :
    x ∈ vars φ ∨ x = fresh φ := by
  obtain ⟨c, hc, l, hl, hxl⟩ := memVars.mp h
  simp only [cvcFormula, List.mem_append, List.mem_map, List.mem_singleton] at hc
  rcases hc with ⟨c', hc', rfl⟩ | rfl
  · simp only [List.mem_append, List.mem_singleton] at hl
    rcases hl with hl | rfl
    · exact Or.inl (memVars.mpr ⟨c', hc', l, hl, hxl⟩)
    · exact Or.inr hxl.symm
  · simp only [List.mem_singleton] at hl
    subst l
    exact Or.inr hxl.symm

private theorem cvcPosition {φ : CNF} {i j : ℕ}
    (hi : i < (cvcFormula φ).length) (hj : j < (clauseAt (cvcFormula φ) i).length) :
    (i < φ.length ∧ j ≤ (φ.getD i []).length) ∨ (i = φ.length ∧ j = 0) := by
  by_cases h : i < φ.length
  · left
    refine ⟨h, ?_⟩
    have hm : i < (φ.map (fun c => c ++ [(fresh φ, true)])).length := by simpa using h
    rw [clauseAt, cvcFormula, List.getD_append _ _ _ _ hm,
      List.getD_eq_getElem _ _ hm, List.getElem_map] at hj
    rw [List.getD_eq_getElem _ _ h]
    simp at hj
    omega
  · have he : i = φ.length := by
      simp [cvcFormula] at hi
      omega
    subst i
    have ha : (φ.map (fun c => c ++ [(fresh φ, true)])).length ≤ φ.length := by simp
    rw [clauseAt, cvcFormula, List.getD_append_right _ _ _ _ ha] at hj
    simp at hj
    omega

private theorem encodeClauseLength (c : Clause) :
    c.length + 1 ≤ (encodeClause c).length := by
  have h : c.length ≤ (c.flatMap encodeLiteral).length := by
    induction c with
    | nil => simp
    | cons l ls ih =>
        have hl : 1 ≤ (encodeLiteral l).length := by simp [encodeLiteral]
        simp only [List.length_cons, List.flatMap_cons, List.length_append]
        omega
  simp only [encodeClause, List.length_append, List.length_cons, List.length_nil]
  omega

private theorem encodeCnfLength (φ : CNF) :
    (φ.map (fun c => c.length + 1)).sum ≤ (encodeCNF φ).length := by
  induction φ with
  | nil => simp [encodeCNF]
  | cons c cs ih =>
      simpa only [encodeCNF, List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
        using Nat.add_le_add (encodeClauseLength c) ih

theorem PEqualNP.Outside.L_meta_478 : ∀ (φ : PEqualNP.Search.CNF) (E : ℕ)
    (off : ℕ → ℕ) (e : ℕ → ℕ), E = (PEqualNP.Search.encodeCNF φ).length →
    (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) →
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) →
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
      ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') →
    ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ,
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool,
      num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) →
    (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) =
      2 * E + (if b then 1 else 0)) →
    (∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) →
    num (Sum.inr (φ.length, 0)) = 3 * E + 2 →
    ∀ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex,
      (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v → num u < (3 * (E + 1)) := by
  intro φ E off e hE hoff he _ num hOld hFresh hClause hLast u v huv
  have hu := adjacentEndpoint (φ := cvcFormula φ) huv
  rcases u with ⟨x, b⟩ | ⟨i, j⟩
  · rcases cvcVar hu with hx | rfl
    · have hxBound := he x hx
      rw [hOld x hx]
      cases b <;> simp <;> omega
    · rw [hFresh]
      cases b <;> simp <;> omega
  · rcases cvcPosition hu.1 hu.2 with ⟨hi, hj⟩ | ⟨rfl, rfl⟩
    · have next : off (i + 1) = off i + ((φ.getD i []).length + 1) := by
        simp only [hoff, List.map_take]
        have hm : i < (φ.map (fun c => c.length + 1)).length := by simpa using hi
        rw [List.sum_take_succ _ _ hm, List.getElem_map, List.getD_eq_getElem _ _ hi]
      have prefixBound : off (i + 1) ≤ off φ.length := by
        simpa only [hoff, List.map_take] using
          List.monotone_sum_take (φ.map (fun c => c.length + 1)) (Nat.succ_le_of_lt hi)
      have totalBound : off φ.length ≤ E := by
        rw [hoff, List.take_length, hE]
        exact encodeCnfLength φ
      rw [hClause i j hi hj]
      omega
    · rw [hLast]
      omega
