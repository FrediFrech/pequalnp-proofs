import Mathlib
import PEqualNP.Defs

-- A reduction for L-meta-3020. The two hypotheses are the baseline 16-gate lower
-- bounds for nine-input circuits computing the edge function of the Petersen graph
-- minus a vertex, split into the monotone case and the case with a NOT gate.
-- Any circuit for the posted step, together with the two free gates OR(x0,x2) and
-- the posted AND gate, would be a fifteen-gate circuit of that baseline shape.
theorem PEqualNP.Outside.R_meta_3020_1 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ y : Fin (9 : ℕ) → Bool, C.eval (List.ofFn y) = (fun x : Fin (9 : ℕ) → Bool => (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) y) →
      16 ≤ C.size) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ y : Fin (9 : ℕ) → Bool, C.eval (List.ofFn y) = (fun x : Fin (9 : ℕ) → Bool => (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) y) →
      16 ≤ C.size) →
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro hM hN x1 hx1 x3 hC hsize
  by_contra hno
  push_neg at hno
  simp only [ne_eq, not_not] at hno
  let F : (Fin (9 : ℕ) → Bool) → Bool := fun x =>
    (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))
  let gOr : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩
  let gA : PEqualNP.CircuitLowerBounds.Gate :=
    if h : (10 : Fin (11 : ℕ)) ∈ x1 then
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
    else
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, x1.map (fun i : Fin (11 : ℕ) => (i : ℕ))⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨gOr :: gA :: x3.gates, x3.output⟩
  have hDfan : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    simp only [D, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · constructor <;> simp [gOr]
    · constructor
      · by_cases h10 : (10 : Fin (11 : ℕ)) ∈ x1 <;> simp [gA, h10]
      · by_cases h10 : (10 : Fin (11 : ℕ)) ∈ x1
        · simp [gA, h10]
        · simpa [gA, h10, List.length_map] using hx1
    · exact hC g hg
  have hDsize : D.size ≤ 15 := by
    simp [D, PEqualNP.CircuitLowerBounds.Circuit.size] at hsize ⊢
    omega
  have hb : ∀ x : Fin (9 : ℕ) → Bool,
      gOr.op.eval (gOr.inputs.map (fun i => (List.ofFn x).getD i false)) = (x (0 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ))) := by
    intro x
    simp [gOr, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have ha : ∀ x : Fin (9 : ℕ) → Bool,
      gA.op.eval (gA.inputs.map (fun i => (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ))]).getD i false)) =
      PEqualNP.CircuitLowerBounds.GateOp.and.eval
        (List.map (fun x8 : Fin (11 : ℕ) => (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ))]).getD (↑x8) Bool.false) x1) := by
    intro x
    by_cases h10 : (10 : Fin (11 : ℕ)) ∈ x1
    · have hfalse : PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (List.map (fun x8 : Fin (11 : ℕ) => (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ))]).getD (↑x8) Bool.false) x1) = false := by
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval]
        have hmem : false ∈ List.map (fun x8 : Fin (11 : ℕ) => (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ))]).getD (↑x8) Bool.false) x1 := by
          apply List.mem_map_of_mem h10
        cases hcase : (List.map (fun x8 : Fin (11 : ℕ) => (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ))]).getD (↑x8) Bool.false) x1).all id with
        | false => rfl
        | true =>
          have := (List.all_eq_true.mp hcase) false hmem
          exact False.elim (Bool.false_ne_true this)
      rw [hfalse]
      simp [gA, h10, PEqualNP.CircuitLowerBounds.GateOp.eval]
    · simp [gA, h10, PEqualNP.CircuitLowerBounds.GateOp.eval, Function.comp_def]
  have hwires : ∀ x : Fin (9 : ℕ) → Bool,
      D.wires (List.ofFn x) =
        x3.wires (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)),
          PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun x8 : Fin (11 : ℕ) => (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ))]).getD (↑x8) Bool.false) x1)]) := by
    intro x
    simp only [D, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons]
    rw [hb x]
    rw [ha x]
    simp
  have hDeval : ∀ x : Fin (9 : ℕ) → Bool, D.eval (List.ofFn x) = F x := by
    intro x
    have h1 : D.eval (List.ofFn x) =
        x3.eval (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)),
          PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun x8 : Fin (11 : ℕ) => (List.ofFn x ++ [x (0 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ))]).getD (↑x8) Bool.false) x1)]) := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
      rw [hwires x]
    rw [h1]
    simpa [F] using hno x
  have hDeval' : ∀ y : Fin (9 : ℕ) → Bool, D.eval (List.ofFn y) =
      (fun x : Fin (9 : ℕ) → Bool => (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) y := by
    intro y
    simpa [F] using hDeval y
  have h16 : 16 ≤ D.size := by
    by_cases hnot : ∃ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
    · exact hN D hDfan hnot hDeval'
    · apply hM D hDfan
      · intro g hg hge
        exact hnot ⟨g, hg, hge⟩
      · exact hDeval'
  have hsizeD : D.size = x3.size + 2 := by
    simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  omega
