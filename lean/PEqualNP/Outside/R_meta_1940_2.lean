import Mathlib
import PEqualNP.Defs

-- A reduction for L-meta-1940. The two hypotheses are the baseline 16-gate lower
-- bounds for nine-input circuits computing the edge function of the Petersen graph
-- minus a vertex, split into the monotone case and the case with a NOT gate.
-- Any circuit for the posted step, together with the free NOT x0 and the posted
-- NOT gate, would be a fifteen-gate circuit of that baseline shape.
theorem PEqualNP.Outside.R_meta_1940_2 :
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
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro _hM hN x1 hx1 x3 hC hsize
  by_contra hno
  push_neg at hno
  simp only [ne_eq, not_not] at hno
  let F : (Fin (9 : ℕ) → Bool) → Bool := fun x =>
    (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))
  let gNot0 : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩
  let gSecond : PEqualNP.CircuitLowerBounds.Gate :=
    if x1.head?.getD (10 : ℕ) ≤ 8 then
      ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [x1.head?.getD (10 : ℕ)]⟩
    else if x1.head?.getD (10 : ℕ) = 9 then
      ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩
    else
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨gNot0 :: gSecond :: x3.gates, x3.output⟩
  have hDfan : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    simp only [D, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · constructor <;> simp [gNot0]
    · constructor
      · by_cases h1 : x1.head?.getD (10 : ℕ) ≤ 8 <;> by_cases h2 : x1.head?.getD (10 : ℕ) = 9 <;> simp [gSecond, h1, h2]
      · by_cases h1 : x1.head?.getD (10 : ℕ) ≤ 8 <;> by_cases h2 : x1.head?.getD (10 : ℕ) = 9 <;> simp [gSecond, h1, h2]
    · exact hC g hg
  have hDsize : D.size ≤ 15 := by
    simp [D, PEqualNP.CircuitLowerBounds.Circuit.size] at hsize ⊢
    omega
  have hb : ∀ x : Fin (9 : ℕ) → Bool,
      gNot0.op.eval (gNot0.inputs.map (fun i => (List.ofFn x).getD i false)) = !(x (0 : Fin (9 : ℕ))) := by
    intro x
    simp [gNot0, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have ha : ∀ x : Fin (9 : ℕ) → Bool,
      gSecond.op.eval (gSecond.inputs.map (fun i => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD i false)) =
      PEqualNP.CircuitLowerBounds.GateOp.not.eval
        (List.map (fun x8 : ℕ => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD x8 Bool.false) x1) := by
    intro x
    rcases x1 with _ | ⟨a, rest⟩
    · simp [gSecond, PEqualNP.CircuitLowerBounds.GateOp.eval]
    · by_cases h1 : a ≤ 8
      · simp [gSecond, h1, PEqualNP.CircuitLowerBounds.GateOp.eval]
      · by_cases h2 : a = 9
        · simp [gSecond, h1, h2, PEqualNP.CircuitLowerBounds.GateOp.eval]
        · have hge : ¬ a < 10 := by omega
          have hlen : (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).length = 10 := by simp
          simp [gSecond, h1, h2, PEqualNP.CircuitLowerBounds.GateOp.eval,
            List.getD_eq_getElem?_getD, hlen, hge]
  have hwires : ∀ x : Fin (9 : ℕ) → Bool,
      D.wires (List.ofFn x) =
        x3.wires (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)),
          PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun x8 : ℕ => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD x8 Bool.false) x1)]) := by
    intro x
    simp only [D, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons]
    rw [hb x]
    rw [ha x]
    simp
  have hDeval : ∀ x : Fin (9 : ℕ) → Bool, D.eval (List.ofFn x) = F x := by
    intro x
    have h1 : D.eval (List.ofFn x) =
        x3.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)),
          PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun x8 : ℕ => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD x8 Bool.false) x1)]) := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
      rw [hwires x]
    rw [h1]
    simpa [F] using hno x
  have hDeval' : ∀ y : Fin (9 : ℕ) → Bool, D.eval (List.ofFn y) =
      (fun x : Fin (9 : ℕ) → Bool => (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))) y := by
    intro y
    simpa [F] using hDeval y
  have h16 : 16 ≤ D.size :=
    hN D hDfan ⟨gNot0, by simp [D], by simp [gNot0]⟩ hDeval'
  have hsizeD : D.size = x3.size + 2 := by
    simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  omega
