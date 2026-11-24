import Mathlib
import PEqualNP.Defs

-- A reduction for L-meta-3174. The two hypotheses are the baseline 16-gate lower
-- bounds for nine-input circuits computing the edge function of the Petersen graph
-- minus a vertex, split into the monotone case and the case with a NOT gate.
-- Any circuit for the posted step, together with the free NOT x0 and the posted
-- OR gate on two inputs, would be a fifteen-gate circuit of that baseline shape.
theorem PEqualNP.Outside.R_meta_3174_1 :
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
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ((¬∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) ∧ ¬∀ x4 ∈ x1, x4 = (2 : ℕ) ∨ x4 = (3 : ℕ) ∨ x4 = (8 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro _hM hN x1 hx1 _hmem _hnot x5 hC hsize
  by_contra hno
  push_neg at hno
  simp only [ne_eq, not_not] at hno
  let F : (Fin (9 : ℕ) → Bool) → Bool := fun x =>
    (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))
  let gNot0 : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩
  let gSecond : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, x1⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨gNot0 :: gSecond :: x5.gates, x5.output⟩
  have hDfan : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    simp only [D, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · constructor <;> simp [gNot0]
    · constructor <;> simp [gSecond, hx1]
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
      PEqualNP.CircuitLowerBounds.GateOp.or.eval
        (List.map (fun x10 : ℕ => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD x10 Bool.false) x1) := by
    intro x
    simp [gSecond, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have hwires : ∀ x : Fin (9 : ℕ) → Bool,
      D.wires (List.ofFn x) =
        x5.wires (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)),
          PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x10 : ℕ => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD x10 Bool.false) x1)]) := by
    intro x
    simp only [D, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons]
    rw [hb x]
    rw [ha x]
    simp
  have hDeval : ∀ x : Fin (9 : ℕ) → Bool, D.eval (List.ofFn x) = F x := by
    intro x
    have h1 : D.eval (List.ofFn x) =
        x5.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)),
          PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun x10 : ℕ => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD x10 Bool.false) x1)]) := by
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
  have hsizeD : D.size = x5.size + 2 := by
    simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  omega
