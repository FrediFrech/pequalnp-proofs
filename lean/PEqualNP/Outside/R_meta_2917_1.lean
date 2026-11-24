import Mathlib
import PEqualNP.Defs

-- A reduction for L-meta-2917. The two hypotheses are the baseline 16-gate lower
-- bounds for nine-input circuits computing the edge function of the Petersen graph
-- minus a vertex, split into the monotone case and the case with a NOT gate.
-- Any circuit for the posted step, together with the two free NOT gates, would be
-- a fifteen-gate circuit of that baseline shape.
theorem PEqualNP.Outside.R_meta_2917_1 :
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
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     (5 : ℕ) ≤ x1.headD (10 : ℕ) ∧ x1.headD (10 : ℕ) ≤ (8 : ℕ) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro _hM hN x1 hx1 hhead x4 hC hsize
  by_contra hno
  push_neg at hno
  simp only [ne_eq, not_not] at hno
  let F : (Fin (9 : ℕ) → Bool) → Bool := fun x =>
    (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))
  let gNot0 : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩
  let gNotI : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [x1.headD (10 : ℕ)]⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨gNot0 :: gNotI :: x4.gates, x4.output⟩
  have hDfan : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    simp only [D, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · constructor <;> simp [gNot0]
    · constructor <;> simp [gNotI]
    · exact hC g hg
  have hDsize : D.size ≤ 15 := by
    simp [D, PEqualNP.CircuitLowerBounds.Circuit.size] at hsize ⊢
    omega
  have hb : ∀ x : Fin (9 : ℕ) → Bool,
      gNot0.op.eval (gNot0.inputs.map (fun i => (List.ofFn x).getD i false)) = !(x (0 : Fin (9 : ℕ))) := by
    intro x
    simp [gNot0, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have ha : ∀ x : Fin (9 : ℕ) → Bool,
      gNotI.op.eval (gNotI.inputs.map (fun i => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD i false)) =
      PEqualNP.CircuitLowerBounds.GateOp.not.eval
        (List.map (fun x9 : ℕ => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD x9 Bool.false) x1) := by
    intro x
    rcases x1 with _ | ⟨a, rest⟩
    · simp at hhead
    · simp [gNotI, PEqualNP.CircuitLowerBounds.GateOp.eval]
  have hwires : ∀ x : Fin (9 : ℕ) → Bool,
      D.wires (List.ofFn x) =
        x4.wires (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)),
          PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun x9 : ℕ => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD x9 Bool.false) x1)]) := by
    intro x
    simp only [D, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons]
    rw [hb x]
    rw [ha x]
    simp
  have hDeval : ∀ x : Fin (9 : ℕ) → Bool, D.eval (List.ofFn x) = F x := by
    intro x
    have h1 : D.eval (List.ofFn x) =
        x4.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)),
          PEqualNP.CircuitLowerBounds.GateOp.not.eval (List.map (fun x9 : ℕ => (List.ofFn x ++ [!x (0 : Fin (9 : ℕ))]).getD x9 Bool.false) x1)]) := by
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
  have hsizeD : D.size = x4.size + 2 := by
    simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  omega
