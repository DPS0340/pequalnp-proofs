import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1888_316
    (wiring : ∀ (C : Circuit) (ρ : Fin 10 → Fin 10), FanInTwo C → ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 2]) = C.eval (List.ofFn (x ∘ ρ) ++ [x 0 || x 2]))
    (budget : ∀ C : Circuit, FanInTwo C → (∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) → 16 ≤ C.size ∧ ∀ j : Fin 10, (if j=0 ∨ j=2 then 15 else 14) + C.gates.countP (fun g => GateOp.rec (g.inputs.contains j.val) (g.inputs.contains j.val) ((g.inputs.take 1).contains j.val) (fun _ => g.inputs.contains j.val) (g.inputs.contains j.val) g.op) ≤ C.size)
    (remaining : ∀ C : Circuit, FanInTwo C → 16 ≤ C.size → C.size ≤ 18 → (∀ j : Fin 10, (if j=0 ∨ j=2 then 15 else 14) + C.gates.countP (fun g => GateOp.rec (g.inputs.contains j.val) (g.inputs.contains j.val) ((g.inputs.take 1).contains j.val) (fun _ => g.inputs.contains j.val) (g.inputs.contains j.val) g.op) ≤ C.size) → ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C ρ hf hs
  by_contra! correct
  obtain ⟨D,good,same,ev⟩ := wiring C ρ hf
  have computes (x : Fin 10 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 2]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) :=
    (ev x).trans (correct x)
  obtain ⟨lower,readers⟩ := budget D good computes
  obtain ⟨x,miss⟩ := remaining D good lower (by simpa only [same] using hs) readers
  exact miss (computes x)
