import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4330_317
    (normal : let F := fun x : Fin 10 → Bool => decide (∃ p q : Fin 10, (79267452898694397750816084002 : ℕ).testBit (10*p.val+q.val)=true ∧ x p=true ∧ x q=true);
      ∀ (C : Circuit) (s : Bool), FanInTwo C → C.size=18 → (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) != s)=F x) →
      (∃ (D : Circuit) (b : Bool), FanInTwo D ∧ D.size≤15 ∧ ∀ x : Fin 10 → Bool, x 9=false → (D.eval (List.ofFn x) != b)=F x) ∨ (∃ (j : Fin 3) (D : Circuit) (b : Bool), FanInTwo D ∧ D.size=17 ∧ ((∀ p q : Fin 10, p≠q → (⟨.and,[p.val,q.val]⟩ : Gate)∉D.gates) ∧ (∀ v : Fin 10, let c := D.gates.countP (fun g => g.inputs.contains v.val); if j≠0 ∧ (v=0 ∨ v=(if j=1 then 1 else 2)) then c=1 else c≤2) ∧ (j=0 → D.gates.countP (fun g => g.inputs.contains 0 || g.inputs.contains 10)=1)) ∧ (∀ x : Fin 10 → Bool, (D.eval (List.ofFn x ++ [if j=0 then !x 0 else x 0 || x (if j=1 then 1 else 2)]) != b)=F x)))
    (close : let F := fun x : Fin 10 → Bool => decide (∃ p q : Fin 10, (79267452898694397750816084002 : ℕ).testBit (10*p.val+q.val)=true ∧ x p=true ∧ x q=true);
      (∃ (j : Fin 3) (D : Circuit) (b : Bool), FanInTwo D ∧ D.size=17 ∧ ((∀ p q : Fin 10, p≠q → (⟨.and,[p.val,q.val]⟩ : Gate)∉D.gates) ∧ (∀ v : Fin 10, let c := D.gates.countP (fun g => g.inputs.contains v.val); if j≠0 ∧ (v=0 ∨ v=(if j=1 then 1 else 2)) then c=1 else c≤2) ∧ (j=0 → D.gates.countP (fun g => g.inputs.contains 0 || g.inputs.contains 10)=1)) ∧ (∀ x : Fin 10 → Bool, (D.eval (List.ofFn x ++ [if j=0 then !x 0 else x 0 || x (if j=1 then 1 else 2)]) != b)=F x)) → ∃ (D : Circuit) (b : Bool), FanInTwo D ∧ D.size≤15 ∧ ∀ x : Fin 10 → Bool, x 9=false → (D.eval (List.ofFn x) != b)=F x) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size = (17 : ℕ) →         have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => (x3.wires ({ gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x4 Bool.false;         (∀ (x10 : Fin (10 : ℕ) → Bool), (if x5 = Bool.true then !x9 x10 else x9 x10) = x1 x10) →           ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit) (x12 : ℕ) (x13 : Bool),             PEqualNP.MetaComplexity.FanInTwo x11 ∧               x11.size ≤ (15 : ℕ) ∧                 have x14 : (Fin (10 : ℕ) → Bool) → Bool := fun (x14 : Fin (10 : ℕ) → Bool) => (x11.wires (List.ofFn x14)).getD x12 Bool.false;                 ∀ (x15 : Fin (10 : ℕ) → Bool), x15 (9 : Fin (10 : ℕ)) = Bool.false → (if x13 = Bool.true then !x14 x15 else x14 x15) = x1 x15 := by
  let F := fun x : Fin 10 → Bool => decide (∃ p q : Fin 10, (79267452898694397750816084002 : ℕ).testBit (10*p.val+q.val)=true ∧ x p=true ∧ x q=true)
  let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  have edge : ∀ p q : Fin 10, (79267452898694397750816084002 : ℕ).testBit (10*p.val+q.val)=true ↔ (p,q)∈E := by
    dsimp only [E]; decide +kernel
  have decode (x : Fin 10 → Bool) : F x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
    have rep : ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))=E.any (fun e=>x e.1 && x e.2) := by simp [E,Bool.or_assoc]
    rw [rep]
    apply Bool.eq_iff_iff.mpr
    simp only [F,decide_eq_true_eq,List.any_eq_true]
    constructor
    · rintro ⟨p,q,h,a,b⟩
      exact ⟨(p,q),(edge p q).mp h,by simp [a,b]⟩
    · rintro ⟨⟨p,q⟩,h,ab⟩
      exact ⟨p,q,(edge p q).mpr h,by simpa only [Bool.and_eq_true] using ab⟩
  have phase (z b : Bool) : (z != b)=(if b then !z else z) := by cases b <;> cases z <;> rfl
  dsimp only
  intro g C out s hf ht len fit
  let W : Circuit := ⟨g::C.gates,out⟩
  have wf : FanInTwo W := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl|h
    · exact hf _ List.mem_cons_self
    · exact ht _ h
  have sz : W.size=18 := by change (g::C.gates).length=18; change C.gates.length=17 at len; simp [len]
  have ev (x : Fin 10 → Bool) : (W.eval (List.ofFn x) != s)=F x := by
    rw [phase,decode]; exact fit x
  have answer := (normal W s wf sz ev).elim id close
  obtain ⟨D,b,h,size,eval⟩ := answer
  refine ⟨D,D.output,b,h,size,fun x hx => ?_⟩
  have h' := eval x hx
  change (_ != b)=F x at h'
  rw [phase,decode] at h'
  exact h'
