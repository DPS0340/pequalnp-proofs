import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4297_413
    (stars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)), ∃ ss : List (ℕ × List ℕ),
      (∀ s∈ss, s.2≠[] ∧ ((s.1<n ∧ ∀ j∈s.2,n≤j ∧ j<n+m) ∨ (n ≤ s.1 ∧ s.1<n+m ∧ ∀ j∈s.2,j<n))) ∧
      (∀ (p : Fin n) (l : Fin m), (p,l)∈E ↔ ∃ s∈ss,(s.1=p.val ∧ n+l.val∈s.2) ∨ (s.1=n+l.val ∧ p.val∈s.2)) ∧
      ∀ S : Finset ℕ, (∀ e∈E, e.1.val∈S ∨ n+e.2.val∈S) → (ss.map (fun s => s.2.length)).sum+ss.length-1≤E.card+S.card-1)
    (slices : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit), (∀ p q l k, p≠q → l≠k → ¬((p,l)∈E ∧ (p,k)∈E ∧ (q,l)∈E ∧ (q,k)∈E)) → (∀ g∈C.gates, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length=2) → (∀ x, circuitFun (n+m) C x=decide (∃ p l, (p,l)∈E ∧ x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true)) →
      ∀ (a : ℕ) (f : Fin a ↪ Fin n), (a ≤ 3 ∨ m ≤ 3) → (∃ i l, (f i,l)∈E) →
        let H := Finset.univ.filter (fun e : Fin a × Fin m => (f e.1,e.2)∈E)
        let O := Finset.univ.filter (fun p : Fin n => (¬∃ i,f i=p) ∧ ∃ l,(p,l)∈E)
        ∃ S : Finset ℕ, (∀ e∈H, e.1.val∈S ∨ a+e.2.val∈S) ∧ H.card+S.card-1+O.card≤C.size)
    (large : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit), 4 ≤ n → 4 ≤ m → (∀ p q l k, p≠q → l≠k → ¬((p,l)∈E ∧ (p,k)∈E ∧ (q,l)∈E ∧ (q,k)∈E)) → IsAO2 (n+m) C → C.output<n+m+C.gates.length → (∀ x, circuitFun (n+m) C x=decide (∃ p l, (p,l)∈E ∧ x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true)) → (∀ i<C.gates.length, ∀ u v, C.gates[i]?=some ⟨GateOp.or,[u,v]⟩ → (n+m≤v → WireBelowOutput (n+m) C v → WireBelowOutput (n+m) C u) ∧ (n+m≤u → WireBelowOutput (n+m) C u → WireBelowOutput (n+m) C v)) →
      (∀ (a : ℕ) (f : Fin a ↪ Fin n), a ≤ 3 → (∃ i l, (f i,l)∈E) →
        let H := Finset.univ.filter (fun e : Fin a × Fin m => (f e.1,e.2)∈E)
        let O := Finset.univ.filter (fun p : Fin n => (¬∃ i,f i=p) ∧ ∃ l,(p,l)∈E)
        ∃ S : Finset ℕ, (∀ e∈H, e.1.val∈S ∨ a+e.2.val∈S) ∧ H.card+S.card-1+O.card≤C.size) →
      ∃ S : Finset ℕ, (∀ e∈E, e.1.val∈S ∨ n+e.2.val∈S) ∧ E.card+S.card-1≤C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → x5.output < x1 + x2 + x5.gates.length → (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → (∀ x10 < x5.gates.length, ∀ (x12 x13 : ℕ), x5.gates[x10]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x12, x13] : PEqualNP.CircuitLowerBounds.Gate } → (x1 + x2 ≤ x13 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x13 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x12) ∧ (x1 + x2 ≤ x12 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x12 → PEqualNP.CircuitMoves.WireBelowOutput (x1 + x2) x5 x13)) → ∃ (x11 : List (ℕ × List ℕ)), (∀ x12 ∈ x11, x12.2 ≠ [] ∧ ((x12.1 < x1 ∧ ∀ x14 ∈ x12.2, x1 ≤ x14 ∧ x14 < x1 + x2) ∨ x1 ≤ x12.1 ∧ x12.1 < x1 + x2 ∧ ∀ x14 ∈ x12.2, x14 < x1)) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 ↔ ∃ x14 ∈ x11, x14.1 = ↑x12 ∧ x1 + ↑x13 ∈ x14.2 ∨ x14.1 = x1 + ↑x13 ∧ ↑x12 ∈ x14.2) ∧ (List.map (fun (x12 : ℕ × List ℕ) => x12.2.length) x11).sum + x11.length - (1 : ℕ) ≤ x5.size := by
  intro n m I inst C sq ao out fit normalized
  let E := Finset.univ.filter (fun e : Fin n × Fin m => I e.1 e.2)
  have edge (p : Fin n) (l : Fin m) : (p,l)∈E ↔ I p l := by simp [E]
  have sf : ∀ p q l k, p≠q → l≠k → ¬((p,l)∈E ∧ (p,k)∈E ∧ (q,l)∈E ∧ (q,k)∈E) := by
    simpa only [edge] using sq
  have ev (x : Fin (n+m) → Bool) : circuitFun (n+m) C x=decide (∃ p l, (p,l)∈E ∧
      x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true) := by simpa only [edge] using fit x
  have allSlices := slices n m E C sf (fun g hg => ⟨ao.1 g hg,ao.2.2 g hg⟩) ev
  obtain ⟨ss,legal,rep,price⟩ := stars n m E
  refine ⟨ss,legal,fun p l => (edge p l).symm.trans (rep p l),?_⟩
  by_cases empty : E=∅
  · have bound := price ∅ (by simp [empty])
    exact bound.trans (by simp [empty])
  have existsEdge := Finset.nonempty_iff_ne_empty.mpr empty
  obtain ⟨z,hz⟩ := existsEdge
  by_cases thin : n≤3 ∨ m ≤ 3
  · let idn : Fin n ↪ Fin n := Function.Embedding.refl _
    obtain ⟨S,cover,sz⟩ := allSlices n idn thin ⟨z.1,z.2,hz⟩
    have e : (Finset.univ.filter (fun w : Fin n × Fin m => (idn w.1,w.2)∈E))=E := by
      ext w; simp [idn]
    rw [e] at cover sz
    exact (price S cover).trans (by omega)
  · obtain ⟨S,cov,sz⟩ := large n m E C (by omega) (by omega) sf ao out ev normalized
        (fun a f h => allSlices a f (Or.inl h))
    exact (price S cov).trans sz
