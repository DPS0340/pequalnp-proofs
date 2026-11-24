import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2658_493
    (prune : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (Monotone2 C ∧ circuitFun n C = graphFun G ∅) → ∃ D : Circuit, (Monotone2 D ∧ circuitFun n D = graphFun G ∅) ∧ D.size ≤ C.size ∧ ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g → g.op = .and →
      (∃ u v, G.Adj u v ∧ circuitFun n ⟨D.gates.set j ⟨.or,[]⟩,D.output⟩ (pairInput u v) = false) ∧
      ∀ r < g.inputs.length, ∃ x, graphFun G ∅ x = false ∧
        circuitFun n ⟨D.gates.set j ⟨g.op,g.inputs.eraseIdx r⟩,D.output⟩ x = true)
    (construct : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∃ u v, G.Adj u v) → NoFourCycle G →
      (Monotone2 C ∧ circuitFun n C = graphFun G ∅) → (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = .and →
      (∃ u v, G.Adj u v ∧ circuitFun n ⟨C.gates.set j ⟨.or,[]⟩,C.output⟩ (pairInput u v) = false) ∧
      ∀ r < g.inputs.length, ∃ x, graphFun G ∅ x = false ∧
        circuitFun n ⟨C.gates.set j ⟨g.op,g.inputs.eraseIdx r⟩,C.output⟩ x = true) →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ (∀ u v, circuitFun n D (pairInput u v) = decide (G.Adj u v)) ∧ ∀ j g, D.gates[j]? = some g → g.op = .and → ∀ u v, ¬G.Adj u v →
        gateVal n D j (pairInput u v) = false)
    (certify : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∃ u v, G.Adj u v) → Monotone2 C →
      (∀ u v, circuitFun n C (pairInput u v) = decide (G.Adj u v)) → (∀ j g, C.gates[j]? = some g → g.op = .and → ∀ u v, ¬G.Adj u v →
        gateVal n C j (pairInput u v) = false) →
      circuitFun n C = graphFun G ∅ ∧ ∀ j g, C.gates[j]? = some g → g.op = .and → BelowF G C j) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) ∧ x8.size ≤ x3.size ∧ ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x8.gates[x9]? = Option.some x10 → x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1 → Bool), (x8.wires (List.ofFn x13)).getD (x1 + x9) Bool.false = Bool.true → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ x13 x15 = Bool.true ∧ x13 x16 = Bool.true := by
  classical
  intro n G C inhabited no4 hm he
  have cycleFree : NoFourCycle G := by
    intro a c hac
    by_contra! bad
    obtain ⟨b,hb,d,hd,hbd⟩ := Finset.one_lt_card.mp bad
    obtain ⟨ab,cb⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨ad,cd⟩ := (Finset.mem_filter.mp hd).2
    exact no4 a b c d ab.ne hac ad.ne cb.ne.symm hbd cd.ne ab cb.symm cd ad.symm
  have gf (x : Fin n → Bool) : graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) || decide _) = true ↔ _
    simp
  have hfun : circuitFun n C = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    exact (he x).trans (gf x).symm
  obtain ⟨D,hD,sd,critical⟩ := prune n G C ⟨hm,hfun⟩
  obtain ⟨Q,hQ,sq,table,ands⟩ := construct n G D inhabited cycleFree hD critical
  obtain ⟨func,safe⟩ := certify n G Q inhabited hQ table ands
  refine ⟨Q,hQ,?_,sq.trans sd,?_⟩
  · intro x
    have eq := congrFun func x
    exact (Bool.eq_iff_iff.mp eq).trans (gf x)
  · intro j g hj ha x hx
    have r := safe j g hj ha x hx
    exact (gf x).mp r
