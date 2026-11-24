import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.SharedBlockCost

theorem PEqualNP.Outside.R_meta_612_618
    (visible : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∃ u v, G.Adj u v) → NoFourCycle G → Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∀ H : SimpleGraph (Fin n), H ≤ G → (∀ u v, H.Adj u v → ∃ k < C.size, circuitFun n ⟨C.gates.mapIdx (fun i g => if i=k ∨ isOrOp g.op=true then g else ⟨.or,[]⟩),C.output⟩ (pairInput u v) = true) →
      ∃ S : Finset (Fin n), CoverPromise.IsVertexCover H S ∧ H.edgeSet.ncard + S.card ≤ C.size+1)
    (trace : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      Monotone2 C → circuitFun n C = graphFun G ∅ → ∀ u v, G.Adj u v → ¬ (∃ k < C.size, circuitFun n ⟨C.gates.mapIdx (fun i g => if i=k ∨ isOrOp g.op=true then g else ⟨.or,[]⟩),C.output⟩ (pairInput u v) = true) →
      let x := pairInput u v; ∃ a b w, PEqualNP.Core.InOutputCone n C b ∧ InCone n C a b ∧
      (gateAt C a).op=.and ∧ (gateAt C b).op=.and ∧ BelowF G C b ∧
      gateVal n C a x=true ∧ gateVal n C b x=true ∧
      w ∈ (gateAt C b).inputs ∧ PEqualNP.CleanedNonEdge.wireVal n C w x=true ∧
      PEqualNP.CleanedNonEdge.wireVal n ⟨C.gates.mapIdx (fun i g => if i=C.size ∨ isOrOp g.op=true then g else ⟨.or,[]⟩),C.output⟩ w x=false)
    (hidden : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      (∃ u v, G.Adj u v ∧ ¬ (∃ k < C.size, circuitFun n ⟨C.gates.mapIdx (fun i g => if i=k ∨ isOrOp g.op=true then g else ⟨.or,[]⟩),C.output⟩ (pairInput u v) = true) ∧ (let x := pairInput u v; ∃ a b w, PEqualNP.Core.InOutputCone n C b ∧ InCone n C a b ∧
      (gateAt C a).op=.and ∧ (gateAt C b).op=.and ∧ BelowF G C b ∧
      gateVal n C a x=true ∧
      w ∈ (gateAt C b).inputs ∧
      PEqualNP.CleanedNonEdge.wireVal n ⟨C.gates.mapIdx (fun i g => if i=C.size ∨ isOrOp g.op=true then g else ⟨.or,[]⟩),C.output⟩ w x=false)) →
      ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ G.edgeSet.ncard + S.card ≤ C.size+1) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  intro n t G initial edge no4 _ minimal initialMono correct
  have squareFree : NoFourCycle G := by
    intro a c hac
    by_contra! bad
    obtain ⟨b,hb,d,hd,hbd⟩ := Finset.one_lt_card.mp bad
    obtain ⟨ab,cb⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨ad,cd⟩ := (Finset.mem_filter.mp hd).2
    exact no4 a b c d ab.ne hac ad.ne cb.ne.symm hbd cd.ne ab cb.symm cd ad.symm
  have gf (x : Fin n → Bool) : graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) || decide _) = true ↔ _
    simp
  have initialSem : circuitFun n initial = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    exact (correct x).trans (gf x).symm
  let feas (s : ℕ) := ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = s
  have existsSize : ∃ s, feas s := ⟨initial.size,initial,initialMono,initialSem,rfl⟩
  obtain ⟨C,mono,sem,sizeEq⟩ := Nat.find_spec existsSize
  have smaller : C.size ≤ initial.size := sizeEq.trans_le
    (Nat.find_min' existsSize (show feas initial.size from ⟨initial,initialMono,initialSem,rfl⟩))
  have least : IsMinimalMonoCircuit n C := by
    refine ⟨mono,?_⟩
    intro D dm de
    exact sizeEq.trans_le (Nat.find_min' existsSize (show feas D.size from ⟨D,dm,de.trans sem,rfl⟩))
  by_cases bad : ∃ u v, G.Adj u v ∧ ¬ (∃ k < C.size, circuitFun n ⟨C.gates.mapIdx (fun i g => if i=k ∨ isOrOp g.op=true then g else ⟨.or,[]⟩),C.output⟩ (pairInput u v) = true)
  · obtain ⟨u,v,adj,miss⟩ := bad
    obtain ⟨a,b,w,live,cone,oa,ob,below,ona,_,read,_,cut⟩ := trace n G C mono sem u v adj miss
    obtain ⟨S,cover,cost⟩ := hidden n G C squareFree least sem
      ⟨u,v,adj,miss,a,b,w,live,cone,oa,ob,below,ona,read,cut⟩
    exact (Nat.add_le_add_left (minimal S cover) _).trans (cost.trans (Nat.add_le_add_right smaller 1))
  · have all : ∀ u v, G.Adj u v → ∃ k < C.size, circuitFun n ⟨C.gates.mapIdx (fun i g => if i=k ∨ isOrOp g.op=true then g else ⟨.or,[]⟩),C.output⟩ (pairInput u v) = true := by
      intro u v h
      by_contra miss
      exact bad ⟨u,v,h,miss⟩
    obtain ⟨S,cover,cost⟩ := visible n G C edge squareFree mono sem G le_rfl all
    exact (Nat.add_le_add_left (minimal S cover) _).trans (cost.trans (Nat.add_le_add_right smaller 1))
