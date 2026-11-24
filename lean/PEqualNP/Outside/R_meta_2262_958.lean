import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

-- Three disjoint induced residual edges cannot be covered by the two incomparable junk gates.
-- The first child turns this into a lower bound on the edges outside any vertex cover.
theorem PEqualNP.Outside.R_meta_2262_958
    (demand : let H := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (C : Circuit) (p q : Nat), IsLeastAO H C → TopForm H C → junk H C = {p,q} →
        ¬InCone 11 C p q → ¬InCone 11 C q p → ∀ S : Finset (Fin 11),
        (H.deleteEdges (Ustar H C : Set (Sym2 (Fin 11)))).IsVertexCover (S : Set (Fin 11)) →
        [17,17,10,6,4,2,1,0][S.card]?.getD 0 ≤ (Ustar H C).card)
    (remaining : let H := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (C : Circuit) (p q : Nat), IsLeastAO H C → TopForm H C → junk H C = {p,q} →
        ¬InCone 11 C p q → ¬InCone 11 C q p → (∃ a ∈ tops H C, InCone 11 C p a ∧ InCone 11 C q a) →
        let c := (tops H C \ centreless H C).card
        let u := (Ustar H C).card
        [17,17,10,6,4,2,1,0][c]?.getD 0 ≤ u →
        c + 2 * (centreless H C).card + (orN H C \ lam H C).card ≤ 4+u → 22 ≤ C.size) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∃ x21 ∈ x9, x12 x4 x21 ∧ x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  intro H decH C p q eqH least form topsH z U cone adj route budget cap ltPQ pair de ed common
  subst H
  have equalInst : decH = instDecidableRelFinAdjEdgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] := Subsingleton.elim _ _
  subst decH
  let J := (edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]).deleteEdges (U : Set (Sym2 (Fin 11)))
  classical
  let pool := Finset.univ.filter (fun S : Finset (Fin 11) => J.IsVertexCover (S : Set (Fin 11)))
  have nonempty : pool.Nonempty := ⟨Finset.univ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun {_ _} _ => Or.inl (Finset.mem_univ _)⟩⟩
  obtain ⟨S,hS,opt⟩ := Finset.exists_min_image pool Finset.card nonempty
  have minS : IsMinCover J S := ⟨(Finset.mem_filter.mp hS).2,fun T cov => opt T (Finset.mem_filter.mpr ⟨Finset.mem_univ _,cov⟩)⟩
  let c := (topsH \ z).card
  have upper : S.card ≤ c := cap S minS
  have lower := demand C p q least form pair de ed S minS.1
  let f (k : Nat) := [17,17,10,6,4,2,1,0][k]?.getD 0
  have down (a b : Nat) (le : a ≤ b) : f b ≤ f a := by
    by_cases h : b < 7
    · interval_cases b <;> interval_cases a <;> decide
    · obtain ⟨k,rfl⟩ : ∃ k, b = k+7 := ⟨b-7,by omega⟩
      cases k <;> simp [f]
  have shape : f c ≤ U.card := (down _ _ upper).trans lower
  by_contra! small
  apply (Nat.not_le_of_lt small) (remaining C p q least form pair de ed common shape ?_)
  change c + 2*z.card + _ ≤ 4+U.card
  change 17 + c + 2*z.card + _ ≤ C.size + U.card at budget
  omega
