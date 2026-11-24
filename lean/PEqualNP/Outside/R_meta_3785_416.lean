import Mathlib
import PEqualNP.Defs

open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3785_416
    (search : let V := (List.range 21).map (fun i => let a := (23525614998242838241557093858560 : ℕ) >>> (5*i); (([20903549701104813257814214409206692132834305521556948504182138452387990252913521825,87450172329102581734502660542769188821086026997254747913319396661892096825655264,1912314690812971607224427191607982911851698329643778133097223840990601981692004961091,1606940266590962622866085733889249973447551590526115683763002524616376032976215791004] : List (BitVec 280)).getD ((a/8)%4) 0).rotateLeft (35*(a%8)));
      ∃ (p : List (Bool × List ℕ)) (k : ℕ), (∀g∈p,g.2.length≤2) ∧ p.length≤43 ∧ k<21+p.length ∧
        (p.foldl (fun w g => let v := g.2.map (fun i => w.getD i 0); w++[ite (g.1=true) (v.foldl (· &&& ·) (-1)) (v.foldl (· ||| ·) 0)]) V).getD k 0=(1752712288311167896225073113099036249885499950629362868768964765205600927775 : BitVec 280))
    (compile : ∀ (n : ℕ) (V : List (BitVec n)) (p : List (Bool × List ℕ)) (k : ℕ), (∀g∈p,g.2.length≤2) →
      ∃ C : Circuit, Monotone2 C ∧ C.size=p.length ∧ C.output=k ∧
        ∀ r : Fin n,C.eval (V.map (fun x=>x.getLsbD r.val))=((p.foldl (fun w g => let v := g.2.map (fun i => w.getD i 0); w++[ite (g.1=true) (v.foldl (· &&& ·) (-1)) (v.foldl (· ||| ·) 0)]) V).getD k 0).getLsbD r.val)
    (border : let V := (List.range 21).map (fun i => let a := (23525614998242838241557093858560 : ℕ) >>> (5*i); (([20903549701104813257814214409206692132834305521556948504182138452387990252913521825,87450172329102581734502660542769188821086026997254747913319396661892096825655264,1912314690812971607224427191607982911851698329643778133097223840990601981692004961091,1606940266590962622866085733889249973447551590526115683763002524616376032976215791004] : List (BitVec 280)).getD ((a/8)%4) 0).rotateLeft (35*(a%8)));
      ∀ C : Circuit, Monotone2 C → (∀ r : Fin 280,C.eval (V.map (fun x=>x.getLsbD r.val))=(1752712288311167896225073113099036249885499950629362868768964765205600927775 : BitVec 280).getLsbD r.val) →
      ∀ (s : Finset (Fin 9)) (t : Finset (Fin 12)),
        C.eval ((List.ofFn (fun i : Fin 9 => decide (i∈s)))++(List.ofFn (fun j : Fin 12 => decide (j∈t))))=true ↔
        ∃ i∈s,∃j∈t,(41456571456872167955723480796225 : ℕ).testBit (12*i.val+j.val)=true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (43 : ℕ) ∧       x1.output < (21 : ℕ) + x1.size ∧         have x2 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];         have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];         ∀ (x5 x6 : Finset (Fin (13 : ℕ))), x1.eval (List.map (x3 x5 x6) x2) = Bool.true ↔ ∃ x7 ∈ x5, ↑x7 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x8 ∈ x6, x4 x7 x8 := by
  let V := (List.range 21).map (fun i => let a := (23525614998242838241557093858560 : ℕ) >>> (5*i); (([20903549701104813257814214409206692132834305521556948504182138452387990252913521825,87450172329102581734502660542769188821086026997254747913319396661892096825655264,1912314690812971607224427191607982911851698329643778133097223840990601981692004961091,1606940266590962622866085733889249973447551590526115683763002524616376032976215791004] : List (BitVec 280)).getD ((a/8)%4) 0).rotateLeft (35*(a%8)))
  obtain ⟨p,k,leg,sz,cap,eq⟩ := search
  obtain ⟨C,mono,size,out,ev⟩ := compile 280 V p k leg
  have word := border C mono (fun r=>(ev r).trans (congrArg (fun x : BitVec 280=>x.getLsbD r.val) eq))
  refine ⟨C,mono,size ▸ sz,by omega,?_⟩
  dsimp only
  intro s t
  let point : Fin 9 → Fin 13 := ![2,4,5,6,7,8,10,11,12]
  let line : Fin 12 → Fin 13 := fun j=>⟨j.val+1,Nat.succ_lt_succ j.isLt⟩
  let outside : List ℕ := [0,1,3,9]
  let ps := univ.filter (fun i : Fin 9 => point i∈s)
  let ls := univ.filter (fun j : Fin 12 => line j∈t)
  have hp (i : Fin 9) : i∈ps ↔ point i∈s := by simp [ps]
  have hl (j : Fin 12) : j∈ls ↔ line j∈t := by simp [ls]
  have enumP : ∀ u : Fin 13,u.val∉outside ↔ ∃i,point i=u := by dsimp only [outside,point];decide +kernel
  have enumL : ∀ u v : Fin 13,u.val∉outside → (u.val+v.val)%13∈outside → ∃j,line j=v := by dsimp only [outside,line];decide +kernel
  have mask : ∀ (i : Fin 9) (j : Fin 12),(41456571456872167955723480796225 : ℕ).testBit (12*i.val+j.val)=true ↔ ((point i).val+(line j).val)%13∈outside := by
    dsimp only [point,line,outside];decide +kernel
  have correct := word ps ls
  simp only [hp,hl] at correct
  change C.eval ((List.ofFn (fun i : Fin 9=>decide (point i∈s)))++(List.ofFn (fun j : Fin 12=>decide (line j∈t))))=true ↔ _
  rw [correct]
  constructor
  · rintro ⟨i,si,j,tj,ed⟩
    exact ⟨point i,si,(enumP _).mpr ⟨i,rfl⟩,line j,tj,(mask i j).mp ed⟩
  · rintro ⟨u,su,hu,v,tv,ed⟩
    obtain ⟨i,rfl⟩ := (enumP u).mp hu
    obtain ⟨j,rfl⟩ := enumL _ _ hu ed
    exact ⟨i,su,j,tv,(mask i j).mpr ed⟩
