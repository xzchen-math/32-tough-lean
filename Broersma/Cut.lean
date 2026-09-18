import Broersma.Basic

/-! Component counting and the toughness contradiction in Section 4.
These statements count the actual connected components, not an abstract
integer supplied as a hypothesis. -/

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem isolated_reachable_eq {S : Finset V} {x y : {v // v ∉ S}}
    (hx : ∀ z, G.Adj x.val z → z ∈ S)
    (hxy : (Deleted G S).Reachable x y) : x = y := by
  by_contra hne
  obtain ⟨z, hz⟩ := hxy.nonempty_neighborSet_left hne
  exact z.property (hx z.val hz)

/-- `|I|` isolated surviving vertices and one further survivor give
at least `|I|+1` connected components. -/
theorem components_ge_isolated_add_one {S I : Finset V}
    (hsurvive : ∀ x ∈ I, x ∉ S)
    (hisolate : ∀ x ∈ I, ∀ y, G.Adj x y → y ∈ S)
    {u : V} (huS : u ∉ S) (huI : u ∉ I) : I.card + 1 ≤ components G S := by
  classical
  let vertex : Option {x // x ∈ I} → {v // v ∉ S}
    | none => ⟨u, huS⟩
    | some x => ⟨x.val, hsurvive x.val x.property⟩
  let f : Option {x // x ∈ I} → (Deleted G S).ConnectedComponent :=
    fun x => (Deleted G S).connectedComponentMk (vertex x)
  have hf : Function.Injective f := by
    intro a b hab
    have hreach := SimpleGraph.ConnectedComponent.exact hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        have heq := isolated_reachable_eq (hisolate b.val b.property) hreach.symm
        have hb : b.val = u := congrArg Subtype.val heq
        exact (huI (hb ▸ b.property)).elim
    | some a =>
      have heq := isolated_reachable_eq (hisolate a.val a.property) hreach
      cases b with
      | none =>
        have ha : a.val = u := congrArg Subtype.val heq
        exact (huI (ha ▸ a.property)).elim
      | some b =>
        have hv : a.val = b.val := congrArg (fun z : {v // v ∉ S} => z.val) heq
        exact congrArg some (Subtype.ext hv)
  have hcard := Nat.card_le_card_of_injective f hf
  simpa [components, Nat.card_eq_fintype_card] using hcard

/-- The `k+1` lower bound used in the last paragraph of the paper. -/
theorem components_neighborhood_ge {I : Finset V} (hI : Independent G I)
    {u : V} (huI : u ∉ I) (huN : u ∉ neighborhood G I) :
    I.card + 1 ≤ components G (neighborhood G I) := by
  apply components_ge_isolated_add_one
    (fun _ hx => Finset.disjoint_left.mp hI.disjoint_neighborhood hx)
    (fun x hx y hxy => mem_neighborhood.mpr ⟨x, hx, hxy.symm⟩) huN huI

theorem ToughThreeHalves.neighborhood_lower_bound (hG : ToughThreeHalves G)
    {I : Finset V} (hI : Independent G I) (hne : I.Nonempty)
    {u : V} (huI : u ∉ I) (huN : u ∉ neighborhood G I) :
    3 * (I.card + 1) ≤ 2 * (neighborhood G I).card := by
  have hcomp := components_neighborhood_ge hI huI huN
  have hpos := Finset.card_pos.mpr hne
  have ht := hG (neighborhood G I) (by omega)
  omega

/-- The two upper bounds for `|S|` in the paper are incompatible with
3/2-toughness. All subtraction is moved to the other side in ℕ. -/
theorem cut_contradiction (hG : ToughThreeHalves G)
    {I : Finset V} (hI : Independent G I) (hne : I.Nonempty)
    {u : V} (huI : u ∉ I) (huN : u ∉ neighborhood G I)
    (t : ℕ)
    (hupper₁ : (neighborhood G I).card + t + 1 ≤ 2 * I.card)
    (hupper₂ : (neighborhood G I).card + 1 ≤ t + I.card) : False := by
  have hlower := hG.neighborhood_lower_bound hI hne huI huN
  omega

/-- Exact integer arithmetic combining Claims 4.1–4.3 and the two
neighborhood bounds. Integers avoid the truncated subtraction of ℕ. -/
theorem final_counting_contradiction
    (n α m k w h q p t s : ℤ)
    (hα : α = m + k)
    (hn : n = 2 * w - 1 - h + α + q)
    (hh : p + t + w - α ≤ h)
    (hwq : w + q ≤ α - 1)
    (hs₁ : s ≤ n - α - 2 * m + p + 1)
    (hs₂ : s ≤ t + k - 1)
    (htough : 3 * (k + 1) ≤ 2 * s) : False := by
  omega

/-- The first neighborhood bound, before toughness is applied. -/
theorem first_neighborhood_bound
    (n α m k w h q p t s : ℤ)
    (hα : α = m + k)
    (hn : n = 2 * w - 1 - h + α + q)
    (hh : p + t + w - α ≤ h)
    (hwq : w + q ≤ α - 1)
    (hs : s ≤ n - α - 2 * m + p + 1) : s + t + 1 ≤ 2 * k := by
  omega

end Broersma
