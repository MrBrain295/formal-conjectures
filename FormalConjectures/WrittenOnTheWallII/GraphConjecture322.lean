/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated
import FormalConjecturesUtil.Attributes.AMS
import FormalConjecturesUtil.Attributes.Basic

/-!
# Written on the Wall II - Conjecture 322

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

open Classical

namespace WrittenOnTheWallII.GraphConjecture322

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII [Conjecture 322](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

Let `G` be a simple connected graph on `n ≥ 5` vertices. If the maximum over all
vertices `v` of `l(v)` — the independence number of the neighborhood `N(v)` of `v`
— is at most 1, then `G` is well totally dominated.

Here `l(v) = α(G[N(v)])` is the independence number of the subgraph induced by the
open neighborhood of `v`.

The proof below only uses `2 ≤ n`; the original conjecture's assumption `5 ≤ n` is
retained to state the source faithfully.
-/
private lemma neighborhood_is_clique (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : ∀ v : α, indepNeighborsCard G v ≤ 1) {v a b : α}
    (hva : G.Adj v a) (hvb : G.Adj v b) (hab : a ≠ b) : G.Adj a b := by
  by_contra hnab
  let a' : G.neighborSet v := ⟨a, hva⟩
  let b' : G.neighborSet v := ⟨b, hvb⟩
  have hab' : a' ≠ b' := by
    intro heq
    exact hab (congrArg Subtype.val heq)
  have hindep : (G.induce (G.neighborSet v)).IsIndepSet ({a', b'} : Finset _) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact hnab ∘ SimpleGraph.induce_adj.mp
    · intro hba
      exact hnab (SimpleGraph.induce_adj.mp hba).symm
    · exact (hxy rfl).elim
  have htwo : 2 ≤ indepNeighborsCard G v := by
    simpa [indepNeighborsCard, hab'] using hindep.card_le_indepNum
  exact (Nat.not_succ_le_self 1) (htwo.trans (h v))

omit [Fintype α] in
private lemma complete_of_connected_local_cliques (G : SimpleGraph α) (hG : G.Connected)
    (hlocal : ∀ ⦃v a b : α⦄, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b) :
    G = ⊤ := by
  ext a b
  constructor
  · intro _
    simp only [SimpleGraph.top_adj]
    exact G.ne_of_adj ‹G.Adj a b›
  · intro hab
    rw [SimpleGraph.top_adj] at hab
    have hr := (SimpleGraph.reachable_iff_reflTransGen a b).mp (hG a b)
    let Q : α → α → Prop := fun x y ↦ x = y ∨ G.Adj x y
    have hQrefl : Reflexive Q := fun _ ↦ Or.inl rfl
    have hQtrans : Transitive Q := by
      intro x y z hxy hyz
      rcases hxy with rfl | hxy
      · exact hyz
      rcases hyz with rfl | hyz
      · exact Or.inr hxy
      by_cases hxz : x = z
      · exact Or.inl hxz
      · exact Or.inr (hlocal hxy.symm hyz hxz)
    have hQ : Q a b := by
      have hrtc : Relation.ReflTransGen Q a b := hr.mono (fun _ _ ↦ Or.inr)
      rw [Relation.reflTransGen_eq_self hQrefl hQtrans] at hrtc
      exact hrtc
    exact hQ.resolve_left hab

omit [Fintype α] in
private lemma complete_graph_is_well_totally_dominated [Nontrivial α] :
    IsWellTotallyDominated (⊤ : SimpleGraph α) := by
  intro S T hS hT
  have card_eq_two (U : Finset α)
      (hU : (⊤ : SimpleGraph α).IsMinimalTotalDominatingSet U) : U.card = 2 := by
    have hUne : U.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hUempty
      obtain ⟨v⟩ := inferInstanceAs (Nonempty α)
      obtain ⟨w, hw, _⟩ := hU.1 v
      rw [hUempty] at hw
      simp at hw
    obtain ⟨x, hxU⟩ := hUne
    obtain ⟨y, hyU, hxy⟩ := hU.1 x
    have hxy_ne : x ≠ y := by
      simpa only [SimpleGraph.top_adj] using hxy
    have hpair : (⊤ : SimpleGraph α).IsTotalDominatingSet {x, y} := by
      intro v
      by_cases hvx : v = x
      · exact ⟨y, by simp, by simpa [SimpleGraph.top_adj, hvx] using hxy_ne⟩
      · exact ⟨x, by simp, by simpa only [SimpleGraph.top_adj]⟩
    have hsubset : {x, y} ⊆ U := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxU
      · exact hyU
    have heq : {x, y} = U := by
      by_contra hne
      have hproper : {x, y} ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩
      exact hU.2 {x, y} hproper hpair
    rw [← heq]
    simp [hxy_ne]
  rw [card_eq_two S hS, card_eq_two T hT]

@[category research solved, AMS 5]
theorem conjecture322 (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (hn : 5 ≤ Fintype.card α)
    (h : ∀ v : α, indepNeighborsCard G v ≤ 1) :
    IsWellTotallyDominated G := by
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hlocal : ∀ ⦃v a b : α⦄, G.Adj v a → G.Adj v b → a ≠ b → G.Adj a b :=
    fun {v a b} hva hvb hab ↦ neighborhood_is_clique G h (v := v) (a := a) (b := b) hva hvb hab
  have hcomplete : G = ⊤ := complete_of_connected_local_cliques G hG hlocal
  subst G
  exact complete_graph_is_well_totally_dominated

-- Sanity checks

/-- In `K₄`, all vertices have degree 3. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 4)).maxDegree = 3 := by decide +native

/-- In the edgeless graph `⊥` on 5 vertices, the minimum degree is 0. -/
@[category test, AMS 5]
example : (⊥ : SimpleGraph (Fin 5)).minDegree = 0 := by decide +native

end WrittenOnTheWallII.GraphConjecture322
