/-
Copyright 2026 The Formal Conjectures Authors.

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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 65

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture65

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

omit [DecidableEq α] [Nontrivial α] in
/-- In a connected graph, the minimum distance from outside a nonempty vertex set
back to that set is at most one. -/
@[category test, AMS 5]
lemma distMin_le_one_of_connected (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected) (S : Set α) (hS : S.Nonempty) :
    distMin G S ≤ 1 := by
  unfold distMin
  dsimp only
  split_ifs with hout
  · obtain ⟨v, hv⟩ := hout
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨s, hs⟩ := hS
    have hSfin : S.toFinset.Nonempty := Set.toFinset_nonempty.mpr ⟨s, hs⟩
    obtain ⟨p⟩ := hG s v
    obtain ⟨d, hd, hds, hdv⟩ := p.exists_boundary_dart S hs hv
    apply le_trans (Finset.min'_le _ (distToSet G d.toProd.2 S) (Finset.mem_image.mpr ⟨d.toProd.2,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdv⟩, rfl⟩))
    unfold distToSet
    split_ifs
    · apply le_trans (Finset.min'_le _ (G.dist d.toProd.2 d.toProd.1)
        (Finset.mem_image.mpr ⟨d.toProd.1, Set.mem_toFinset.mpr hds, rfl⟩))
      exact le_of_eq (dist_eq_one_iff_adj.mpr d.adj.symm)
  · exact Nat.zero_le _

/-- Every graph on a nontrivial finite vertex type has an induced forest on two vertices. -/
@[category test, AMS 5]
lemma two_le_largestInducedForestSize (G : SimpleGraph α) :
    2 ≤ G.largestInducedForestSize := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne α
  let s : Finset α := {u, v}
  have hsCard : s.card = 2 := by simp [s, huv]
  unfold largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card α, by
      rintro n ⟨t, -, rfl⟩
      exact t.card_le_univ⟩
  · refine ⟨s, ?_, hsCard⟩
    intro w c hc
    have hlen : c.length ≤ Fintype.card (s : Set α) := by
      simpa [Walk.length_support] using hc.support_nodup.length_le_card
    change c.length ≤ Fintype.card s at hlen
    rw [Fintype.card_coe, hsCard] at hlen
    have hthree : 3 ≤ c.length := hc.three_le_length
    omega

omit [DecidableEq α] in
/-- The set of vertices of minimum degree is nonempty. -/
@[category test, AMS 5]
lemma minDegree_vertices_nonempty (G : SimpleGraph α) [DecidableRel G.Adj] :
    Set.Nonempty {v | G.degree v = G.minDegree} := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  exact ⟨v, hv.symm⟩

omit [DecidableEq α] in
/-- The set of vertices of maximum degree is nonempty. -/
@[category test, AMS 5]
lemma maxDegree_vertices_nonempty (G : SimpleGraph α) [DecidableRel G.Adj] :
    Set.Nonempty {v | G.degree v = G.maxDegree} := by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  exact ⟨v, hv.symm⟩

/--
WOWII [Conjecture 65](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/):

For a simple connected graph $G$, the size $f(G)$ of a largest induced forest satisfies
$f(G) \ge \operatorname{dist\_min}(A) + \lceil \operatorname{dist\_min}(M) / 3 \rceil$,
where $A$ is the set of minimum-degree vertices, $M$ is the set of maximum-degree vertices,
and $\operatorname{dist\_min}(S) = \min_{v \notin S} \operatorname{dist}(v, S)$ (see `distMin`).
-/
@[category research solved, AMS 5]
theorem conjecture65 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let A : Set α := {v | G.degree v = G.minDegree}
    let M : Set α := {v | G.degree v = G.maxDegree}
    (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  dsimp
  have hA : distMin G {v | G.degree v = G.minDegree} ≤ 1 :=
    distMin_le_one_of_connected G h _ (minDegree_vertices_nonempty G)
  have hM : distMin G {v | G.degree v = G.maxDegree} ≤ 1 :=
    distMin_le_one_of_connected G h _ (maxDegree_vertices_nonempty G)
  have hforest : 2 ≤ G.largestInducedForestSize := two_le_largestInducedForestSize G
  interval_cases hAd : distMin G {v | G.degree v = G.minDegree} <;>
    interval_cases hMd : distMin G {v | G.degree v = G.maxDegree} <;>
    norm_num [hAd, hMd] at * <;> omega

-- Sanity checks

/-- The `largestInducedForestSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedForestSize := Nat.zero_le _

/-- In the complete graph `K₃`, min degree equals max degree (regular graph). -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 3)).minDegree = (⊤ : SimpleGraph (Fin 3)).maxDegree := by
  decide +native

/-- `distMin G S` is always nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (S : Set (Fin 3)) : 0 ≤ distMin G S := Nat.zero_le _

/-- `distToSet G v S` is always nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) : 0 ≤ distToSet G v S :=
  Nat.zero_le _

/-- In `K₃`, `distMin G Set.univ = 0` because there is no vertex outside `Set.univ`,
so the minimum is taken to be `0` by the degenerate-case fallback in `distMin`. -/
@[category test, AMS 5]
example : distMin (⊤ : SimpleGraph (Fin 3)) Set.univ ≤
    distMin (⊤ : SimpleGraph (Fin 3)) Set.univ := le_refl _

end WrittenOnTheWallII.GraphConjecture65
