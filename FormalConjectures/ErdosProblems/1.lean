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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1

*Reference:* [erdosproblems.com/1](https://www.erdosproblems.com/1)
-/

open Filter

open scoped Topology Real

namespace Erdos1

/--
A finite set of naturals $A$ is said to be a sum-distinct set for $N \in \mathbb{N}$ if
$A\subseteq\{1, ..., N\}$ and the sums $\sum_{a\in S}a$ are distinct for all $S\subseteq A$
-/
abbrev IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧ (fun (⟨S, _⟩ : A.powerset) => S.sum id).Injective

lemma sum_distinct_card_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) :
    2 ^ A.card ≤ N * A.card + 1 := by
  obtain ⟨h₁, h₂⟩ := h
  have h_card : Finset.card (Finset.image (fun S : Finset ℕ => S.sum id)
      (Finset.powerset A)) ≤ N * A.card + 1 := by
    have h_bound : ∀ S : Finset ℕ, S ⊆ A → S.sum id ≤ N * A.card := by
      exact fun S hS => le_trans (Finset.sum_le_sum_of_subset hS)
        (le_trans (Finset.sum_le_sum fun x hx => Finset.mem_Icc.mp (h₁ hx) |>.2)
          (by norm_num; nlinarith))
    exact le_trans (Finset.card_le_card <| Finset.image_subset_iff.mpr fun S hS =>
      Finset.mem_Icc.mpr ⟨Nat.zero_le _, h_bound S <| Finset.mem_powerset.mp hS⟩)
      (by norm_num)
  rwa [Finset.card_image_of_injOn, Finset.card_powerset] at h_card
  intro x hx y hy; have := @h₂ ⟨x, hx⟩ ⟨y, hy⟩; aesop

/--
If $A\subseteq\{1, ..., N\}$ with $|A| = n$ is such that the subset sums $\sum_{a\in S}a$ are
distinct for all $S\subseteq A$ then
$$
  N \gg 2 ^ n.
$$
-/
@[category research open, AMS 5 11]
theorem erdos_1 : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
    N ≠ 0 → C * 2 ^ A.card < N := by
  sorry

/--
The trivial lower bound is $N \gg 2^n / n$.
-/
@[category undergraduate, AMS 5 11]
theorem erdos_1.variants.weaker : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ)
    (_ : IsSumDistinctSet A N), N ≠ 0 → C * 2 ^ A.card / A.card < N := by
    use 1 / 8, by norm_num
    intro N A hA hN_ne_zero
    have h_card : (2 : ℝ) ^ A.card ≤ N * A.card + 1 := by
      exact_mod_cast sum_distinct_card_bound A N hA
    by_cases hA_card : A.card = 0 <;> simp_all +decide
    · positivity
    · field_simp
      rw [div_lt_iff₀] <;> norm_cast at * <;>
        nlinarith [Nat.pos_of_ne_zero (show A.card ≠ 0 by aesop),
          show (2 : ℕ) ^ A.card > A.card from Nat.recOn A.card (by norm_num) fun n ih => by
            rw [pow_succ']; linarith [Nat.one_le_pow n 2 zero_lt_two]]

/--
Erdős and Moser [Er56] proved
$$
  N \geq (\tfrac{1}{4} - o(1)) \frac{2^n}{\sqrt{n}}.
$$

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la Th\'{E}orie des Nombres, Bruxelles, 1955 (1956), 127-137.
-/
@[category research solved, AMS 5 11]
theorem erdos_1.variants.lb : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  sorry

/--
A number of improvements of the constant $\frac{1}{4}$ have been given, with the current
record $\sqrt{2 / \pi}$ first provied in unpublished work of Elkies and Gleason.
-/
@[category research solved, AMS 5 11]
theorem erdos_1.variants.lb_strong : ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
    ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
      (√(2 / π) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  sorry

/--
A finite set of real numbers is said to be sum-distinct if all the subset sums differ by
at least $1$.
-/
abbrev IsSumDistinctRealSet (A : Finset ℝ) (N : ℕ) : Prop :=
  ↑A ⊆ Set.Ioc (0 : ℝ) N ∧ (A.powerset : Set (Finset ℝ)).Pairwise fun S₁ S₂ =>
    1 ≤ dist (S₁.sum id) (S₂.sum id)

/--
A generalisation of the problem to sets $A \subseteq (0, N]$ of real numbers, such that the subset
sums all differ by at least $1$ is proposed in [Er73] and [ErGr80].

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973), 117-138.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number theory_. Monographies de L'Enseignement Mathematique (1980).
-/
@[category research open, AMS 5 11]
theorem erdos_1.variants.real : ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℝ)
    (_ : IsSumDistinctRealSet A N), N ≠ 0 → C * 2 ^ A.card < N := by
  sorry

/--
The minimal value of $N$ such that there exists a sum-distinct set with three
elements is $4$.

https://oeis.org/A276661
-/
@[category undergraduate, AMS 5 11]
theorem erdos_1.variants.least_N_3 :
    IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 3 } 4 := by
  refine ⟨⟨{1, 2, 4}, ?_⟩, ?_⟩
  · simp
    refine ⟨by decide, ?_⟩
    let P := Finset.powerset {1, 2, 4}
    have : Finset.univ.image (fun p : P ↦ ∑ x ∈ p, x) = {0, 1, 2, 4, 3, 5, 6, 7} := by
      refine Finset.ext_iff.mpr (fun n => ?_)
      simp [show P = {{}, {1}, {2}, {4}, {1, 2}, {1, 4}, {2, 4}, {1, 2, 4}} by decide]
      omega
    rw [← Set.injOn_univ, ← Finset.coe_univ]
    have : (Finset.univ.image (fun p : P ↦ ∑ x ∈ p.1, x)).card = (Finset.univ (α := P)).card := by
      rw [this]; aesop
    exact Finset.injOn_of_card_image_eq this
  · simp [mem_lowerBounds]
    intro n S h h_inj hcard3
    by_contra hn
    interval_cases n; aesop; aesop
    · have := Finset.card_le_card h
      aesop
    · absurd h_inj
      rw [(Finset.subset_iff_eq_of_card_le (Nat.le_of_eq (by rw [hcard3]; decide))).mp h]
      decide

/--
The minimal value of $N$ such that there exists a sum-distinct set with five
elements is $13$.

https://oeis.org/A276661
-/
@[category research solved, AMS 5 11]
theorem erdos_1.variants.least_N_5 :
    IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 5 } 13 := by
  constructor <;> norm_num [IsSumDistinctSet]
  · exists {6, 9, 11, 12, 13}
  · intro N hN
    contrapose! hN
    simp +zetaDelta at *
    native_decide +revert

/--
The minimal value of $N$ such that there exists a sum-distinct set with nine
elements is $161$.

https://oeis.org/A276661
-/
@[category research solved, AMS 5 11]
theorem erdos_1.variants.least_N_9 :
    IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 9 } 161 := by
  sorry

end Erdos1
