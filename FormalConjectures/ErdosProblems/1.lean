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

set_option maxHeartbeats 500000

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

private lemma variance_identity (s : Finset ℕ) :
    4 * ∑ t ∈ s.powerset, ((∑ x ∈ t, (x : ℝ)) - (∑ x ∈ s, (x : ℝ)) / 2) ^ 2 =
    (2 : ℝ) ^ s.card * ∑ x ∈ s, ((x : ℝ) ^ 2) := by
  induction s using Finset.induction <;> simp_all +decide [Finset.mul_sum] ; ring_nf;
  rename_i k s hk ih; rw [ Finset.sum_powerset_insert ] ; simp_all +decide [ Finset.mul_sum _ _ _, Finset.sum_add_distrib, Finset.sum_mul ] ; ring_nf;
  · have h_sum : ∑ t ∈ Finset.powerset s, (∑ x ∈ t, (x : ℝ)) = 2 ^ (s.card - 1) * ∑ x ∈ s, (x : ℝ) := by
      clear ih hk;
      induction s using Finset.induction <;> simp_all +decide [ Finset.sum_powerset_insert ] ; ring_nf;
      rw [ Finset.sum_congr rfl fun x hx => Finset.sum_insert <| Finset.notMem_mono ( Finset.mem_powerset.mp hx ) ‹_› ] ; simp_all +decide [ Finset.sum_add_distrib, mul_comm ] ; ring_nf;
      cases ‹Finset ℕ› using Finset.induction <;> simp_all +decide [ pow_succ' ] ; ring;
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_sq, Finset.sum_const, Finset.card_powerset ] ; ring_nf;
    have h_sum_insert : ∑ t ∈ Finset.powerset s, (∑ x ∈ insert k t, (x : ℝ)) = ∑ t ∈ Finset.powerset s, (∑ x ∈ t, (x : ℝ)) + 2 ^ s.card * (k : ℝ) := by
      rw [ Finset.sum_congr rfl fun t ht => Finset.sum_insert <| Finset.notMem_mono ( Finset.mem_powerset.mp ht ) hk ] ; simp +decide [ Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_powerset ] ; ring;
    have h_sum_insert_sq : ∑ t ∈ Finset.powerset s, (∑ x ∈ insert k t, (x : ℝ)) ^ 2 = ∑ t ∈ Finset.powerset s, (∑ x ∈ t, (x : ℝ)) ^ 2 + 2 * (k : ℝ) * ∑ t ∈ Finset.powerset s, (∑ x ∈ t, (x : ℝ)) + 2 ^ s.card * (k : ℝ) ^ 2 := by
      rw [ Finset.sum_congr rfl fun t ht => by rw [ Finset.sum_insert ( Finset.notMem_mono ( Finset.mem_powerset.mp ht ) hk ) ] ] ; simp +decide [Finset.sum_add_distrib,
        Finset.mul_sum _ _ _, add_sq, mul_comm, mul_left_comm, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_powerset] ; ring;
    cases n : Finset.card s <;> simp_all +decide [ pow_succ' ] ; ring_nf at * ; linarith;
  · assumption

private lemma markov_counting {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℝ) (t : ℝ)
    (ht : 0 < t) :
    ((S.filter fun x => t ≤ |f x|).card : ℝ) ≤
    (∑ x ∈ S, (f x) ^ 2) / t ^ 2 := by
  rw [ le_div_iff₀ ( sq_pos_of_pos ht ) ]
  rw [ Finset.card_filter ]
  push_cast [ Finset.sum_mul _ _ _ ]
  exact Finset.sum_le_sum fun x _ => by split_ifs <;> nlinarith [ abs_mul_abs_self ( f x ) ]

private lemma nat_count_in_interval (S : Finset ℕ) (c : ℝ) (t : ℝ) (ht : 0 < t)
    (hS_inj : S.Nonempty → Function.Injective (fun x : S => (x : ℕ)))
    (hS : ∀ x ∈ S, |(x : ℝ) - c| < t) :
    (S.card : ℝ) ≤ 2 * t + 1 := by
  by_contra! h_contra
  obtain ⟨a, ha⟩ : ∃ a ∈ S, ∀ x ∈ S, a ≤ x := by
    exact ⟨ Nat.find <| Finset.card_pos.mp <| by exact_mod_cast ( by linarith : ( 0 : ℝ ) < S.card ), Nat.find_spec <| Finset.card_pos.mp <| by exact_mod_cast ( by linarith : ( 0 : ℝ ) < S.card ), fun x hx => Nat.find_min' _ hx ⟩
  obtain ⟨b, hb⟩ : ∃ b ∈ S, ∀ x ∈ S, x ≤ b := by
    exact ⟨ Finset.max' _ ⟨ a, ha.1 ⟩, Finset.max'_mem _ ⟨ a, ha.1 ⟩, fun x hx => Finset.le_max' _ _ hx ⟩
  have h_card : (S.card : ℝ) ≤ b - a + 1 := by
    have h_card : (S.card : ℝ) ≤ Finset.card (Finset.Icc a b) := by
      exact_mod_cast Finset.card_le_card fun x hx => Finset.mem_Icc.mpr ⟨ ha.2 x hx, hb.2 x hx ⟩
    convert h_card using 1 ; norm_num [ Nat.cast_sub ( show a ≤ b from ha.2 b hb.1 ) ] ; ring_nf
    rw [ Nat.cast_sub ] <;> push_cast <;> linarith [ ha.2 b hb.1 ]
  linarith [ abs_lt.mp ( hS a ha.1 ), abs_lt.mp ( hS b hb.1 ) ]

private lemma sum_sq_le_of_subset_Icc (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    ∑ x ∈ A, ((x : ℝ) ^ 2) ≤ A.card * (N : ℝ) ^ 2 := by
  exact le_trans ( Finset.sum_le_sum fun x hx => pow_le_pow_left₀ ( by positivity ) ( show ( x : ℝ ) ≤ N by norm_cast; linarith [ Finset.mem_Icc.mp ( hA hx ) ] ) 2 ) ( by norm_num )

private lemma chebyshev_bound (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N) :
    (3 : ℝ) * 2 ^ A.card ≤ 8 * N * Real.sqrt A.card + 4 := by
  set n := A.card
  set μ := (∑ a ∈ A, (a : ℝ)) / 2
  set t := (N : ℝ) * Real.sqrt n
  by_cases hn : n = 0 <;> simp_all +decide [ IsSumDistinctSet ]
  · norm_num
  · have h_markov : (Finset.filter (fun S : Finset ℕ => |(∑ x ∈ S, (x : ℝ)) - μ| ≥ t) (Finset.powerset A)).card ≤ 2 ^ n / 4 := by
      have h_markov : (∑ S ∈ Finset.powerset A, ((∑ x ∈ S, (x : ℝ)) - μ) ^ 2) ≤ 2 ^ n * n * (N : ℝ) ^ 2 / 4 := by
        have h_var : ∑ S ∈ A.powerset, ((∑ x ∈ S, (x : ℝ)) - μ) ^ 2 = 2 ^ n * ∑ x ∈ A, (x : ℝ) ^ 2 / 4 := by
          have := variance_identity A
          rw [ ← Finset.sum_div _ _ _ ] ; linarith
        rw [ h_var, ← Finset.sum_div _ _ _ ]
        have := sum_sq_le_of_subset_Icc A N h.1; norm_num at *; nlinarith [ pow_pos ( zero_lt_two' ℝ ) n ]
      have h_markov : (∑ S ∈ Finset.filter (fun S : Finset ℕ => |(∑ x ∈ S, (x : ℝ)) - μ| ≥ t) (Finset.powerset A), ((∑ x ∈ S, (x : ℝ)) - μ) ^ 2) ≥ (Finset.filter (fun S : Finset ℕ => |(∑ x ∈ S, (x : ℝ)) - μ| ≥ t) (Finset.powerset A)).card * t ^ 2 := by
        have h_markov : ∀ S ∈ Finset.filter (fun S : Finset ℕ => |(∑ x ∈ S, (x : ℝ)) - μ| ≥ t) (Finset.powerset A), ((∑ x ∈ S, (x : ℝ)) - μ) ^ 2 ≥ t ^ 2 := by
          exact fun S hS => by simpa using pow_le_pow_left₀ ( by positivity ) ( Finset.mem_filter.mp hS |>.2 ) 2
        simpa using Finset.sum_le_sum h_markov
      have h_markov : (Finset.filter (fun S : Finset ℕ => |(∑ x ∈ S, (x : ℝ)) - μ| ≥ t) (Finset.powerset A)).card * t ^ 2 ≤ 2 ^ n * n * (N : ℝ) ^ 2 / 4 := by
        exact h_markov.trans ( le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sq_nonneg _ ) ‹_› )
      rw [ Nat.le_div_iff_mul_le ] <;> norm_num at *
      rw [ ← @Nat.cast_le ℝ ] ; norm_num at *
      rw [ show t ^ 2 = ( N : ℝ ) ^ 2 * n by rw [ mul_pow, Real.sq_sqrt <| Nat.cast_nonneg _ ] ] at h_markov ; nlinarith [ show ( 0 :ℝ ) < N ^ 2 * n by exact mul_pos ( sq_pos_of_pos <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; exact absurd ( h.1 <| Classical.choose_spec <| Finset.card_pos.mp <| Nat.pos_of_ne_zero hn ) <| by norm_num ) <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero hn ]
    have h_interval : (Finset.filter (fun S : Finset ℕ => |(∑ x ∈ S, (x : ℝ)) - μ| < t) (Finset.powerset A)).card ≤ 2 * t + 1 := by
      convert nat_count_in_interval ( Finset.image ( fun S : Finset ℕ => ∑ x ∈ S, x ) ( Finset.filter ( fun S : Finset ℕ => |∑ x ∈ S, ( x : ℝ ) - μ| < t ) ( Finset.powerset A ) ) ) μ t _ _ using 1
      · rw [ Finset.card_image_of_injOn ] ; aesop
        intro x hx y hy; have := @h.2 ⟨ x, by aesop ⟩ ⟨ y, by aesop ⟩ ; aesop
      · exact mul_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd ( h.1 ( Classical.choose_spec ( Finset.card_pos.mp ( Nat.pos_of_ne_zero hn ) ) ) ) ( by norm_num ) ) ) ) ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hn ) ) )
      · aesop_cat
    have h_combined : (Finset.filter (fun S : Finset ℕ => |(∑ x ∈ S, (x : ℝ)) - μ| < t) (Finset.powerset A)).card + (Finset.filter (fun S : Finset ℕ => |(∑ x ∈ S, (x : ℝ)) - μ| ≥ t) (Finset.powerset A)).card = 2 ^ n := by
      rw [ Finset.card_filter, Finset.card_filter ]
      rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun x hx => by aesop, Finset.sum_const, Finset.card_powerset ] ; norm_num [ hn ]
      rfl
    rw [ ← @Nat.cast_inj ℝ ] at * ; norm_num at *
    linarith [ show ( Finset.card ( Finset.filter ( fun S : Finset ℕ => t ≤ |∑ x ∈ S, ( x : ℝ ) - μ| ) ( Finset.powerset A ) ) : ℝ ) ≤ 2 ^ n / 4 by exact le_trans ( Nat.cast_le.mpr h_markov ) ( by rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( 2 ^ n ) 4 ] ) ]

private lemma lb_for_large_card (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hn : 2 ≤ A.card) :
    (1 / 4 : ℝ) * 2 ^ A.card / Real.sqrt A.card ≤ N := by
  have h_div : (2 * 2 ^ A.card : ℝ) ≤ 8 * N * Real.sqrt A.card := by
    have := chebyshev_bound A N h
    nlinarith [ show ( 2 : ℝ ) ^ A.card ≥ 4 by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) hn ) ]
  rw [ div_le_iff₀ ] <;> first | positivity | linarith

private lemma lb_for_card_one (A : Finset ℕ) (N : ℕ) (h : IsSumDistinctSet A N)
    (hn : A.card = 1) :
    (1 / 4 : ℝ) * 2 ^ A.card / Real.sqrt A.card ≤ N := by
  rcases N with ( _ | _ | N ) <;> norm_num at * ; aesop
  · norm_num [ hn ]
  · norm_num [ hn ] ; linarith

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
  refine ⟨0, Asymptotics.isLittleO_zero _ _, ?_⟩
  intro N A h
  simp only [Pi.zero_apply, sub_zero]
  by_cases hc0 : A.card = 0
  · simp [hc0]
  · by_cases hc1 : A.card = 1
    · exact lb_for_card_one A N h hc1
    · exact lb_for_large_card A N h (by omega)

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
