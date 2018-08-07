import data.nat.prime
import algebra.group_power
import tactic.ring
import linear_algebra.multivariate_polynomial
import ring_theory.localization

universes u v w u₁

-- ### FOR_MATHLIB
-- everything in this section should move to other files

instance int.cast.is_ring_hom (R : Type u) [ring R] : is_ring_hom (int.cast : ℤ → R) :=
{ map_add := int.cast_add,
  map_mul := int.cast_mul,
  map_one := int.cast_one }


section ring_hom_commutes_with_stuff

variables {R : Type u} [comm_ring R]
variables {S : Type v} [comm_ring S]
variables (i : R → S) [is_ring_hom i]

lemma ring_hom_powers (x : R) (n : ℕ) : i(x^n) = (i x)^n :=
begin
  induction n with n ih,
  { simp [pow_zero,is_ring_hom.map_one i] },
  simp [pow_succ,is_ring_hom.map_mul i,ih]
end

section finset

open finset

variables {X : Type w} [decidable_eq X] (s : finset X) (f : X → R)

lemma ring_hom_sum.finset : i (sum s f) = sum s (i ∘ f) :=
begin
  apply finset.induction_on s,
  { repeat { rw sum_empty },
    exact is_ring_hom.map_zero i },
  { intros x s' hx ih,
    repeat { rw sum_insert hx },
    rw [is_ring_hom.map_add i, ←ih] }
end

end finset

section finsupp

open finsupp

variables {α : Type w} {β : Type u₁} [add_comm_monoid β]
variables [decidable_eq α] [decidable_eq β]
variables (f : α → β → R) (s : α →₀ β)
variables (hf1 : ∀ (a : α), f a 0 = 0)
variables (hf2 : ∀ (a : α) (b₁ b₂ : β), f a (b₁ + b₂) = f a b₁ + f a b₂)
include hf1 hf2

lemma ring_hom_sum.finsupp : i (sum s f) = sum s (λ a b, i (f a b)) :=
begin
  apply finsupp.induction s,
  { repeat { rw sum_zero_index },
    exact is_ring_hom.map_zero i },
  { intros a b f' H1 H2 ih,
    repeat { rw sum_add_index },
    repeat { rw sum_single_index },
    rw [is_ring_hom.map_add i, ← ih],
    { rw hf1; exact is_ring_hom.map_zero i },
    { apply hf1 },
    { intros, rw hf1; exact is_ring_hom.map_zero i },
    { intros, rw hf2; exact is_ring_hom.map_add i },
    { apply hf1 },
    { apply hf2 } }
end

end finsupp

end ring_hom_commutes_with_stuff

-- namespace mv_polynomial

-- variables {σ : Type u} [decidable_eq σ]
-- variables {R : Type v} [decidable_eq R] [comm_ring R]
-- variables {S : Type w} [decidable_eq S] [comm_ring S]


-- variables {τ : Type w} [decidable_eq τ]

-- theorem eval_assoc₁
-- (f : mv_polynomial σ R) (g : σ → mv_polynomial τ R) (h : τ → R)
-- : f.eval (λ n : σ, (g n).eval h) = ((map C f).eval g).eval h :=
-- begin
--   simp [eval],
--   sorry
-- end

-- theorem eval_assoc₂
-- (f : mv_polynomial σ (mv_polynomial τ R)) (g : σ → mv_polynomial τ R) (h : τ → R)
-- : C ((f.eval g).eval h) = f.eval (λ n : σ, C ((g n).eval h)) :=
-- begin
--   simp [eval],
--   sorry
-- end

-- end mv_polynomial

namespace nat

class Prime :=
(p : ℕ) (pp : nat.prime p)

end nat

-- ### end FOR_MATHLIB

-- proper start of this file

open nat.Prime
variable [nat.Prime] -- fix a prime p

open mv_polynomial

variables {R : Type u} [decidable_eq R] [comm_ring R]

def witt_polynomial (n : ℕ) : mv_polynomial ℕ R :=
finset.sum finset.univ (λ i : fin (n+1), (p^i.val * (X i.val)^(p^(n-i.val))))

-- noncomputable theory
-- local attribute [instance] classical.prop_decidable

-- def ℤpinv := localization.away (p : ℤ)
-- instance : comm_ring ℤpinv := localization.away.comm_ring _

-- def pinv : ℤpinv := sorry

def X_in_terms_of_W : ℕ → mv_polynomial ℕ ℚ
| n := (X n - (finset.sum finset.univ (λ i : fin n, have _ := i.2, (p^i.val * (X_in_terms_of_W i.val)^(p^(n-i.val)))))) * C (1/p^(n+1))

lemma X_in_terms_of_W_eq {n : ℕ} : X_in_terms_of_W n =
(X n - (finset.sum finset.univ (λ i : fin n, (p^i.val * (X_in_terms_of_W i.val)^(p^(n-i.val)))))) * C (1/p^(n+1))
:= X_in_terms_of_W.equations._eqn_1 n

-- This proof goes a long way... but deterministic timeouts keep bugging me. So I sorried it for the moment.
lemma X_in_terms_of_W_prop (n : ℕ) : (X_in_terms_of_W n).map₂ witt_polynomial C = X n :=
begin
  apply nat.strong_induction_on n,
  intros n H,
  rw X_in_terms_of_W_eq,
  rw map₂_mul,
  rw sub_eq_add_neg,
  rw map₂_add,
  rw map₂_X,
  rw map₂_C,
  rw is_ring_hom.map_mul (map C),
  { rw is_ring_hom.map_sub (map C),
    { rw map_ring_hom_X,
      rw sub_mul,
      rw sub_eq_add_neg,
      rw eval_add,
      rw eval_mul,
      rw eval_X,
      rw map_ring_hom_C,
      rw eval_C,
      rw is_ring_hom.map_neg (eval witt_polynomial),
      rw is_ring_hom.map_mul (eval witt_polynomial),
      rw eval_C,
      rw neg_mul_eq_neg_mul,
      suffices : witt_polynomial n + -eval witt_polynomial
            (map C
               (finset.sum finset.univ (λ (i : fin n), ↑p ^ i.val * X_in_terms_of_W (i.val) ^ p ^ (n - i.val)))) =
        X n * C (↑p ^ (n + 1)),
      { sorry },
      { rw show eval witt_polynomial
          (map C
             (finset.sum finset.univ (λ (i : fin n), ↑p ^ i.val * X_in_terms_of_W (i.val) ^ p ^ (n - i.val)))) =
             
             finset.sum finset.univ (λ (i : fin n), ↑p ^ i.val * (eval witt_polynomial
          ((map C) (X_in_terms_of_W (i.val))) ^ p ^ (n - i.val))),
        { sorry },
        rw show (λ (i : fin n),
             ↑p ^ i.val * eval witt_polynomial (map C (X_in_terms_of_W (i.val))) ^ p ^ (n - i.val)) = (λ (i : fin n),
             ↑p ^ i.val * (X (i.val)) ^ p ^ (n - i.val)),
        { funext i,
          rw (H i.1 i.2) },
        -- unfold witt_polynomial,
        sorry },
      -- rw [ring_hom_sum.finset (map C)],
      -- rw ring_hom_sum (eval witt_polynomial) finset.univ (λ (x : fin n), map C (↑p ^ x.val * X_in_terms_of_W (x.val) ^ p ^ (n - x.val))),
      sorry },
    { exact mv_polynomial.map_is_ring_hom C } },
  { exact mv_polynomial.map_is_ring_hom C }
end

-- theorem X_in_terms_of_W_prop2 (n : ℕ) : (witt_polynomial n).eval (X_in_terms_of_W) = X n :=
-- begin
--   simp only [witt_polynomial, ring_hom_sum.finset (eval X_in_terms_of_W), function.comp],
--   simp only [is_ring_hom.map_mul (eval X_in_terms_of_W), ring_hom_powers (eval X_in_terms_of_W)],
--   -- simp only [X_in_terms_of_W_eq],
--   sorry
-- end

-- theorem X_in_terms_of_W_prop3 (f g : ℕ → mv_polynomial (bool × ℕ) ℚ) :
-- (∀ n, (map C (X_in_terms_of_W n)).eval f = (map C (X_in_terms_of_W n)).eval g) → f = g :=
-- begin
--   intro H,
--   funext n,
--   sorry
-- end

-- def witt_structure_rat (Φ : mv_polynomial bool ℚ) (n : ℕ) : mv_polynomial (bool × ℕ) ℚ :=
-- (map C (X_in_terms_of_W n)).eval (λ k : ℕ,
--    (map C Φ).eval (λ b, ((witt_polynomial k).eval (λ i, X (b,i))))
-- )

-- lemma witt_structure_rat_eq (Φ : mv_polynomial bool ℚ) (n : ℕ) :
-- witt_structure_rat Φ n = (map C (X_in_terms_of_W n)).eval (λ k : ℕ,
--    (map C Φ).eval (λ b, ((witt_polynomial k).eval (λ i, X (b,i))))
-- ) := rfl


-- theorem witt_structure_prop (Φ : mv_polynomial bool ℚ) (φ : ℕ → mv_polynomial (bool × ℕ) ℚ) :
-- (∀ n : ℕ, (witt_polynomial n).eval φ = (map C Φ).eval (λ b, ((witt_polynomial n).eval (λ i, X (b,i)))))
-- ↔ φ = witt_structure_rat Φ
-- :=
-- begin
--   split,
--   { intro H,
--     funext n,
--     unfold witt_structure_rat,
--     rw show (λ (k : ℕ), eval (λ (b : bool), eval (λ (i : ℕ), X (b, i)) (witt_polynomial k)) (map C Φ)) =
--     (λ (k : ℕ), eval φ (witt_polynomial k)),
--     { funext k,
--       exact (H k).symm },
--     rw show φ n = (map C ((map C (X_in_terms_of_W n)).eval witt_polynomial)).eval φ,
--     { rw X_in_terms_of_W_prop,
--       rw map_ring_hom_X C,
--       exact eval_X.symm },
--     simp,
--     sorry },
--   { intro H,
--     intro k,
--     refine @congr _ _ _ _ k k _ rfl,
--     apply X_in_terms_of_W_prop3,
--     intro n,
--     rw ← witt_structure_rat_eq,
--     sorry }
-- end
