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

@[simp] lemma ring_hom_powers (x : R) (n : ℕ) : i(x^n) = (i x)^n :=
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

lemma quux {A : Type*} [add_comm_group A] (n : ℕ) (f : ℕ → A) : (finset.range (n+1)).sum f = f n + (finset.range n).sum f :=
begin
  sorry
end

end finset

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

-- end mv_polynomial

namespace nat

class Prime :=
(p : ℕ) (pp : nat.prime p)

end nat

-- ### end FOR_MATHLIB

-- proper start of this file

open nat.Prime
variable [nat.Prime] -- fix a prime p

lemma p_ne_zero : p ≠ 0 := nat.pos_iff_ne_zero.mp $ nat.prime.pos pp

open mv_polynomial

variables {R : Type u} [decidable_eq R] [comm_ring R]

theorem range_sum_eq_fin_univ_sum {α} [add_comm_monoid α] (f : ℕ → α) (n) :
  (finset.range n).sum f = finset.univ.sum (λ i : fin n, f i.1) :=
show _ = @multiset.sum α _ ↑(list.map _ _),
by rw [list.map_pmap, list.pmap_eq_map]; refl

def witt_polynomial (n : ℕ) : mv_polynomial ℕ R :=
(finset.range (n+1)).sum (λ i, (C p ^ i * X i ^ (p^(n-i))))

def X_in_terms_of_W : ℕ → mv_polynomial ℕ ℚ
| n := (X n - (finset.sum finset.univ (λ i : fin n,
  have _ := i.2, (C p^i.val * (X_in_terms_of_W i.val)^(p^(n-i.val)))))) * C (1/p^n)

lemma X_in_terms_of_W_eq {n : ℕ} : X_in_terms_of_W n =
    (X n - (finset.range n).sum (λ i, C p ^ i * X_in_terms_of_W i ^ p ^ (n - i))) *
      C (1 / ↑p ^ n) :=
by rw [X_in_terms_of_W, range_sum_eq_fin_univ_sum]

set_option pp.all true

lemma X_in_terms_of_W_prop (n : ℕ) : (X_in_terms_of_W n).eval₂ C witt_polynomial = X n :=
begin
  apply nat.strong_induction_on n,
  intros n H,
  rw X_in_terms_of_W_eq,
  simp only [eval₂_mul, eval₂_add, eval₂_sub, eval₂_neg, eval₂_C, eval₂_X],
  rw (_ : witt_polynomial n -
         eval₂ C witt_polynomial
           (finset.sum (finset.range n) (λ (i : ℕ), C ↑p ^ i * X_in_terms_of_W i ^ p ^ (n - i)))
          = C (p ^ n) * X n),
  { rw [mul_comm, ←mul_assoc],
    conv
    begin
      to_rhs,
      rw ←one_mul (X n : mv_polynomial ℕ ℚ),
    end,
    rw [←C_mul, ←C_1],
    congr,
    simp,
    rw inv_mul_cancel _,
    clear H,
    apply pow_ne_zero,
    sorry },
  -- Deep breath.
  rw sub_eq_iff_eq_add,
  unfold witt_polynomial,
  rw quux n (λ (i : ℕ), (C ↑p ^ i * X i ^ p ^ (n - i) : mv_polynomial ℕ ℚ)),
  dsimp,
  rw nat.sub_self,
  -- rw @ring_hom_powers _ _ (mv_polynomial ℕ ℚ) (by apply_instance) C (by apply_instance) (↑p) n,
  rw @ring_hom_sum.finset (mv_polynomial ℕ ℚ) (by apply_instance) _ _ (eval₂ C witt_polynomial) _ _ _ (finset.range n)
    (λ i, C ↑p ^ i * X_in_terms_of_W (i) ^ p ^ (n - i)),
  -- rw ring_hom_sum.finset (eval₂ C witt_polynomial) (finset.range n)
  -- (λ i, C ↑p ^ i * X_in_terms_of_W (i) ^ p ^ (n - i)),
  simp only [function.comp, eval₂_mul],
  dsimp,
  congr,
  { rw ring_hom_powers C _ _,
    sorry },
  { rw nat.sub_self,
    simp },
  { funext,
    dsimp [fin.raise],
    congr,
    { --rw ring_hom_powers (eval₂ C witt_polynomial) _ i.val,
      --rw eval₂_C,
      sorry },
    { rw ring_hom_powers (eval₂ C witt_polynomial) _ _,
      rw H x.val x.is_lt }
    }
end

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
