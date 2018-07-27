import data.nat.prime
import algebra.group_power
import tactic.ring
import linear_algebra.multivariate_polynomial

universes u v

noncomputable theory
local attribute [instance] classical.prop_decidable

namespace nat

class Prime :=
(p : ℕ) (pp : nat.prime p)

end nat

open nat.Prime
variable [nat.Prime] -- fix a prime p

lemma p_ge_two : p ≥ 2 := nat.prime.ge_two pp

lemma p_eq_succ_pred_p : p = nat.succ (nat.pred p) :=
begin
  apply (nat.eq_zero_or_eq_succ_pred _).resolve_left,
  intro hp,
  have H := nat.lt_of_lt_of_le (nat.zero_lt_succ 1) p_ge_two,
  rw hp at H,
  exact (nat.lt_irrefl 0) H,
end

def Frob {A : Type u} [ring A] (x : A) := x^p

section delta_ring_aux_poly

open mv_polynomial

def delta_ring.aux_poly1 : mv_polynomial bool ℤ :=
begin
  let X0 : mv_polynomial bool ℤ := X false,
  let X1 : mv_polynomial bool ℤ := X true,
  exact (X0^p + X1^p - (X0+X1)^p),
end

def delta_ring.aux_poly2 : mv_polynomial bool ℤ :=
finsupp.map_range (λ n:ℤ, n/p) (int.zero_div p) delta_ring.aux_poly1

instance int.cast.is_ring_hom (α : Type u) [ring α] : is_ring_hom (int.cast : ℤ → α) :=
{ map_add := int.cast_add,
  map_mul := int.cast_mul,
  map_one := int.cast_one }

end delta_ring_aux_poly

def delta_ring.aux {A : Type u} [comm_ring A] : A → A → A :=
(λ a b, (mv_polynomial.functorial int.cast delta_ring.aux_poly2).eval (λ i, cond i a b : bool → A))

class delta_ring (A : Type u) extends comm_ring A :=
(δ : A → A)
(zero_prop : δ(0) = 0)
(one_prop  : δ(1) = 0)
(add_prop  : ∀ {a b}, δ(a+b) = δ(a) + δ(b) + (delta_ring.aux a b))
(mul_prop  : ∀ {a b}, δ(a*b) = a^p*δ(b) + b^p*δ(a) + p*δ(a)*δ(b))

namespace delta_ring

variables {A : Type u} [delta_ring A]

@[simp] lemma delta_zero : δ(0:A) = 0 := zero_prop A
@[simp] lemma delta_one  : δ(1:A) = 0 :=  one_prop A
@[simp] lemma aux_prop (a b : A) : (p : A) * delta_ring.aux a b = (a^p + b^p - (a+b)^p) := sorry

def Frob_lift (x : A) := x^p + p*δ(x)

instance : is_ring_hom (Frob_lift : A → A) :=
{ map_one := by simp [Frob_lift],
  map_add :=
  begin
    intros a b,
    simp [Frob_lift,add_prop,left_distrib]
  end,
  map_mul :=
  begin
    intros a b,
    simp [Frob_lift,mul_prop,mul_pow],
    ring
  end }

lemma Frob_lift_mul_delta_p (x : A) : Frob_lift(x) * δ(p) = x^p*δ(p) + p*δ(x)*δ(p) :=
by simp [Frob_lift,right_distrib]

lemma Frob_lift_is_zero_on_p_torsion (x : A) (hx : (p:A) * x = 0) (hdp : ∃ u : A, δ(p:A) * u = 1) : Frob_lift(x) = 0 :=
begin
  have foo : (0:A)^p = (0:A) :=
  begin
    rw p_eq_succ_pred_p,
    simp [pow_succ],
  end,
  have bar : δ((p:A)*x) = 0 := by rw [hx,zero_prop],
  have xyzzy : (p:A)^p * δ(x) + Frob_lift(x) * δ(p) = 0 :=
  begin
    rw [mul_prop] at bar,
    simp [Frob_lift],
    rw ← bar,
    ring
  end,
  have quux : (p:A)^p * δ(x) = 0 :=
  begin
    sorry
  end,
  -- now use that δ(p) is a unit
  sorry
end

end delta_ring