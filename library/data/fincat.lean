/-
Copyright (c) 2015 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais

Category of finite ordinal types.
-/

import data.nat data.fin data.equiv
open nat

namespace fin

-- Initial Object --

definition zero.init (n : nat) : fin 0 → fin n := elim0

definition zero.rec {C : fin 0 → Type} : Π i : fin 0, C i := elim0

theorem zero.ext {C : fin 0 → Type} {f g : Π i : fin 0, C i} : f = g :=
  funext zero.rec

definition empty_of_zero : fin 0 → empty := zero.rec

definition zero_of_empty : empty → fin 0 := empty.rec _

definition zero_equiv_empty : equiv (fin 0) empty :=
  equiv.mk empty_of_zero zero_of_empty zero.rec (empty.rec _)

-- Terminal Object --

definition one.term (n : nat) : fin n → fin 1 := (λ i, zero 0)

definition one.rec {C : fin 1 → Type} (H : C (zero 0)) : (Π i : fin 1, C i)
| (mk v h) :=
  have eqz : mk v h = zero 0, from eq_of_veq (eq_zero_of_le_zero (le_of_lt_succ h)),
  eq.rec_on (eq.symm eqz) H

theorem one.ext {C : fin 1 → Type} {H : C (zero 0)} {f g : Π i : fin 1, C i} : f (zero 0) = g (zero 0) → f = g :=
  take Hzero, funext (one.rec Hzero)

theorem one.eq : ∀ i j : fin 1, i = j := one.rec (one.rec rfl)

definition unit_of_one : fin 1 → unit := one.rec unit.star

definition one_of_unit : unit → fin 1 := unit.rec (zero 0)

definition one_equiv_unit : equiv (fin 1) unit :=
  equiv.mk unit_of_one one_of_unit
    (one.rec rfl)
    (unit.rec rfl)

-- Coproducts --

definition add.inl {m n : nat} : fin m → fin (m + n)
| (mk v h) := mk v (lt_add_of_lt_right h n)

definition add.inr {m n : nat} : fin n → fin (m + n)
| (mk v h) := mk (m + v) (add_lt_add_left h m)

definition add.rec {m n : nat} {C : fin (m + n) → Type} :
  (Π i : fin m, C (add.inl i)) →
  (Π j : fin n, C (add.inr j)) →
  (Π k : fin (m + n), C k) :=
  take fl fr, fin.rec (take v h,
    decidable.rec_on (nat.decidable_lt v m)
      (λ h', fl (mk v h'))
      (λ f', let v' := v - m in
        have Heq : m + v' = v, from add_sub_of_le (le_of_not_gt f'),
        assert h' : v' < n, from lt_of_add_lt_add_left (eq.subst (eq.symm Heq) h),
        have Leq : add.inr (mk v' h') = mk v h, from eq_of_veq Heq,
        have Cr : C (add.inr (mk v' h')), from fr (mk v' h'),
        eq.rec_on Leq Cr))

definition add.ext {m n : nat} {C : fin (m + n) → Type} {f g : Π k : fin (m + n), C k} :
  (∀ i : fin m, f (add.inl i) = g (add.inl i)) →
  (∀ j : fin n, f (add.inr j) = g (add.inr j)) →
  f = g :=
  take Hinl Hinr, funext (add.rec Hinl Hinr)

definition add.eq_rec_inl {m n : nat} {C : fin (m + n) → Type}
  {F : Π i : fin m, C (add.inl i)} {G : Π j : fin n, C (add.inr j)} :
  ∀ {i : fin m}, add.rec F G (add.inl i) = F i :=
  begin
    intro i, cases i with [vi, hi],
    unfold add.rec, unfold add.inl,
    cases (decidable_lt vi m), esimp, contradiction
  end

definition add.eq_rec_inr {m n : nat} {C : fin (m + n) → Type}
  {F : Π i : fin m, C (add.inl i)} {G : Π j : fin n, C (add.inr j)} :
  ∀ {j : fin n}, add.rec F G (add.inr j) = G j :=
  begin
    intro j, cases j with [vj, hj],
    unfold add.rec, unfold add.inr,
    cases (decidable_lt (m + vj) m) with [hf,hn],
    { apply absurd hf (not_lt_of_ge (le_add_right m vj))},
    { esimp, apply heq.to_eq,
      transitivity (G (mk (m + vj - m) _)),
      { unfold eq.rec_on, apply eq_rec_heq},
      { apply hcongr_arg, apply eq_of_veq, exact (add_sub_cancel_left m vj)}}
  end

definition add.to_sum {m n : nat} : fin (m + n) → sum (fin m) (fin n) :=
  add.rec (λ i : fin m, sum.inl i) (λ j : fin n, sum.inr j)

definition add.of_sum {m n : nat} : sum (fin m) (fin n) → fin (m + n) :=
  sum.rec add.inl add.inr

definition add_equiv_sum {m n : nat} : equiv (fin (m + n)) (sum (fin m) (fin n)) :=
  equiv.mk add.to_sum add.of_sum
    (add.rec
      (λ i, by unfold add.to_sum; rewrite add.eq_rec_inl)
      (λ j, by unfold add.to_sum; rewrite add.eq_rec_inr))
    (sum.rec
      (λ i, by unfold add.to_sum; unfold add.of_sum; rewrite add.eq_rec_inl)
      (λ j, by unfold add.to_sum; unfold add.of_sum; rewrite add.eq_rec_inr))

-- Products --

private lemma mul.mk_is_lt {m n : nat} {i j : nat} : i < m → j < n → i * n + j < m * n :=
  take hi hj,
  let m' := nat.pred m in
  have Sm : m = nat.succ m', from
    or.elim (eq_zero_or_eq_succ_pred m)
      (take F, absurd (eq.subst F hi) (not_lt_zero i))
      (take H, H),
  have hi' : i ≤ m', from le_of_lt_succ (eq.subst Sm hi),
  have A : i * n ≤ m' * n, from mul_le_mul_right n hi',
  have B : i * n + j < m' * n + n, from add_lt_add_of_le_of_lt A hj,
  have C : i * n + j < (nat.succ m') * n, from eq.subst (eq.symm (succ_mul m' n)) B,
  eq.subst (eq.symm Sm) C

definition mul.mk {m n : nat} : Π (i : fin m) (j : fin n), fin (m * n)
| (mk vi hi) (mk vj hj) := mk (vi * n + vj) (mul.mk_is_lt hi hj)

definition mul.pr1 {m n : nat} : Π (k : fin (m * n)), fin m
| (mk v h) := mk (v div n) (div_lt_of_lt_mul h)

definition mul.pr2 {m n : nat} : Π (k : fin (m * n)), fin n
| (mk v h) :=
  have p : 0 < n, from pos_of_mul_pos_left (lt_of_le_of_lt (zero_le v) h),
  mk (v mod n) (mod_lt v p)

definition mul.eq_mk_pr1_pr2 {m n : nat} : ∀ (k : fin (m * n)), k = mul.mk (mul.pr1 k) (mul.pr2 k)
| (mk v h) := eq_of_veq (eq_div_mul_add_mod v n)

definition mul.eq_pr1_mk {m n : nat} : ∀ (i : fin m) (j : fin n), i = mul.pr1 (mul.mk i j)
| (mk vi hi) (mk vj hj) :=
  have pn : n > 0, from lt_of_le_of_lt (zero_le _) hj,
  eq_of_veq (calc
    vi  = 0 + vi                : zero_add
    ... = vj div n + vi         : div_eq_zero_of_lt hj
    ... = (vj + vi * n) div n   : add_mul_div_self pn
    ... = (vi * n + vj) div n   : add.comm)

definition mul.eq_pr2_mk {m n : nat} : ∀ (i : fin m) (j : fin n), j = mul.pr2 (mul.mk i j)
| (mk vi hi) (mk vj hj) :=
  eq_of_veq (calc
    vj  = vj mod n              : mod_eq_of_lt hj
    ... = (vj + vi * n) mod n   : add_mul_mod_self
    ... = (vi * n + vj) mod n   : add.comm)

definition mul.rec {m n : nat} {C : fin (m * n) → Type} :
  (Π (i : fin m) (j : fin n), C (mul.mk i j)) →
  (Π k : fin (m * n), C k) :=
  take F k, eq.rec_on (eq.symm (mul.eq_mk_pr1_pr2 k)) (F (mul.pr1 k) (mul.pr2 k))

definition mul.ext {m n : nat} {C : fin (m * n) → Type} {f g : Π k : fin (m * n), C k} :
  (∀ (i : fin m) (j : fin n), f (mul.mk i j) = g (mul.mk i j)) → f = g :=
  take Hmk, funext (mul.rec Hmk)

lemma mul.eq_rec_mk {m n : nat} {C : fin (m * n) → Type} {F : Π (i : fin m) (j : fin n), C (mul.mk i j)} :
  ∀ (i : fin m) (j : fin n), mul.rec F (mul.mk i j) = F i j :=
  begin
    intros i j,
    unfold mul.rec, unfold eq.rec_on,
    apply heq.to_eq,
    transitivity F (mul.pr1 (mul.mk i j)) (mul.pr2 (mul.mk i j)),
    { apply eq_rec_heq},
    { apply hcongr_arg2,
      rewrite [-mul.eq_pr1_mk,-mul.eq_pr2_mk],
      rewrite [-mul.eq_pr1_mk,-mul.eq_pr2_mk]}
  end

definition mul.to_prod {m n : nat} : fin (m * n) → prod (fin m) (fin n) :=
  mul.rec prod.mk

definition mul.of_prod {m n : nat} : prod (fin m) (fin n) → fin (m * n) :=
  prod.rec mul.mk

definition mul_equiv_prod {m n : nat} : equiv (fin (m * n)) (prod (fin m) (fin n)) :=
  equiv.mk mul.to_prod mul.of_prod
    (mul.rec (λ i j, by unfold mul.to_prod; rewrite mul.eq_rec_mk))
    (prod.rec (λ i j, by unfold mul.to_prod; unfold mul.of_prod; rewrite mul.eq_rec_mk))

-- Exponentials --

definition exp.ev {m n : nat} : fin (m ^ n) → fin n → fin m :=
  nat.rec_on n
    (λ i, elim0)
    (λ n IH i, zero_succ_cases (mul.pr2 i) (IH (mul.pr1 i)))

lemma exp.ev_zero {m n : nat} {k : fin (m ^ nat.succ n)} : exp.ev k (zero n) = mul.pr2 k := rfl

lemma exp.ev_succ {m n : nat} {k : fin (m ^ nat.succ n)} : ∀ i : fin n, exp.ev k (succ i) = exp.ev (mul.pr1 k) i
| (mk vi hi) := rfl

lemma exp.ev_mk_succ {m n : nat} {k : fin (m ^ n)} {j : fin m} {i : fin n} : @exp.ev m (nat.succ n) (mul.mk k j) (succ i) = @exp.ev m n k i :=
  by rewrite exp.ev_succ; rewrite -mul.eq_pr1_mk

definition exp.fn {m n : nat} : (fin n → fin m) → fin (m ^ n) :=
  nat.rec_on n
    (λ f, zero 0)
    (λ n IH f, mul.mk (IH (λ i : fin n, f (succ i))) (f (zero n)))

lemma exp.fn_succ {m n : nat} {f : fin (nat.succ n) → fin m} :
  exp.fn f = mul.mk (exp.fn (λ i : fin n, f (succ i))) (f (zero n)) := rfl

definition exp.eq_ev_fn {m n : nat} : ∀ f : fin n → fin m, f = exp.ev (exp.fn f) :=
  nat.induction_on n
    (take f, zero.ext)
    (take n IH f, funext (zero_succ_cases
      (begin
        rewrite exp.fn_succ,
        rewrite exp.ev_zero,
        exact !mul.eq_pr2_mk
      end)
      (begin
        intro i,
        rewrite exp.ev_succ,
        rewrite exp.fn_succ,
        rewrite -mul.eq_pr1_mk,
        rewrite -(IH (λ i : fin n, f (succ i)))
      end)))

definition exp.eq_fn_ev {m n : nat} : ∀ k : fin (m ^ n), k = exp.fn (exp.ev k) :=
  nat.induction_on n
    (by intro k; rewrite pow_zero at k; apply one.eq)
    (λ n IH k, begin
         rewrite pow_succ at k,
         revert k,
         apply mul.rec,
         intros k j,
         rewrite exp.fn_succ,
         apply congr_arg2 mul.mk,
         { rewrite (IH k),
           apply congr_arg exp.fn,
           apply funext,
           intro i,
           rewrite exp.ev_mk_succ,
           apply congr_arg2 exp.ev,
             exact IH k,
             exact rfl},
         { rewrite exp.ev_zero,
           exact !mul.eq_pr2_mk}
      end)

definition exp.rec {m n : nat} {C : (fin n → fin m) → Type} :
  (Π k : fin (m ^ n), C (exp.ev k)) →
  (Π f : fin n → fin m, C f) :=
  take Hev f, eq.rec_on (eq.symm (exp.eq_ev_fn f)) (Hev (exp.fn f))

definition exp.ext {m n : nat} {C : (fin n → fin m) → Type} {f g : Π h : fin n → fin m, C h} :
  (Π i : fin (m ^ n), f (exp.ev i) = g (exp.ev i)) → f = g :=
  take Hev, funext (exp.rec Hev)

definition exp.eq_rec_ev {m n : nat} {C : (fin n → fin m) → Type}
  {F : Π k : fin (m ^ n), C (exp.ev k)} :
  ∀ k : fin (m ^ n), exp.rec F (exp.ev k) = F k :=
  begin
    intro k,
    unfold exp.rec,
    unfold eq.rec_on,
    apply heq.to_eq,
    transitivity F (exp.fn (exp.ev k)),
    { apply eq_rec_heq},
    { apply hcongr_arg,
      rewrite -exp.eq_fn_ev}
  end

definition exp_equiv_fun {m n : nat} : equiv (fin (m ^ n)) (fin n → fin m) :=
  equiv.mk exp.ev exp.fn
    (λ k, eq.symm (exp.eq_fn_ev k))
    (λ f, eq.symm (exp.eq_ev_fn f))

end fin
