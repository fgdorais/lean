lemma ex1 (a b : Prop) : a ∧ b ∧ b → b ∧ a :=
and.rec (λ ha hb hb, ha)

@[elab_as_eliminator]
def bogus_elim {A : Type} {C : A → A → Prop} {a b : A} (h : C a a) : C a b :=
sorry

lemma ex2 (a b : Prop) : a ∧ b :=
bogus_elim trivial

lemma ex1 (a b : Prop) : a ∧ b ∧ b → b ∧ a :=
λ h, and.rec
       (λ ha hb, ha + hb)
       h
