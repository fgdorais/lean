open tactic

lemma ex1 : let x := 1 in ∀ y, x = y → y = 1 :=
by using_smt $ smt_tactic.intros >> get_local `x >>= (fun a, trace a)

open tactic_result

meta def fail_if_success {α : Type} (t : smt_tactic α) : smt_tactic unit :=
λ ss ts, match t ss ts with
| success _ _                         := failed ts
| exception .(α × smt_state) _ _ _ := success ((), ss) ts
end

def my_pre_config : smt_pre_config :=
{ default_smt_pre_config with zeta := tt }

def my_smt_config : smt_config :=
{ default_smt_config with pre_cfg := my_pre_config }

lemma ex2 : let x := 1 in ∀ y, x = y → y = 1 :=
by using_smt_core my_smt_config $ smt_tactic.intros >> fail_if_success (get_local `x) >> return ()
