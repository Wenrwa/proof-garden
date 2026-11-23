/-!
# Cantor's theorem

There is no way to list all subsets of a set using the set's own elements:
for any map `f` from a type `α` to its subsets, some subset is missed.
(The subset `{a | a ∉ f a}` cannot be `f a` for any `a`.)
-/

namespace ProofGarden

/-- No function from a type to its powerset (`α → Prop`) is surjective:
there is always a subset `s` that `f` never hits. -/
theorem cantor {α : Type} (f : α → (α → Prop)) :
    ¬ ∀ s : α → Prop, ∃ a, f a = s := by
  intro h
  -- the diagonal set `{x | ¬ f x x}`
  obtain ⟨a, ha⟩ := h (fun x => ¬ f x x)
  -- `ha : f a = fun x => ¬ f x x`, so evaluating at `a` gives `f a a = ¬ f a a`
  have h1 : f a a = ¬ f a a := congrFun ha a
  rcases Classical.em (f a a) with hp | hp
  · have hn : ¬ f a a := by
      rw [h1] at hp
      exact hp
    exact hn hp
  · have hp2 : f a a := by
      rw [h1]
      exact hp
    exact hp hp2

end ProofGarden
