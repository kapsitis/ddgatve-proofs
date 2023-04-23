variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
Iff.intro (
  fun h1: (∀ x, p x ∧ q x) => 
  fun hX: α => 
  have h2: (p hX) := (h1 hX).left
  have h3: (q hX) := (h1 hX).right
  show ((∀ x, p x) ∧ (∀ x, q x)) from And.intro h2 h3
)
(

)
 


 example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
 example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry