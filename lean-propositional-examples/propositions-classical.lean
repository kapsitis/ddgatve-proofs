open Classical

variable (p q r s : Prop)
#check em p

-- Double negation elimination
theorem dne: ¬¬p → p :=
  (fun h: ¬¬ p =>
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h))

#print dne

theorem demorgan_neg_and :  ¬(p ∧ q) → ¬p ∨ ¬q :=
  (fun h: ¬ (p ∧ q) => 
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp))

#print demorgan_neg_and







example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
fun hP_RorS: p → r ∨ s => 
Or.elim (em p) (
  fun hP: p => 
  have hRorS : r ∨ s := hP_RorS hP
  Or.elim hRorS (
    fun hR : r => 
    have hP_R : p → r := fun hP => hR
    show  (p → r) ∨ (p → s) from Or.intro_left (p → s) hP_R
  )
  (
    fun hS : s => 
    have hP_S : p → s := fun hP => hS 
    show (p → r) ∨ (p → s) from Or.intro_right (p → r) hP_S
  )
)
(
  fun hNP: ¬p => 
  have hP_R : p → r := (
    fun hP : p => 
    absurd hP hNP
  ) 
  show  (p → r) ∨ (p → s) from Or.intro_left (p → s) hP_R
)


example : ¬(p ∧ q) → ¬p ∨ ¬q := 
fun hnPQ: ¬(p ∧ q) =>
Or.elim (em p) (
  fun hP : p => 
  have hNQ: ¬q := (
    fun hQ : q => 
    have hPandQ : p ∧ q := And.intro hP hQ
    absurd hPandQ hnPQ 
  )
  show ¬p ∨ ¬q from (Or.intro_right (¬p) hNQ)
) 
(
  fun hNP : ¬p => 
  show ¬p ∨ ¬q from Or.intro_left (¬q) hNP  
)


example : ¬(p → q) → p ∧ ¬q := 
fun hnP_Q : ¬(p → q) => 
  Or.elim (em p) (
    fun hP : p => 
    have hnQ : ¬q := (
      fun hQ : q => 
      have hP_Q : p → q := (fun dummy: p => hQ)
      absurd hP_Q hnP_Q
    )
    show p ∧ ¬q from And.intro hP hnQ
  ) 
  (
    fun hnP : ¬p => 
    have hP_Q : p → q := (
      fun hP : p => 
      absurd hP hnP
    )
    absurd hP_Q hnP_Q
  )


example : (p → q) → (¬p ∨ q) := 
fun hP_Q : p → q => 
Or.elim (em p) (
  fun hP : p => 
  have hQ : q := hP_Q hP 
  show ¬p ∨ q from Or.intro_right (¬p) hQ 
)
(
  fun hnP : ¬p => 
  show ¬p ∨ q from Or.intro_left q hnP
)


example : (¬q → ¬p) → (p → q) := 
fun hnQ_nP: ¬q → ¬p => 
fun hP: p =>
Or.elim (em q) (
  fun hQ : q => 
  show q from hQ
)
(
  fun hnQ : ¬q => 
  absurd hP (hnQ_nP hnQ)
)

example : p ∨ ¬p := (em p)



theorem contra_positive1 : (p → q) → (¬q → ¬p) := 
fun hP_Q: p → q => 
fun hnQ: ¬q =>
have hnP : ¬p := (
  fun hP : p => 
  have hQ : q := hP_Q hP
  absurd hQ hnQ
)
show ¬p from hnP



theorem peirce_law : (((p → q) → p) → p) := 
fun hPQP: ((p → q) → p) => 
Or.elim (em p) (
  fun hP : p => 
  show p from hP
)
(
  fun hnP : ¬p => (
    suffices hPQ : p → q from hPQP hPQ
    show p → q from (
      fun hP :p => 
      absurd hP hnP 
    )
  )
)

#print peirce_law



example : ¬(p ↔ ¬p) := (
  fun hPnP : p ↔ ¬ p => 
  have hP_nP : p → ¬ p := Iff.mp hPnP
  have hnP_P : ¬ p → p := Iff.mpr hPnP
  have hnP : ¬ p := (
    fun hP: p => 
    have hnP: ¬p := hP_nP hP
    absurd hP hnP
  )
  have hP: p := hnP_P hnP 
  absurd hP hnP
)
