/-
https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html?search=
-/
variable (p q r : Prop)


theorem id_P : p → p :=
  fun hp : p =>
  show p from hp 

#print id_P


theorem imp_trans : (p → q) → (q → r) → p → r :=
  fun hPQ : p → q => 
  fun hQR : q → r => 
  fun hP : p => 
  show r from hQR (hPQ hP)

#print imp_trans 



theorem and_comm : (p ∧ q) → (q ∧ p) :=
  (fun hPandQ : p ∧ q => 
  have hP : p := And.left hPandQ 
  have hQ : q := And.right hPandQ
  show q ∧ p from And.intro hQ hP)

#print and_comm


theorem or_comm : (p ∨ q) → (q ∨ p) :=
  (fun hPorQ : p ∨ q => 
  Or.elim hPorQ (
    fun hP : p =>
      show q ∨ p from Or.intro_right q hP
  )
  (
    fun hQ : q => 
      show q ∨ p from Or.intro_left p hQ

  ))

#print or_comm


theorem noncon : ¬ (p ∧ ¬ p) := 
  (fun hPandNotP: (p ∧ ¬ p) => 
  have hP : p := And.left hPandNotP
  have hNotP : ¬p := And.right hPandNotP
  absurd hP hNotP)

#print noncon 


theorem modus_ponens : p → (p → q) → q := 
  (fun hP : p => 
  fun hP_Q : p → q => 
  show q from hP_Q hP)

#print modus_ponens



theorem cond_ident : (¬ p ∨ q) → (p → q) := 
  (
    fun hNP_Q : ¬ p ∨ q => 
    fun hP : p => 
    Or.elim hNP_Q (
      fun hNP : ¬ p => 
      absurd hP hNP
    )
    (
      fun hQ : q => 
      show q from hQ
    )
  )

#print cond_ident

theorem prob3a : (p ∧ q) → (p ∨ r) :=
  fun hPandQ : p ∧ q => 
  have hP := And.left hPandQ 
  show p ∨ r from Or.intro_left r hP 

#print prob3a


theorem prob3b : p → (q → p) := 
  fun hP : p => 
  fun hQ : q => 
  show p from hP

#print prob3b




example : p ∧ q ↔ q ∧ p := 
  Iff.intro (
    fun hPQ : p ∧ q => 
    have hP := And.left hPQ 
    have hQ := And.right hPQ
    show q ∧ p from And.intro hQ hP 
  )
  (
    fun hQP : q ∧ p => 
    have hQ := And.left hQP
    have hP := And.right hQP
    show p ∧ q from And.intro hP hQ
  )



example : p ∨ q ↔ q ∨ p := 
  Iff.intro (
    fun hPQ : p ∨ q => 
    Or.elim hPQ (
      fun hP : p => 
      show q ∨ p from Or.intro_right q hP
    )
    (
      fun hQ: q => 
      show q ∨ p from Or.intro_left p hQ
    )
  )
  (
    fun hQP : q ∨ p => 
    Or.elim hQP (
      fun hQ : q => 
      show p ∨ q from Or.intro_right p hQ
    )
    (
      fun hP : p => 
      show p ∨ q from Or.intro_left q hP
    )
  )

example: (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro (
    fun hPQR :  (p ∧ q) ∧ r => 
    have hP := (And.left (And.left hPQR))
    have hQ := (And.right (And.left hPQR))
    have hR := And.right hPQR
    show p ∧ (q ∧ r) from 
    And.intro hP (And.intro hQ hR)
  )
  (
    fun hPQR : p ∧ (q ∧ r) => 
    have hP := (And.left hPQR)
    have hQ := (And.left (And.right hPQR))
    have hR := (And.right (And.right hPQR))
    show (p ∧ q) ∧ r from
    And.intro (And.intro hP hQ) hR
  )


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro (
    fun hPQR : (p ∨ q) ∨ r => 
    Or.elim hPQR (
      fun hPQ : (p ∨ q) => 
      Or.elim hPQ (
        fun hP : p => 
        show  p ∨ (q ∨ r) from Or.intro_left (q ∨ r) hP
      )
      (
        fun hQ : q => 
        show p ∨ (q ∨ r) from 
        Or.intro_right p (Or.intro_left r hQ)
      )
    )
    (
      fun hR : r => 
      show p ∨ (q ∨ r) from 
        Or.intro_right p (Or.intro_right q hR) 
    )
  )
  (
    fun hPQR : p ∨ (q ∨ r) => 
    Or.elim hPQR (
      fun hP : p => 
      show (p ∨ q) ∨ r from 
      Or.intro_left r (Or.intro_left q hP)
    )
    (
      fun hQR : q ∨ r => 
      Or.elim hQR (
        fun hQ : q => 
        show (p ∨ q) ∨ r from 
        Or.intro_left r (Or.intro_right p hQ)
      )
      (
        fun hR : r => 
        show (p ∨ q) ∨ r from 
        Or.intro_right (p ∨ q) hR
      )
    )
  )



