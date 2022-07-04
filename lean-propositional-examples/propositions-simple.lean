/-
https://leanprover.github.io/theorem_proving_in_lean4/propositions_and_proofs.html?search=
-/
variable {p q r : Prop}


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

