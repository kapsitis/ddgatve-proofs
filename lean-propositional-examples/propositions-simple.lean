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

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
Iff.intro (
  fun hPQR : p ∧ (q ∨ r) => 
  have hP : p := And.left hPQR
  have hQR : q ∨ r := And.right hPQR
  Or.elim hQR (
    fun hQ : q => 
    show (p ∧ q) ∨ (p ∧ r) from 
    Or.intro_left (p ∧ r) (And.intro hP hQ)
  )
  (
    fun hR : r => 
    show (p ∧ q) ∨ (p ∧ r) from 
    Or.intro_right (p ∧ q) (And.intro hP hR)
  )
)
(
  fun hPQPR : (p ∧ q) ∨ (p ∧ r) => 
  Or.elim hPQPR (
    fun hPQ : p ∧ q =>
    have hP : p := And.left hPQ
    have hQ : q := And.right hPQ 
    show p ∧ (q ∨ r) from 
    And.intro hP (Or.intro_left r hQ)
  )
  (
    fun hPR : p ∧ r => 
    have hP : p := And.left hPR
    have hR : r := And.right hPR 
    show p ∧ (q ∨ r) from 
    And.intro hP (Or.intro_right q hR)
  )
)


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
Iff.intro (
  fun hPQR : p ∨ (q ∧ r) => 
  Or.elim hPQR (
    fun hP : p => 
    have hPQ : p ∨ q := Or.intro_left q hP 
    have hPR : p ∨ r := Or.intro_left r hP 
    show (p ∨ q) ∧ (p ∨ r) from And.intro hPQ hPR 
  )
  (
    fun hQR : q ∧ r => 
    have hPorQ : p ∨ q := Or.intro_right p (And.left hQR)
    have hPorR : p ∨ r := Or.intro_right p (And.right hQR)
    show (p ∨ q) ∧ (p ∨ r) from And.intro hPorQ hPorR
  )
)
(
  fun hPQPR : (p ∨ q) ∧ (p ∨ r) => 
  have hPQ : p ∨ q := And.left hPQPR
  have hPR : p ∨ r := And.right hPQPR
  Or.elim hPQ (
    fun hP : p => 
    show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hP
  )
  (
    fun hQ : q => 
    Or.elim hPR (
      fun hP : p => 
      show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hP
    )
    (
      fun hR : r => 
      show p ∨ (q ∧ r) from Or.intro_right p (And.intro hQ hR)
    )
  )
)


example : (p → (q → r)) ↔ (p ∧ q → r) := 
Iff.intro (
  fun hP_Q_R: p → (q → r) => 
  fun hPQ : p ∧ q => 
  have hP : p := And.left hPQ
  have hQ : q := And.right hPQ
  show r from hP_Q_R hP hQ 
)
(
  fun hPQ_R : (p ∧ q → r) => 
  fun hP : p => 
  fun hQ : q => 
  have hPQ : p ∧ q := And.intro hP hQ 
  show r from hPQ_R hPQ 
)


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
Iff.intro (
  fun hPorQ_R: (p ∨ q) → r =>
  have hP_R: p → r := (
    fun hP : p => 
    have hPorQ: p ∨ q := Or.intro_left q hP
    show r from hPorQ_R hPorQ
  )
  have hQ_R: q → r := (
    fun hQ : q => 
    have hPorQ: p ∨ q := Or.intro_right p hQ
    show r from hPorQ_R hPorQ
  )
  show (p → r) ∧ (q → r) from And.intro hP_R hQ_R
)
(
  fun hPRandQR: (p → r) ∧ (q → r) => 
  fun hPorQ: p ∨ q => 
  have hPR: p → r := And.left hPRandQR 
  have hQR: q → r := And.right hPRandQR
  Or.elim hPorQ (
    fun hP: p => 
    show r from hPR hP
  )
  (
    fun hQ: q => 
    show r from hQR hQ
  ) 
)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
Iff.intro (
  fun hPQ : ¬ (p ∨ q) => 
  have hnP: ¬p := (
    fun hP : p => 
    have hPorQ : p ∨ q := Or.intro_left q hP 
    absurd hPorQ hPQ 
  )
  have hnQ: ¬q := (
    fun hQ : q => 
    have hPorQ : p ∨ q := Or.intro_right p hQ
    absurd hPorQ hPQ
  )
  show ¬p ∧ ¬q from And.intro hnP hnQ
)
(
  fun hNPandNQ : ¬p ∧ ¬q => 
  have NP : ¬p := And.left hNPandNQ
  have NQ : ¬q := And.right hNPandNQ
  show ¬(p ∨ q) from (
    fun PorQ : p ∨ q => 
    Or.elim PorQ (
      fun P : p => absurd P NP
    )
    (
      fun Q : q => absurd Q NQ
    )
  )
)



example : ¬p ∨ ¬q → ¬(p ∧ q) := 
fun hNPorNQ : ¬p ∨ ¬q => 
Or.elim hNPorNQ (
  fun hNP : ¬p => 
  show ¬(p ∧ q) from (
    fun PandQ: p ∧ q => 
    absurd (And.left PandQ) hNP
  )
)
(
  fun hNQ : ¬q => 
  show ¬(p ∧ q) from (
    fun PandQ: p ∧ q => 
    absurd (And.right PandQ) hNQ
  )
)


example : ¬(p ∧ ¬p) := 
fun hPandNP: p ∧ ¬p => 
absurd (And.left hPandNP) (And.right hPandNP) 



example : p ∧ ¬q → ¬(p → q) := 
fun hPandNQ : p ∧ ¬q => 
have hP: p := And.left hPandNQ
have hNQ : ¬q := And.right hPandNQ 
show ¬(p → q) from (
  fun hP_Q : p → q =>
  absurd (hP_Q hP) hNQ
) 

example : ¬p → (p → q) := (
  fun hNP: ¬p => 
  fun hP: p => 
  show q from absurd hP hNP
)


example : (¬p ∨ q) → (p → q) := 
fun hNPorQ : ¬ p ∨ q => 
fun hP : p => 
Or.elim hNPorQ (
  fun hNP : ¬p => 
  show q from absurd hP hNP
)
(
  fun hQ : q => 
  show q from hQ
)

example : p ∨ False ↔ p := 
Iff.intro (
  fun hPorFALSE: p ∨ False => 
  Or.elim hPorFALSE (
    fun hP : p => 
    show p from hP 
  )
  (
    fun hFALSE: False =>
    show p from False.elim hFALSE
  )
)
(
  fun hP : p => 
  show p ∨ False from Or.intro_left False hP
)


example : p ∧ False ↔ False := 
Iff.intro (
  fun hPandFALSE : p ∧ False => 
  show False from And.right hPandFALSE
)
(
  fun hFALSE: False => 
  show p ∧ False from False.elim hFALSE
)

example : (p → q) → (¬q → ¬p) := 
fun hP_Q: p → q => 
fun hnQ: ¬q => 
show ¬p from (
  fun hP : p => 
  have hQ : q := hP_Q hP 
  absurd hQ hnQ
)

