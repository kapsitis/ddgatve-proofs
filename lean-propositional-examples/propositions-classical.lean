open Classical

variable {p q r: Prop}
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



theorem peirce_law : ((p → q) → p) → p := 
  fun hPQP : (p → q) → p => 
  Or.elim (em p)
  (fun hP : p => 
    show p from hP
  )
  (fun hNegP: ¬ p =>
    (
      suffices hPQ : p → q from hPQP hPQ
      show p → q from (
        fun hP: p => 
        absurd hP hNegP
      )
    ) 
  )

#print peirce_law

