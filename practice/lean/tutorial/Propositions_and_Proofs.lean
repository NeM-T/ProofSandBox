namespace hidden

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
iff.intro
  (assume h: p ∧ q,
    show q ∧ p, from and.intro (and.right h) (and.left h))
  (assume h: q ∧ p,
    show p ∧ q, from and.intro (and.right h) (and.left h))


example : p ∨ q ↔ q ∨ p := 
iff.intro
  (assume h: p ∨ q,
    h.elim
      (assume hp: p, or.inr hp)
      (assume hq: q, or.inl hq)
    )
  (assume h: q ∨ p,
    h.elim
      (assume hq: q, or.inr hq)
      (assume hp: p, or.inl hp)
    )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  iff.intro
    (assume h: (p ∧ q) ∧ r,
      show p ∧ (q ∧ r), 
        from and.intro (and.left (and.left h)) (and.intro (and.right(and.left h)) (and.right h) ) )
    (assume h: p ∧ (q ∧ r),
      show (p ∧ q) ∧ r, 
        from and.intro (and.intro (and.left h) (and.left (and.right h)) ) (and.right (and.right h)) )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (assume h: (p ∨ q) ∨ r,
      h.elim 
        (assume hpq: p ∨ q,
          hpq.elim 
            (assume hp: p, or.inl hp)
            (assume hq: q, or.inr (or.inl hq)))
        (assume hr: r, or.inr (or.inr hr) ) )
    (assume h: (p ∨ (q ∨ r)), 
        h.elim 
          (assume hp: p, or.inl (or.inl hp))
          (assume hqr: q ∨ r,
            hqr.elim 
              (assume hq: q, or.inl (or.inr hq) )
              (assume hr: r, or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (assume pqr: p ∧ (q ∨ r),
        (and.right pqr).elim
          (assume hq: q, or.inl (and.intro (and.left pqr) hq ))
          (assume hr: r, or.inr (and.intro (and.left pqr) hr)))
    (assume pqpr: (p ∧ q) ∨ (p ∧ r), 
         pqpr.elim 
         (assume pq: p ∧ q, and.intro (and.left pq) (or.inl (and.right pq)))
         (assume pr: p ∧ r, and.intro (and.left pr) (or.inr (and.right pr))))


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  iff.intro
    (assume pqr: p ∨ (q ∧ r),
      pqr.elim
        (assume hp: p, and.intro (or.inl hp)(or.inl hp)) 
        (assume qr: q ∧ r, and.intro (or.inr (and.left qr)) (or.inr (and.right qr))))
    (assume pqpr: (p ∨ q) ∧ (p ∨ r), 
      (and.left pqpr).elim
        (assume hp: p, or.inl hp)
        (assume hq: q,
          (and.right pqpr).elim
            (assume hp: p, or.inl hp)
            (assume hr: r, or.inr (and.intro hq hr ))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  iff.intro
    (assume h: p → (q → r), assume pq : p ∧ q, show r, from h (and.left pq)( and.right pq) )
    (assume h: p ∧ q → r, assume hp: p, assume hq: q, show r, from h (and.intro hp hq))


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro
    (assume h: (p ∨ q) → r,
      and.intro (assume hp: p, show r, from h (or.inl hp)) (assume hq: q, show r, from h (or.inr hq)))
    (assume h: (p → r) ∧ (q → r), assume pq: p ∨ q,
      pq.elim
        (assume hp: p, show r, from (and.left h) hp )
        (assume hq: q, show r, from (and.right h) hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro
    (assume h: ¬ (p ∨ q),
      and.intro 
        (assume hp: p, show false, from h (or.inl hp))
        (assume hq: q, show false, from h (or.inr hq)))
    (assume h: ¬ p ∧ ¬q, assume pq: p ∨ q,
      pq.elim
      (assume hp: p, show false, from (and.left h) hp)
      (assume hq: q, show false, from (and.right h) hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  assume poq : ¬ p ∨ ¬ q, assume paq: p ∧ q,
  poq.elim
  (assume hp: ¬p, show false, from hp (and.left paq))
  (assume hq: ¬q, show false, from hq (and.right paq))

example : ¬(p ∧ ¬p) :=
  assume h: p ∧ ¬p, show false, from (and.right h) (and.left h)

example : p ∧ ¬q → ¬(p → q) :=
  assume paq : p ∧ ¬q, assume h: p → q,
  show false, from (and.right paq) (h (and.left paq))

example : ¬p → (p → q) :=
  assume np : ¬p, assume hp: p,
  absurd hp np

example : (¬p ∨ q) → (p → q) :=
  assume npq : ¬p ∨ q, assume hp: p,
  npq.elim
    (assume np: ¬p, absurd hp np)
    (assume hq: q, show q, from hq)

example : p ∨ false ↔ p :=
  iff.intro
    (assume pf: p ∨ false,
      pf.elim 
        (assume hp: p, show p, from hp) (assume F: false, false.elim F))
    (assume hp: p, or.inl hp)

example : p ∧ false ↔ false :=
  iff.intro
    (assume pf: p ∧ false, show false, from and.right pf)
    (assume F: false, false.elim F)

example : (p → q) → (¬q → ¬p) :=
  assume pq: p → q, assume nq: ¬ q, assume hp : p,
  show false, from nq (pq hp)

end hidden
