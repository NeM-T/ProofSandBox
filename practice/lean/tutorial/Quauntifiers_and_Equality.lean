namespace hidden
open classical

variables (α : Type*) (p q : α → Prop)
variable a : α
variable r : Prop

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨w, hw⟩ := ⟨w, hw.right, hw.left⟩
end

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
by_contradiction
  (assume h1 : ¬ ∃ x, p x,
    have h2 : ∀ x, ¬ p x, from
      assume x,
      assume h3 : p x,
      have h4 : ∃ x, p x, from  ⟨x, h3⟩,
      show false, from h1 h4,
    show false, from h h2)

example : (∃ x : α, r) → r :=
  assume h: ∃ x:α, r,
  exists.elim h
  (assume w, assume hr: r, show r, from hr)

example : r → (∃ x : α, r) :=
  assume hr: r, exists.intro a hr 

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro
  (assume h: ∃ x, p x ∧ r, 
    show (∃ x, p x) ∧ r , from exists.elim h
      (assume w: α, assume pwr : p w ∧ r,
        and.intro (show ∃ x, p x, from exists.intro w pwr.left) pwr.right))
  (assume h: (∃ x, p x) ∧ r,
    exists.elim h.left
      (assume w: α, assume pw : p w, exists.intro w (and.intro pw h.right)))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  iff.intro
  (assume h: ∃ x, p x ∨ q x, 
    exists.elim h
    (assume a: α, assume pq: p a ∨ q a,
      or.elim pq
      (assume pa: p a, or.inl (exists.intro a pa))
      (assume qa: q a, or.inr (exists.intro a qa))))
  (assume h: (∃ x, p x) ∨ (∃ x, q x), 
    or.elim h
    (assume h1: ∃ x, p x,
      exists.elim h1
        (assume a, assume pa: p a, 
          show ∃ x, p x ∨ q x, from exists.intro a (or.inl pa)))
    (assume h1: ∃ x, q x,
      exists.elim h1
        (assume a, assume qa: q a,
          show ∃ x,p x ∨ q x, from exists.intro a (or.inr qa))))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  iff.intro
  (assume h: (∀ x, p x), assume h1: (∃ x, ¬ p x),
    exists.elim h1
      (assume a: α, assume npa: ¬ p a, show false, from npa (h a)))
  (assume h: ¬ (∃ x, ¬ p x), assume x: α,
    by_contradiction
      (assume npx: ¬ p x, 
        show false, from h (exists.intro x npx)))
        
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
  (assume ⟨a, (h1 : p a ∨ q a)⟩,
    or.elim h1
      (assume hpa : p a, or.inl ⟨a, hpa⟩)
      (assume hqa : q a, or.inr ⟨a, hqa⟩))
  (assume h : (∃ x, p x) ∨ (∃ x, q x),
    or.elim h
      (assume ⟨a, hpa⟩, ⟨a, (or.inl hpa)⟩)
      (assume ⟨a, hqa⟩, ⟨a, (or.inr hqa)⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
iff.intro
  (assume h: ∃ x, p x, assume h1: ∀ x, ¬ p x,
    exists.elim h
      (assume a, assume pa: p a,
        show false, from h1 a pa))
  (assume h: ¬ ∀ x, ¬ p x,
    by_contradiction
      (assume h1: ¬ ∃ x, p x,
        show false, from h 
          (assume x: α, assume px: p x,
            show false, from h1 (exists.intro x px))))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
iff.intro
  (assume h: ¬ ∃ x, p x, assume x: α, assume px: p x,
    show false, from h (exists.intro x px))
  (assume h: ∀ x, ¬ p x, assume h1: ∃ x, p x,
    exists.elim h1
      (assume a: α, assume pa: p a,
        show false, from h a pa))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
iff.intro
  (assume h: ¬ ∀ x, p x,
    by_contradiction
      (assume h1 :¬ ∃ x, ¬ p x, 
        show false, from h 
          (assume x, 
            by_contradiction
              (assume h2: ¬ p x,
                show false, from h1
                  (exists.intro x h2)))))
  (assume h: ∃ x, ¬ p x, assume h1: ∀ x, p x,
    exists.elim h
      (assume a:α, assume npa: ¬ p a,
        show false, from npa (h1 a)))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
iff.intro
  (assume h: ∀ x, p x → r, assume h1: ∃ x, p x,
    exists.elim h1
      (assume a, assume pa: p a,
        show r, from h a pa))
  (assume h: (∃ x, p x) → r, assume x, assume px: p x,
    show r, from h (exists.intro x px))

end hidden

variables (α : Type*) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (assume h: ∀ x, p x ∧ q x,
    show (∀ x, p x) ∧ (∀ x, q x), 
      from and.intro (assume x, (h x).left ) (assume x, (h x).right))
  (assume h: (∀ x, p x) ∧ (∀ x, q x), assume x,
    and.intro (h.left x) (h.right x))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  assume h: ∀ x, p x → q x, assume h1: ∀ x, p x, assume x,
    show q x, from h x (h1 x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  assume h: (∀ x, p x) ∨ (∀ x, q x), assume x,
    h.elim
    (assume h1 : ∀ x, p x,
      show p x ∨ q x, from or.inl (h1 x))
    (assume h2: ∀ x, q x,
      show p x ∨ q x, from or.inr (h2 x))
