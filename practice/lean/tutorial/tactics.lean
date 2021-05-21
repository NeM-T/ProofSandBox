example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
begin
  split; try {split}, 
    left, assumption,
    right, left, assumption,
    right, right, assumption
end
