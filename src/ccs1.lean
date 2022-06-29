import auxccs 
import data.fintype.basic

open aux_ccs

inductive ccs
|simp (x : aux_ccs ℕ) : ccs
|recu (fx : aux_ccs ℕ → aux_ccs ℕ) : ccs

export ccs (simp recu)

namespace ccs

instance : decidable_eq (ccs)
  |(simp x) (simp y) := if h: x = y then is_true (h ▸ eq.refl (simp x)) 
      else is_false (λ a, ccs.no_confusion a (λ b, absurd b h))
  |(recu fx) (recu fy) := if h: (fx) = (fy) 
      then is_true (h ▸ eq.refl (recu fx))
      else is_false (λ a, ccs.no_confusion a (λ b, absurd b h))
  |(simp x) (recu fy) := is_false (λ contra, ccs.no_confusion contra)
  |(recu fx) (simp y) := is_false (λ contra, ccs.no_confusion contra)


end ccs