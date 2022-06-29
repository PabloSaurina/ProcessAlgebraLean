universes u v  

mutual inductive ccs, fccs (lab: Type u) 
with ccs : Type u
|zer : ccs
|ap (a : lab) (p : ccs): ccs
|pq (p q : ccs) : ccs -- Paralelo
|psq (p q : ccs) : ccs -- Suma
|re (f : fccs) : ccs -- Recursivo
with fccs : Type u
|var : fccs 
|ax (a : lab) (x : fccs) : fccs
|xq (x : fccs) (q : ccs) : fccs
|px (p : ccs) (x : fccs) : fccs
|xx (x y: fccs) : fccs
|xsq (x : fccs) (q : ccs) : fccs
|psx (p : ccs) (x : fccs) : fccs
|xsx (x y: fccs) : fccs

export ccs (zer ap pq psq re)
export fccs (var ax xq px xx xsq psx xsx)

namespace ccs

-- No vamos a definir la igualdad, por lo menos en principio.
-- Igual es más sencillo definir una relación de equivalencia
-- para ahorrarnos definir las igualdades con f(ccs).

variables {lab : Type u} [decidable_eq lab]

def r : ccs ℕ := zer 
 


mutual def sumandos, fsumandos
with sumandos: ccs lab → set (ccs lab)
|(psq p q) := set.union (sumandos p) (sumandos q)
|(re x) := fsumandos x
|a := {a}
with fsumandos: fccs lab → set (ccs lab)
|a := {re a}

def equivalence_relation: ccs lab → ccs lab → Prop
|zer zer := tt
|(ap a p) (ap b q) := if (a = b) then equivalence_relation p q else ff
|(pq p q) (pq r s) := equivalence_relation p r ∧ equivalence_relation q s
|(psq p q) (psq r s) := equivalence_relation p r ∧ equivalence_relation q s
|(re (var)) (re (var)) := tt
|(re (ax a x)) (re (ax b y)) := if a = b then equivalence_relation (re x)
  (re y) else ff
|(re (xq x q)) (re (xq y p)) := equivalence_relation (re x) (re y) ∧ 
  equivalence_relation q p
|(re (px p x)) (re (px q y)) := equivalence_relation (re x) (re y) ∧ 
  equivalence_relation p q
|(re (xx x y)) (re (xx z w)) := equivalence_relation (re x) (re z) ∧ 
  equivalence_relation (re y) (re w)
|(re (xsq x q)) (re (xsq y p)) := equivalence_relation (re x) (re y) ∧ 
  equivalence_relation q p
|(re (psx p x)) (re (psx q y)) := equivalence_relation (re x) (re y) ∧ 
  equivalence_relation p q
|(re (xsx x y)) (re (xsx z w)) := equivalence_relation (re x) (re z) ∧ 
  equivalence_relation (re y) (re w)
|_ _ := ff 


-- Definimos las funciones asociadas a los símbolos usuales para ccs

def add : ccs lab → ccs lab → ccs lab
|a b := psq a b

def par : ccs lab → ccs lab → ccs lab
|a b := pq a b

def lab_tran : lab → ccs lab → ccs lab
|a p := ap a p

-- Definimos las mismas funciones pero para fccs

def fadd : fccs lab → ccs lab → fccs lab
|a b := xsq a b

def addf : ccs lab → fccs lab → fccs lab
|a b := psx a b

def faddf : fccs lab → fccs lab → fccs lab
|a b := xsx a b


def fpar : fccs lab → ccs lab → fccs lab
|a b := xq a b

def parf : ccs lab → fccs lab → fccs lab
|a b := px a b

def fparf : fccs lab → fccs lab → fccs lab
|a b := xx a b


def flab_tran : lab → fccs lab → fccs lab
|a p := ax a p

-- Asignamos ahora a cada símbolo su función

infix ` + `:50 := ccs.add
infix ` + `:50 := ccs.fadd
infix ` + `:50 := ccs.addf
infix ` + `:50 := ccs.faddf

infix ` ∣ `:50 := ccs.par
infix ` ∣ `:50 := ccs.fpar
infix ` ∣ `:50 := ccs.parf
infix ` ∣ `:50 := ccs.fparf

infix ` . `:55 := ccs.lab_tran 
infix ` . `:55 := ccs.flab_tran 

-- Comprobamos que las asignaciones de símbolos funcionen correctamente

#check (1 . zer : ccs ℕ)
#check (zer ∣ zer : ccs lab)
#check re var 
#check (re (var + zer) ∣ 1 . zer : ccs ℕ) 
#check (re ((re (var + zer) ∣ 1 . zer : ccs ℕ) + var) : ccs ℕ)

-- Comprobamos que la relación de equivalencia funcione correctamente

#reduce equivalence_relation (1 . zer) (re (var + zer)) 
#reduce equivalence_relation (1 . zer) (1 . zer) 

infix ` ↔ `: 40 := ccs.equivalence_relation

#reduce (1 . zer) ↔ (1 . zer) 
#reduce re (var) ↔ re (var)
#reduce re (var) ↔ (re var) + (re var)

end ccs