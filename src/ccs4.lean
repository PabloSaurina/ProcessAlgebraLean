import data.fintype.basic
import init.classical
import init.logic
import set_theory.cardinal
import tactic
import init.meta.match_tactic

universe u 

mutual inductive ccs, fccs (lab ids: Type u)
with ccs : Type u
|zer : ccs
|ap (a : lab) (p : ccs): ccs
|pq (p q : ccs) : ccs -- Paralelo
|psq (p q : ccs) : ccs -- Suma
|re (f : fccs) (id : ids) : ccs -- Recursivo, id variable a sustituir
with fccs : Type u
|var (id : ids): fccs 
|ax (a : lab) (x : fccs) : fccs
|xq (x : fccs) (q : ccs) : fccs
|px (p : ccs) (x : fccs) : fccs
|xx (x y: fccs) : fccs
|xsq (x : fccs) (q : ccs) : fccs
|psx (p : ccs) (x : fccs) : fccs
|xsx (x y: fccs) : fccs
|fre (f : fccs) (id : ids) : fccs

export ccs (zer ap pq psq re)
export fccs (var ax xq px xx xsq psx xsx fre)

namespace ccs

variables {lab ids: Type u} [decidable_eq lab] [decidable_eq ids]

-- Por como hemos definido ccs, necistamos ahora una funcion que nos permira reconocer si
-- de verdad es un ccs o no.

-- Para esto, primero necesitamos ser capaces de identificar si todas la variables han sido 
-- asignadas.

def variables_sin_asignar: fccs lab ids → set ids
|(var id) := {id}
|(ax a x) := variables_sin_asignar x
|(xq x q) := variables_sin_asignar x
|(px p x) := variables_sin_asignar x
|(xx x y) := (variables_sin_asignar x) ∪ (variables_sin_asignar y)
|(xsq x q) := variables_sin_asignar x
|(psx p x) := variables_sin_asignar x
|(xsx x y) := (variables_sin_asignar x) ∪ (variables_sin_asignar y)
|(fre f id) := (variables_sin_asignar f) \ {id}

-- Aplicamos esta propiedad para definir ya cuando un ccs tiene todas la variables asignadas

def variables_asignadas: ccs lab ids → Prop 
|zer := tt
|(ap a p) := variables_asignadas p
|(pq p q) := (variables_asignadas p) ∧ (variables_asignadas q)
|(psq p q) := (variables_asignadas p) ∧ (variables_asignadas q)
|(re f id) := ((variables_sin_asignar f) \ {id}) = ∅ 

-- Hay que definir ~ , y para ello tenemos que definir primero lo que es una transición. 

-- Antes de definir una transición definimos que elementos estan al principio de un ccs.

def add_set (S:set (ids × (ccs lab ids))) (id :ids) (p : ccs lab ids) : set (ids × (ccs lab ids))
|(a,b) := ((a,b) ∈ S ∧ a ≠ id) ∨ (a = id ∧ p = b)

def find (S:set (ids × (ccs lab ids))) (id :ids): set (ccs lab ids)
|p := (id,p)∈ S

mutual def now_proc, fnow_proc
with now_proc: ccs lab ids → set (ids × (ccs lab ids)) → (set (ccs lab ids))
|zer S := {zer}
|(ap a p) S := {}
|(pq p q) S := set.union (now_proc p S) (now_proc q S) -- Faltarian las combinaciones
|(psq p q) S := set.union (now_proc p S) (now_proc q S) -- Faltarian las combinaciones
|(re f id) S := fnow_proc f (add_set S id (re f id))
with fnow_proc: fccs lab ids → set (ids × (ccs lab ids)) → (set (ccs lab ids))
|(var id) S := find S id
|(ax a x) S := {}
|(xq x q) S := set.union (fnow_proc x S) (now_proc q S) -- Faltarian las combinaciones
|(px p x) S := set.union (now_proc p S) (fnow_proc x S) -- Faltarian las combinaciones
|(xx x y) S := set.union (fnow_proc x S) (fnow_proc y S) -- Faltarian las combinaciones
|(xsq x q) S := set.union (fnow_proc x S) (now_proc q S) -- Faltarian las combinaciones
|(psx p x) S := set.union (now_proc p S) (fnow_proc x S) -- Faltarian las combinaciones
|(xsx x y) S := set.union (fnow_proc x S) (fnow_proc y S) -- Faltarian las combinaciones
|(fre f id) S := set.union (fnow_proc f S) ({re f id})

-- Definimos ahora que significa x →ᵃ y, donde 'x' e 'y' son ccs y 'a' es lab

mutual def transition, ftransition
with transition: ccs lab ids → lab → set (ids × (ccs lab ids)) → (set (ccs lab ids))
|zer a S:= {}
|(ap a p) b S:= if a = b then set.union {p} (now_proc p S) else {}
|(pq p q) a S:= set.union (transition p a S) (transition q a S)
|(psq p q) a S:= set.union (transition p a S) (transition q a S)
|(re f id) a S:= ftransition f a (add_set S id (re f id))
with ftransition: fccs lab ids → lab → set (ids × (ccs lab ids)) → (set (ccs lab ids))
|(var id) a S := {}
|(ax a x) b S := if a = b then fnow_proc x S else {}
|(xq x q) a S := set.union (ftransition x a S) (transition q a S)
|(px p x) a S := set.union (transition p a S) (ftransition x a S)
|(xx x y) a S := set.union (ftransition x a S) (ftransition y a S)
|(xsq x q) a S := set.union (ftransition x a S) (transition q a S)
|(psx p x) a S := set.union (transition p a S) (ftransition x a S)
|(xsx x y) a S := set.union (ftransition x a S) (ftransition y a S)
|(fre f id) a S := ftransition f a S

-- Procedemos con la bisimulación fuerte

def strong_bisimulation (r₁: ccs lab ids → ccs lab ids → Prop) := ∀ x y, (∀ (a : lab) 
  (x₁ : ccs lab ids), (r₁ x y ∧ x₁ ∈ transition x a {}) → ∃ (y₁ : ccs lab ids), 
  (y₁ ∈ transition y a {} ∧ (r₁ x₁ y₁))) ∧ (∀ (b : lab) (y₁ : ccs lab ids), 
  (r₁ x y ∧ y₁ ∈ transition y b {}) → ∃ (x₁ : ccs lab ids), (x₁ ∈ transition x b {} ∧ (r₁ x₁ y₁)))

def bisimilar (x:ccs lab ids) (y:ccs lab ids) := ∃ (s:ccs lab ids → ccs lab ids → Prop), 
  (s x y) ∧ strong_bisimulation s

def bisimilar_relation: ccs lab ids → ccs lab ids → Prop
|p q := bisimilar p q

-- Vamos a asignar los símbolos usuales de ccs a nuestras definiciones
-- Para ello primero creamos unas funciones

def add : ccs lab ids → ccs lab ids→ ccs lab ids
|a b := psq a b

def par : ccs lab ids → ccs lab ids → ccs lab ids
|a b := pq a b

def lab_tran : lab → ccs lab ids → ccs lab ids
|a p := ap a p

-- Definimos las mismas funciones pero para fccs

def fadd : fccs lab ids → ccs lab ids → fccs lab ids
|a b := xsq a b

def addf : ccs lab ids → fccs lab ids → fccs lab ids
|a b := psx a b

def faddf : fccs lab ids → fccs lab ids → fccs lab ids
|a b := xsx a b


def fpar : fccs lab ids → ccs lab ids → fccs lab ids
|a b := xq a b

def parf : ccs lab ids → fccs lab ids → fccs lab ids
|a b := px a b

def fparf : fccs lab ids → fccs lab ids → fccs lab ids
|a b := xx a b


def flab_tran : lab → fccs lab ids → fccs lab ids
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

infix ` ∼ `:40 := ccs.bisimilar_relation

-- Comprobamos que las asignaciones de símbolos funcionen correctamente

#check ("input" . zer : ccs string ℕ)
#check (zer ∣ zer : ccs lab ids)
#check (re (var 1) 1: ccs ℕ ℕ)
#check (re ((var 2) + zer) 2 ∣ "action" . zer : ccs string ℕ) 
#check (re (((re ((var 0) + zer) 0 ∣ "output" . zer) : ccs string ℕ) + (var 3)) 3 : ccs string ℕ)
#check zer ∼ zer
#check ("input" . zer ∣ zer : ccs string ℕ) ∼ zer



-- La definición de buffer1 intenta emular B₀¹ del libro:
-- Reactive Systems: Modelling, Specification and Verification

def buffer1 : ccs string ℕ := re (ax "in" (ax "out" (var 0))) 0

-- La definición de buffer2 intenta emular (B₀¹ | B₀¹)

def buffer2 : ccs string ℕ := pq buffer1 buffer1

-- La definición de buffer2_2 intenta emular b₀² 

def buffer2_2 : ccs string ℕ := re (ax "in" (fre (xsx (ax "in" (ax "out" (var 1))) 
  (ax "out" (var 0))) 1)) 0

end ccs

open ccs

lemma buffer2.equivalence : buffer2 ∼ buffer2_2 :=
begin
  fconstructor,
  sorry,
  sorry,
end

