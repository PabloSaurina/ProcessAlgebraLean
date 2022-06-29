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
|sus (f : fccs) (id : ids) (p : ccs) : ccs -- Sustitucion, id variable a sustituir
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
|fsus (f : fccs) (id : ids) (p : ccs) : fccs
|fre (f : fccs) (id : ids) : fccs

export ccs (zer ap pq psq sus re)
export fccs (var ax xq px xx xsq psx xsx fsus fre)

namespace ccs

variables {lab ids: Type u} [decidable_eq lab] [decidable_eq ids]

-- Por como hemos definido ccs, necistamos ahora una funcion que nos permira reconocer si
-- de verdad es un ccs o no.

-- Para esto, primero necesitamos ser capaces de identificar si todas la variables han sido 
-- asignadas.

#check  ({1} : set ℕ)
#reduce 1 ∈ ({1,1} \ {2,3} :set ℕ)
#reduce 1 ∈ ({3} ∪ ({1,2} \ {2}) : set ℕ)

def variables_sin_asignar: fccs lab ids → set ids
|(var id) := {id}
|(ax a x) := variables_sin_asignar x
|(xq x q) := variables_sin_asignar x
|(px p x) := variables_sin_asignar x
|(xx x y) := (variables_sin_asignar x) ∪ (variables_sin_asignar y)
|(xsq x q) := variables_sin_asignar x
|(psx p x) := variables_sin_asignar x
|(xsx x y) := (variables_sin_asignar x) ∪ (variables_sin_asignar y)
|(fsus f id p) := (variables_sin_asignar f) \ {id}
|(fre f id) := (variables_sin_asignar f) \ {id}

-- Aplicamos esta propiedad para definir ya cuando un ccs tiene todas la variables asignadas


mutual def variables_asignadas, fvariables_asignadas
with variables_asignadas : ccs lab ids → Prop 
|zer := tt
|(ap a p) := variables_asignadas p
|(pq p q) := (variables_asignadas p) ∧ (variables_asignadas q)
|(psq p q) := (variables_asignadas p) ∧ (variables_asignadas q)
|(sus f id p) := (((variables_sin_asignar f) \ {id}) = ∅) ∧ (variables_asignadas p)
|(re f id) := ((variables_sin_asignar f) \ {id}) = ∅ 
with fvariables_asignadas : fccs lab ids → Prop
|(var id) := tt
|(ax a x) := fvariables_asignadas x
|(xq x q) := (variables_asignadas q) ∧ (fvariables_asignadas x)
|(px p x) := (variables_asignadas p) ∧ (fvariables_asignadas x)
|(xx x y) := (fvariables_asignadas x) ∧ (fvariables_asignadas y)
|(xsq x q) := (variables_asignadas q) ∧ (fvariables_asignadas x) 
|(psx p x) := (variables_asignadas p) ∧ (fvariables_asignadas x) 
|(xsx x y) := (fvariables_asignadas x) ∧ (fvariables_asignadas y)
|(fsus f id p) := (variables_asignadas p) ∧ (fvariables_asignadas f)
|(fre f id) := fvariables_asignadas f

#check (re (psx (re (xsx (var 2) (var 1)) 1) (var 2)) 2)
#check variables_asignadas (re (psx (re (xsx (var 2) (var 1)) 1) (var 2)) 2)
-- #eval variables_asignadas (re (psx (re (xsx (var 2) (var 1)) 1) (var 2)) 2 : ccs ℕ ℕ)

#check (((variables_sin_asignar (var 2)) \ {2}) = ∅)


-- OTRA VERSION DE VARIABLES ASIGNADAS

def aux : set ℕ := {0,1,2,3}
def aux2 : set ℕ := {}

#check aux
#check aux2
#check cardinal.mk aux 
#check cardinal.mk aux2
#reduce cardinal.mk aux = cardinal.mk aux2
#reduce cardinal.mk aux2 = cardinal.mk ({} : set ℕ)
#check cardinal.mk aux + cardinal.mk aux2
#reduce (cardinal.mk aux2 + cardinal.mk aux) = 4

def variables_asignadas2: ccs lab ids → cardinal 
|zer := 0
|(ap a p) := variables_asignadas2 p
|(pq p q) := (variables_asignadas2 p) + (variables_asignadas2 q)
|(psq p q) := (variables_asignadas2 p) + (variables_asignadas2 q)
|(sus f id p) := (cardinal.mk ((variables_sin_asignar f) \ {id} : set ids)) 
  + (variables_asignadas2 p)
|(re f id) := cardinal.mk ((variables_sin_asignar f) \ {id} : set ids)

-- La definición de buffer1 intenta emular B₀¹ del libro:
-- Reactive Systems: Modelling, Specification and Verification

def buffer1 : ccs string ℕ := re (ax "in" (ax "out" (var 0))) 0

-- La definición de buffer2 intenta emular (B₀¹ | B₀¹)

def buffer2 : ccs string ℕ := pq buffer1 buffer1

-- La definición de buffer2_2 intenta emular b₀² 

def buffer2_2 : ccs string ℕ := re (ax "in" (fre (xsx (ax "in" (ax "out" (var 1))) 
  (ax "out" (var 0))) 1)) 0

-- La definición de buffern intenta emular (B₀¹ | ... | B₀¹) 

def buffern : ℕ → ccs string ℕ
|0 := buffer1
|(nat.succ a) := pq buffer1 (buffern (a))

-- La definición de buffern_2 intenta emular (B₀ⁿ)

def buffern_aux : ℕ → ℕ → fccs string ℕ
|(nat.succ n) 0 := ax "in" (buffern_aux n 1)
|(nat.succ n) k := xsx  (fre (ax "in" (buffern_aux n (k+1))) k) (ax "out" (var (k-1)))
|0 k := (ax "out" (var (k-1)))

def buffern_2 : ℕ → ccs string ℕ
|n := re (buffern_aux n 0) 0

-- Hay que definir ~

end ccs

open ccs

-- Vamos a ver que buffer1 es realmente un ccs
#check variables_asignadas2 buffer1 = 0
#check cardinal.to_nat 0
#eval 1 + 4
#check 1 = 0

lemma buffer1.variables_asignadas : variables_asignadas2 buffer1 = 0 :=
begin
  have h₁ : re (ax "in" (ax "out" (var 0))) 0 = buffer1,
  tauto,
  have h₂ : variables_asignadas2 (re (ax "in" (ax "out" (var 0))) 0) = variables_asignadas2 buffer1,
  tauto,
  suffices s₁ : variables_asignadas2 (re (ax "in" (ax "out" (var 0))) 0) = 0,
  tauto,
  unfold_cases {refl},
  tauto,
  tauto,
  tauto,
  tauto,
  tauto,
  have h₃ : variables_asignadas2._main._pack (re f id) = 
    cardinal.mk ((variables_sin_asignar f) \ {id} : set ℕ),
  {
    admit,
  },
  {
    sorry,
  },
end

-- Probamos que B₀² ∼ (B₀¹ | B₀¹)
-- Probamos que B₀ⁿ ~ (B₀¹ | ... | B₀¹)