# Semantics

## Data and Types

### Names

```
vn ∈ vname ≈ symbol ⊎ {this,super}
cn ∈ cname ≈ symbol ⊎ {object}
fn ∈ fname ≈ symbol
mn ∈ mname ≈ symbol
```

### Labels

```
ς ∈ label ⩴ Public
          | Secret
```

### Types

```
τ ∈ type ⩴ int
         | bool
         | φ ⇒ φ
         | ref φ
φ ∈ stype ⩴ τ·ς
m ∈ mtype ⩴ method ⨯ τ ⨯ τ
```

### Envs

```
γ ∈ env ≜ vname ⇀ value

ℓ ∈ loc ≈ ℕ
σ ∈ store ≜ loc ⇀ value

Γ ∈ tenv ≜ var ⇀ stype
```

### Classes and Objects

```
cd ∈ cdecl ⩴ CLASS cn EXTENDS cn … cn FIELDS fd … fd ~ md … md
fd ∈ fdecl ⩴ FIELD cn τ
md ∈ mdecl ⩴ METHOD mn(x) ⇒ e

o ∈ object ⩴ OBJECT cn[o,…,o]({fn↦ℓ,…,fn↦ℓ}) {mn↦[FUN(x)⇒e],…,mn↦[FUN(x)⇒e]}
```

## Expressions

```
e ∈ expr ⩴ i | e + e | e × e | e < e | e > e | e == e
         | x | LET x = e IN e
         | FUN (x:τ) ⇒ e
         | e(e)
         | WHILE(e){e}
         | BOX(e)
         | !e
         | e ← e
         | NEW cn(e,…,e)
         | e.fn
         | e.fn ← e
         | e.mn(e)    -- all methods take exactly one argument
```

## Interpreter

```
interp ∈ list(cdecl) × env × store × expr ⇀ value × store
interp(cds,γ,σ,i) ≜ ⟨i,σ⟩
interp(cds,γ,σ,b) ≜ ⟨b,σ⟩
interp(cds,γ,σ,e₁+e₂) ≜ ⟨i₁+i₂,σ″⟩
  where ⟨i₁,σ′⟩ = interp(cds,γ,σ,e₁)
  where ⟨i₂,σ″⟩ = interp(cds,γ,σ′,e₂)
interp(cds,γ,σ,e₁+e₂) ≜ ⟨i₁×i₂,σ″⟩
  where ⟨i₁,σ′⟩ = interp(cds,γ,σ,e₁)
  where ⟨i₂,σ″⟩ = interp(cds,γ,σ′,e₂)
interp(cds,γ,σ,e₁<e₂) ≜ ⟨i₁<i₂,σ″⟩
  where ⟨i₁,σ′⟩ = interp(cds,γ,σ,e₁)
  where ⟨i₂,σ″⟩ = interp(cds,γ,σ′,e₂)
interp(cds,γ,σ,e₁>e₂) ≜ ⟨i₁>i₂,σ″⟩
  where ⟨i₁,σ′⟩ = interp(cds,γ,σ,e₁)
  where ⟨i₂,σ″⟩ = interp(cds,γ,σ′,e₂)
interp(cds,γ,σ,e₁==e₂) ≜ ⟨i₁==i₂,σ″⟩
  where ⟨i₁,σ′⟩ = interp(cds,γ,σ,e₁)
  where ⟨i₂,σ″⟩ = interp(cds,γ,σ′,e₂)
interp(γ,σ,IF e₁ THEN e₂ ELSE e₃) ≜ interp(γ,σ′,e₂)
  when ⟨true,σ′⟩ = interp(γ,σ,e₁)
interp(γ,σ,IF e₁ THEN e₂ ELSE e₃) ≜ interp(γ,σ′,e₃)
  when ⟨false,σ′⟩ = interp(γ,σ,e₁)
interp(cds,γ,σ,x) ≜ γ(x)
interp(cds,γ,σ,LET x = e₁ IN e₂) ≜ interp(cds,γ[x↦v],σ′,e₂)
  where ⟨v,σ′⟩ = interp(cds,γ,σ,e₁)
interp(γ,FUN(x)⇒e) ≜ ⟨FUN(x)⇒e,γ⟩
interp(γ,e₁(e₂)) ≜ interp(γ′[x↦v],e′)
  where ⟨FUN(x)⇒e′,γ′⟩ = interp(γ,e₁)
        v = interp(γ,e₂)
interp(γ,σ,WHILE(e₁){e₂}) ≜ ⟨true,σ′⟩
  when ⟨false,σ′⟩ = interp(γ,σ,e₁)
interp(γ,σ,WHILE(e₁){e₂}) ≜ interp(γ,σ″,WHILE(e₁){e₂})
  when ⟨true,σ′⟩ = interp(γ,σ,e₁)
          ⟨v,σ″⟩ = interp(γ,σ′,e₂)
interp(γ,σ,BOX(e)) ≜ ⟨ℓ,σ′[ℓ↦v]⟩
  where ⟨v,σ′⟩ = interp(γ,σ,e)
        ℓ = fresh-loc(σ′)
interp(γ,σ,!e) ≜ ⟨σ′(ℓ),σ′⟩
  where ⟨ℓ,σ′⟩ = interp(γ,σ,e)
interp(γ,σ,e₁ ← e₂) ≜ ⟨v,σ″[ℓ↦v]⟩
  where ⟨ℓ,σ′⟩ = interp(γ,σ,e₁)
        ⟨v,σ″⟩ = interp(γ,σ′,e₂)
interp(cds,γ,σ₀,NEW cn(e₁,…,eₙ)) ≜ ⟨OBJECT cn[o₁,…,oₜ](fn₁↦ℓ₁,…,fnₘ↦ℓₘ) {mn₁↦[FUN(x₁)⇒e₁′],…,mnₙ↦[FUN(xₙ)⇒eₙ′]},σₘ[ℓ₁↦v₁,…,ℓₘ↦vₘ]
  where ⟨v₁,σ₁⟩ = interp(cds,γ,σ₀,e₁)
                ⋮
        ⟨vₘ,σₘ⟩ = interp(cds,γ,σₘ₋₁,eₙ)
        (CLASS cn EXTENDS cn₁ … cnₒ FIELDS fn₁ … fnₘ ~ METHOD mn₁(x₁) ⇒ e₁′ … METHOD mnₙ(xₙ) ⇒ eₙ′) = cds(cn)
        ℓᵢ ≢ ℓⱼ for i ≢ j , 1 ≤ i ≤ m , 1 ≤ j ≤ m
        {ℓ₁,…,ℓₘ} ∩ dom(σₘ) = ∅
interp(cds,γ,σ,e.fn) ≜ ⟨σ(fm(fn)),σ′⟩
  where ⟨OBJECT cn(fm) mm,σ′⟩ = interp(cds,γ,σ,e)
interp(cds,γ,σ,e₁.fn ← e₂) ≜ ⟨v,σ″[fm(fn)↦v]⟩
  where ⟨OBJECT cn(fm) mm,σ′⟩ = interp(cds,γ,σ,e₁)
        ⟨v,σ″⟩ = interp(cds,γ,σ′,e₂)
interp(cds,γ,e₁.mn(e₂)) ≜ interp(cds,{x↦v,this↦o},σ″,e′)
  where ⟨o,σ′⟩ = interp(cds,γ,σ,e₁)
        (OBJECT cn(fm) mm) = o
        ⟨v,σ″⟩ = interp(cds,γ,σ′,e₂)
        ⟨x,e′⟩ = mm(mn)
```

## Type Checker

```
typecheck ∈ list(cdecl) x tenv × expr ⇀ stype

-----------
Γ ⊢ i : int·⊥

-----------
Γ ⊢ b : bool·⊥

Γ ⊢ e₁ : int·ς₁
Γ ⊢ e₂ : int·ς₂
------------
Γ ⊢ e₁ + e₂ : int·(ς₁ V ς₂)

Γ ⊢ e₁ : int·ς₁
Γ ⊢ e₂ : int·ς₂
------------
Γ ⊢ e₁ * e₂ : int·(ς₁ V ς₂)

Note: this prevents insecure *indirect* information flow
from e1 to output.
Γ ⊢ e₁ : bool·ς₁
Γ ⊢ e₂ : τ·ς₂
Γ ⊢ e₃ : τ·ς₃
ς₁ ≼ ς₂ = ς₃
--------------------------------
Γ ⊢ IF e₁ THEN e₂ ELSE e₃ : τ·(ς₁ V ς₂ V ς₃)

Γ(x) = τ·ς
--------------
Γ ⊢ x : τ·ς

Γ ⊢ e₁ : φ₁
Γ[x↦φ₁] ⊢ e₂ : φ₂
-------------------------
Γ ⊢ LET x = e₁ IN e₂ : φ₂

Γ[x↦φ₁] ⊢ e : φ₂
---------------------------
Γ ⊢ FUN x ⇒ e : (φ₁ ⇒ φ₂)·⊥

Γ ⊢ e₁ : (φ ⇒ τ₂·ς₂)·ς₁)
Γ ⊢ e₂ : φ
------------------
Γ ⊢ e₁(e₂) : τ₂·(ς₁ V ς₂)

NOTE: Tenv 'extension' comes from label from BoxE expr.
This is a hack to create low/high 'memories' that satisfy
the definition of non-interference using the core language.

Γ[x ↦ _·ς₁] ⊢ e : τ·ς₂
------------------------
Γ ⊢ BOX e : ref(τ·ς₁)·⊥

Γ ⊢ e : ref(τ·ς₁)·ς₂
-------------
Γ ⊢ !e : τ·(ς₁ V ς₂)

Note: this prevents insecure *direct* informtion flow
from e2 to e1.

Γ ⊢ e₁ : ref(τ·ς₁)·ς
Γ ⊢ e₂ : τ·ς₂
ς₂ ≼ ς₁
--------------
Γ ⊢ e₁ ← e₂ : τ·ς₂

Note: this also prevents insecure *indirect* information
flow. This only describes a loop that terminates;
infinite loops break the definition of non-interference,
which requires programs to terminate.

Γ ⊢ e₁ : bool·ς₁
Γ ⊢ e₂ : τ·ς₂
ς₁ ≼ ς₂
--------------------------------
Γ ⊢ while(e₁){e₂} : bool·(ς₁ V ς₂)

Γ ⊢ e₁ : φ'
Γ ⊢ e₂ : φ
--------------------------------
Γ ⊢ e₁;e₂ : φ

-----------------------------------------------------
Objects are treated as nonsecret. Typing will fail
if object information directly flows into secret locations
or as a result of indirect flow from conditionals on secret
values. 'Extensions' are just information provided by our
list of CDecls.

Γ ⊢ e₁ : τ₁·⊥
...
Γ ⊢ eₙ : τₙ·⊥
--------------------------------
Γ ⊢ NEW cn(e₁,,…,eₙ) : (object cn)·⊥

Γ ⊢ e₁ : (object cn)·⊥
Γ[x↦τ·⊥] ⊢ fn : τ·⊥
--------------------------------
Γ ⊢ e₁.fn : τ·⊥

Γ ⊢ e₁ : (object cn)·⊥
Γ ⊢ e₂ : τ·⊥
Γ[x↦τ·⊥] ⊢ fn : τ·⊥
--------------------------------
Γ ⊢ e₁.fn(e₂) : void·⊥

Γ ⊢ e₁ : (object cn)·⊥
Γ ⊢ e₂ : τ·⊥
Γ[x↦τ·⊥] ⊢ mn : (τ·⊥ ⇒ τ'·⊥)·⊥
--------------------------------
Γ ⊢ e₁.fn(e₂) : τ'·⊥
```
