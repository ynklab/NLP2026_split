open import continuation
open import Data.Bool.Base

-- entity type
postulate
    e : Set

-- function application
> : {α β : Set} → (α → β) → α → β
> f x = f x

< : {α β : Set} → α → (α → β) → β
< x f = f x

-- function composition
>B : {α β γ : Set} → (β → γ) → (α → β) → (α → γ)
>B f g = λ x → f (g x)

<B : {α β γ : Set} → (α → β) → (β → γ) → (α → γ)
<B g f = λ x → f (g x)

-- type-raising
>T : {α β : Set} → α → (α → β) → β
>T x = λ f → f x

<T : {α β : Set} → α → (α → β) → β
<T x = λ f → f x

-- fronting
F : {α β : Set} → α → (α → β) → β
F x = λ f → f x

-- function application (continuized)
>ᶜ : {α β r o o' : Set} → ICont r o (α → β) → ICont o o' α → ICont r o' β
>ᶜ F X = do
    f ← F
    x ← X
    pure (f x)

<ᶜ : {α β r o o' : Set} → ICont r o α → ICont o o' (α → β) → ICont r o' β
<ᶜ X F = do
    x ← X
    f ← F
    pure (f x)

-- type-raising (continuized)
>Tᶜ : {α β r o : Set} → ICont r o α → ICont r o ((α → β) → β)
>Tᶜ X = do
    x ← X
    pure (λ f → f x)

<Tᶜ : {α β r o : Set} → ICont r o α → ICont r o ((α → β) → β)
<Tᶜ X = do
    x ← X
    pure (λ f → f x)

-- lift
⇑ : {α r : Set} → α → ICont r r α
⇑ x = pure x

-- lower
⇓ : {α : Set} → ICont α Bool Bool → α
⇓ X = X (λ x → x)

-- bind
▷ : {α r o : Set} → ICont r o α → ICont r (α → o) α
▷ X = do
    x ← X
    bind x

-- split (definable with >ᶜ/<ᶜ)
⊛> : {α β r o o' : Set} → ICont r o (α → β) → ICont o o' α → ICont r o' β
⊛> F = λ X → >ᶜ F X

⊛< : {α β r o o' : Set} → ICont o o' (α → β) → ICont r o α → ICont r o' β
⊛< F = λ X → <ᶜ X F
