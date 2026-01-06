open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
    variable
        α β γ r o o' o'' : Set

-- definition
ICont : Set → Set → Set → Set
ICont r o α = (α → o) → r

pure : α → ICont r r α
pure v = λ k → k v

_>>=_ : ICont r o α → (α → ICont o o' β) → ICont r o' β
m >>= f = λ k → m (λ x → f x k)

-- proof that 〈ICont, pure, >>=〉 is an indexed monad 
ICont-left-identity : {x : α} {f : α → ICont r o β}
    → (do
        v ← pure x
        f v
    ) ≡ f x
ICont-left-identity = refl

ICont-right-identity : {m : ICont r o α}
    → (do
        v ← m
        pure v
    ) ≡ m
ICont-right-identity = refl

ICont-associativity : {m : ICont r o α} {f : α → ICont o o' β} {g : β → ICont o' o'' γ}
    → (do
        v' ← do
            v ← m
            f v
        g v'
    ) ≡ (do
        v ← m
        v' ← f v
        g v'
    )
ICont-associativity = refl

-- bind
bind : α → ICont r (α → r) α
bind = λ x k → k x x
