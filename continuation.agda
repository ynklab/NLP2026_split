-- definition
ICont : Set → Set → Set → Set
ICont r o α = (α → o) → r

pure : {α r : Set} → α → ICont r r α
pure v = λ k → k v

_>>=_ : {α β r o o' : Set} → ICont r o α → (α → ICont o o' β) → ICont r o' β
m >>= f = λ k → m (λ x → f x k)

-- bind
bind : {α r : Set} → α → ICont r (α → r) α
bind = λ x k → k x x
