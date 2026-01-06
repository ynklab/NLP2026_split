open import continuation
open import Data.Bool.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- lexical items
postulate
    e : Set -- entity type
    s : e
    k : e
    mom : e → e
    call : e → e → Bool
    rels : e → e
    ev : {r : Set} → ICont r r e
    wh : {r : Set} → ICont r r e -- tentatively defined as a generalized quantifier
    wh2 : {r : Set} → e → ICont r r e

pro : {r : Set} → ICont (e → r) r e
pro = λ k x → k x

-- pro and bind cancel each other
lem-pro-bind : {α r o : Set} {a : e} {f : e → e → ICont r o α}
    → bind a >>= (λ x → pro >>= (λ y → f x y)) ≡ f a a
lem-pro-bind = refl

which : {r o : Set} → ICont r o e → ICont r o e
which X = X >>= (λ x → wh2 x)

did : Bool → Bool
did x = x

of : e → e
of x = x
