open import continuation
open import Data.Bool.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
    variable
        α r o : Set

-- lexical items
postulate
    e : Set -- entity type
    s : e
    k : e
    mom : e → e
    call : e → e → Bool
    rels : e → e
    ev : ICont r r e
    wh : ICont r r e -- tentatively defined as a generalized quantifier
    wh2 : e → ICont r r e

pro : ICont (e → r) r e
pro = λ k x → k x

-- pro and bind cancel each other
lem-pro-bind : {a : e} {f : e → e → ICont r o α}
    → (do
        x ← bind a
        y ← pro
        f x y)
    ≡ f a a
lem-pro-bind = refl

which : ICont r o e → ICont r o e
which X = do
    x ← X
    wh2 x

did : Bool → Bool
did x = x

of : e → e
of x = x
