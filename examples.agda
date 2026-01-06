open import lex
open import rules
open import Data.Bool.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Sandy called Kim's mother
ex₁ : Bool
ex₁ =
    (<
        s
        (>
            call
            (<
                k
                mom
            )
        )
    )

ex₁-check : ex₁ ≡ call (mom k) s
ex₁-check = refl

-- Sandy called everyone
ex₂ : Bool
ex₂ =
    (⇓
        (<ᶜ
            (⇑ s)
            (>ᶜ
                (⇑ call)
                ev
            )
        )
    )

ex₂-check : ex₂ ≡ ev (λ x → call x s)
ex₂-check = refl

-- Everyone₁ called their₁ mother.
ex₃ : Bool
ex₃ =
    (⇓
        (<ᶜ
            (▷ ev)
            (>ᶜ
                (⇑ call)
                (<ᶜ
                    pro
                    (⇑ mom)
                )
            )
        )
    )

ex₃-check : ex₃ ≡ ev (λ x → call (mom x) x)
ex₃-check = refl

-- Who called everyone?
ex₄ : Bool
ex₄ =
    (⇓
        (<ᶜ
            wh
            (>ᶜ
                (⇑ call)
                ev
            )
        )
    )

ex₄-check : ex₄ ≡ wh (λ x → ev (λ y → call y x))
ex₄-check = refl

-- Who called their mother?
ex₅ : Bool
ex₅ =
    (⇓
        (<ᶜ
            (▷ wh)
            (>ᶜ
                (⇑ call)
                (<ᶜ
                    pro
                    (⇑ mom)
                )
            )
        )
    )

ex₅-check : ex₅ ≡ wh (λ x → call (mom x) x)
ex₅-check = refl

-- Kim's mother, Sandy called. (topicalization)
ex₆ : Bool
ex₆ =
    (>
        (F
            (<
                k
                mom
            )
        )
        (>B
            did
            (>B
                (>T s)
                call
            )
        )
    )

ex₆-check : ex₆ ≡ call (mom k) s
ex₆-check = refl

-- Whom did everyone call?
ex₇ : Bool
ex₇ =
    (⇓
        (>
            (F wh)
            (>B
                (⊛> (⇑ did))
                (>B
                    (⊛> (>Tᶜ ev))
                    (⊛> (⇑ call))
                )
            )
        )
    )

ex₇-check : ex₇ ≡ ev (λ x → wh (λ y → call y x))
ex₇-check = refl

-- Which of their₁ relatives did everyone₁ call?
ex₈ : Bool
ex₈ =
    (⇓
        (>
            (F
                (>
                    which
                    (>ᶜ
                        (⇑ of)
                        (<ᶜ
                            pro
                            (⇑ rels)
                        )
                    )
                )
            )
            (>B
                (⊛> (⇑ did))
                (>B
                    (⊛> (>Tᶜ (▷ ev)))
                    (⊛> (⇑ call))
                )
            )
        )
    )

ex₈-check : ex₈ ≡ ev (λ x → wh2 (rels x) (λ y → call y x))
ex₈-check = refl
