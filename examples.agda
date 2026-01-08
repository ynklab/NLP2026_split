open import continuation
open import lex
open import rules
open import Data.Bool.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Basic: Sandy called Kim's mother.
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

-- Quantification: Sandy called everyone.
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

-- Quantificational binding: Everyoneᵢ called theirᵢ mother.
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

-- Binding with a proper name: Sandyᵢ called herᵢ mother.
ex₄ : Bool
ex₄ =
    (⇓
        (<ᶜ
            (▷ (⇑ s))
            (>ᶜ
                (⇑ call)
                (<ᶜ
                    pro
                    (⇑ mom)
                )
            )
        )
    )

ex₄-check : ex₄ ≡ call (mom s) s
ex₄-check = refl

-- Wh-question + quantification: Who called everyone?
ex₅ : Bool
ex₅ =
    (⇓
        (<ᶜ
            wh
            (>ᶜ
                (⇑ call)
                ev
            )
        )
    )

ex₅-check : ex₅ ≡ wh (λ x → ev (λ y → call y x))
ex₅-check = refl

-- Wh-question with binding: Whoᵢ called theirᵢ mother?
ex₆ : Bool
ex₆ =
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

ex₆-check : ex₆ ≡ wh (λ x → call (mom x) x)
ex₆-check = refl

-- Topicalization (to check >B): Kim's mother, Sandy called.
ex₇ : Bool
ex₇ =
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

ex₇-check : ex₇ ≡ call (mom k) s
ex₇-check = refl

-- Object wh-question (reconstructed below the quantifier): Whom did everyone call?
ex₈ : Bool
ex₈ =
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

ex₈-check : ex₈ ≡ ev (λ x → wh (λ y → call y x))
ex₈-check = refl

-- Reconstruction: Which of theirᵢ relatives did everyoneᵢ call?
ex₉ : Bool
ex₉ =
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

ex₉-check : ex₉ ≡ ev (λ x → wh2 (rels x) (λ y → call y x))
ex₉-check = refl

-- Weak crossover: *Whomᵢ did theirᵢ mother call?
-- Derivation before the final step (i.e., application of ⇓)
ex₁₀-1 : ICont (e → Bool) (e → Bool) Bool
ex₁₀-1 =
    (>
        (F (▷ wh))
        (>B
            (⊛> (⇑ did))
            (>B
                (⊛>
                    (>Tᶜ
                        (<ᶜ
                            pro
                            (⇑ mom)
                        )
                    )
                )
                (⊛> (⇑ call))
            )
        )
    )

ex₁₀-1-check : ex₁₀-1 ≡ λ k x → wh (λ y → k (call y (mom x)) y)
ex₁₀-1-check = refl

-- This cannot be lowered with ⇓
-- ex₁₀-2 : Bool
-- ex₁₀-2 = ⇓ ex₁₀-1 -- Type checking fails!