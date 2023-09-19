
module 00-Common where

open import Level using (_⊔_; Level) renaming (suc to lsuc)

private
    variable
        o : Level

Bin : Set o → Set o
Bin α = α → α → α