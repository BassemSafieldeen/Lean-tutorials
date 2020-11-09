import tut3

import linear_algebra.tensor_product
import analysis.normed_space.inner_product

open inner_product_space

open_locale tensor_product

noncomputable theory

variables (V W : Type) 
[complex_hilbert_space V] [complex_hilbert_space W]

variables (ℋ₁ ℋ₂ : Type) 
[complex_hilbert_space ℋ₁] [complex_hilbert_space ℋ₂]

variables (ρ : ℋ₁ →ₗ[ℂ] ℋ₁) (σ : ℋ₂ →ₗ[ℂ] ℋ₂) 
[quantum_state ρ] [quantum_state σ]

#check ρ -- this is a linear operator
#check σ -- this is another linear operator.
#check ρ ⊗ σ -- WHAT IS THIS? 
-- How about this: It's a linear operator that acts on any
-- 

/-
Recall that any element of ℋ₁ ⊗[ℂ] ℋ₂ can be written as 
a linear combination of elements that look like this eᵢ₁ ⊗ eᵢ₂, 
where eᵢ₁ and eᵢ₂ form a basis over ℋ₁ and ℋ₂ respectively.
-/