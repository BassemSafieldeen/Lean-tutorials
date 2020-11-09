import linear_algebra.tensor_product

import tut2

open_locale tensor_product

variables {ℋ : Type} [complex_hilbert_space ℋ]
{ρ σ τ : module.End ℂ ℋ} [quantum_state ρ] [quantum_state σ] [quantum_state τ]

#check tensor_product
#check ρ ⊗ₜ[ℂ] σ

notation A ` ⊗ ` B := A ⊗ₜ[ℂ] B

example {a : ℂ} : a • (ρ ⊗ σ) = (a • ρ) ⊗ σ :=
begin
    exact rfl,
end

example {a : ℂ} : a • (ρ ⊗ σ) = ρ ⊗ (a • σ) :=
begin
    norm_num,
end

example {a : ℂ} : a • (ρ + σ) = a • ρ + a • σ := 
begin
    rw smul_add,
end

example : ρ ⊗ (σ + τ) = ρ ⊗ σ + ρ ⊗ τ := 
begin
    rw tensor_product.tmul_add,
end 

example : (σ + τ) ⊗ ρ = σ ⊗ ρ + τ ⊗ ρ := 
begin
    rw tensor_product.add_tmul,
end