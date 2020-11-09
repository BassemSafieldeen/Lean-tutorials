import linear_algebra.eigenspace
import linear_algebra.tensor_product
import shannon_theory

import tut5
import tut13_ptrace

open_locale tensor_product

noncomputable theory

---- QUANTUM ENTROPY

variables 
{ℋ : Type*} [complex_hilbert_space ℋ]
{ℋ₁ : Type*} [complex_hilbert_space ℋ₁]
{ℋ₂ : Type*} [complex_hilbert_space ℋ₂]

/-
Logarithm of a linear operator.
-/
def log (ρ : ℋ →ₗ[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ := sorry

notation A ` ∘ ` B := linear_map.comp A B

def entropy (ρ : ℋ →ₗ[ℂ] ℋ) : ℝ := 
( Tr ( ρ ∘ (log ρ) ) ).re

theorem entropy_eigenvalues (ρ : ℋ →ₗ[ℂ] ℋ) :
entropy ρ = ∑ e in ρ.eigenvalues, (e i) * real.log(e i) := sorry

#check Shannon_entropy_nonneg
#check module.End.has_eigenvalue

theorem entropy_nonneg {ρ : ℋ →ₗ[ℂ] ℋ} : entropy ρ ≥ 0 := 
begin
    -- Try to use Shannon_entropy_nonneg in this proof
    rw entropy_eigenvalues,
    sorry
end




-- Temporary workaround. TODO: Teach Lean that (ℋ ⊗[ℂ] ℋ) in ℋ ⊗[ℂ] ℋ →ₗ[ℂ] ℋ ⊗[ℂ] ℋ should be 
-- interpreted as ℋ'' →ₗ[ℂ] ℋ''.

def log_bp (ρ : ℋ ⊗[ℂ] ℋ →ₗ[ℂ] ℋ ⊗[ℂ] ℋ) : ℋ ⊗[ℂ] ℋ →ₗ[ℂ] ℋ ⊗[ℂ] ℋ := sorry

def entropy_bp (ρ : ℋ ⊗[ℂ] ℋ →ₗ[ℂ] ℋ ⊗[ℂ] ℋ) : ℝ := -- ⊗ works but ⊗[ℂ] doesn't. I don't understand why.
( Tr ( ρ ∘ (log_bp ρ) ) ).re