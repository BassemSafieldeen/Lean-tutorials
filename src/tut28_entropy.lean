import linear_algebra.eigenspace
import linear_algebra.tensor_product
import rnd_var
import shannon_theory

import tut3
import tut5
-- import tut13_ptrace

---- QUANTUM ENTROPY

open rnd_var

open_locale tensor_product big_operators

noncomputable theory

variables 
{ℋ : Type} [complex_hilbert_space ℋ]
{ℋ₁ : Type} [complex_hilbert_space ℋ₁]
{ℋ₂ : Type} [complex_hilbert_space ℋ₂]

universe x

variables 
{ι : Type x} -- indexing type
[fintype ι] -- tell Lean that the set of all elements ι is finite.

/-
Logarithm of a linear operator.
-/
def log (ρ : ℋ →ₗ[ℂ] ℋ) : ℋ →ₗ[ℂ] ℋ := sorry

notation A ` ∘ ` B := linear_map.comp A B

def entropy (ρ : module.End ℂ ℋ) : ℝ := 
( Tr ( ρ ∘ (log ρ) ) ).re

universe x

/--
If a linear operator has trace one then its eigenvalues sum to 1.
-/
lemma sum_eigenvalues_eq_one_of_trace_one (ρ : module.End ℂ ℋ) 
{e : ι → ℝ} {he : ∀ i, ρ.has_eigenvalue (e i)}: 
(Tr ρ = 1) → (∑ i, e i = 1) := 
begin
    sorry
end

/--
A quantum state has all nonnegative eigenvalues.
-/
lemma quantum_state_pos_semidef (ρ : module.End ℂ ℋ) [quantum_state ρ] (e : ℝ) : 
ρ.has_eigenvalue e → e ≥ 0 := sorry -- This follows directly from the 
-- positive semi-definite axiom (axiom 2).

/--
Quantum entropy is nonnegative
-/
theorem entropy_nonneg  {ρ : module.End ℂ ℋ}
{e : ι → ℝ} {he : ∀ i, ρ.has_eigenvalue (e i)} [quantum_state ρ] : 
entropy ρ ≥ 0 := 
begin
    have : entropy ρ = - ∑ i, (e i) * real.log(e i), {sorry},
    rw this,
    clear this,
    -- All the eignevalues are nonnegative because the state is positive semidefinite
    have he_nonneg : ∀ i, (e i) ≥ 0, {
        intros,
        apply quantum_state_pos_semidef ρ,
        exact he i,
    },
    -- The eigenvalues sum to 1 because the state has trace 1.
    have he_sum_eq_one : ∑ i, (e i) = 1, {
        apply sum_eigenvalues_eq_one_of_trace_one ρ quantum_state.trace_one,
        apply he,
    },
    -- Given the available facts, the remaining term looks like Shannon 
    -- entropy. So we use that Shannon entropy is nonegative to finish.
    apply Shannon_entropy_nonneg, simp,
    {exact he_nonneg},
    {exact he_sum_eq_one},
end

/--
Convacity of the entropy
-/
theorem entropy_concave  {ρ : module.End ℂ ℋ} 
{e : ι → ℝ} {he : ∀ i, ρ.has_eigenvalue (e i)}
(pₓ : ι → ℝ) [hpₓ : rnd_var pₓ] (ρₓ : ι → module.End ℂ ℋ)
(hρ : ρ = ∑ i, (pₓ i) • (ρₓ i)) : 
entropy ρ ≥ ∑ i, (pₓ i) * entropy (ρₓ i) := 
begin
    have : entropy ρ = - ∑ i, (e i) * real.log(e i), {sorry},
    rw this,
    clear this,
    sorry
end

def log_bp (ρ : ℋ₁ ⊗[ℂ] ℋ₂ →ₗ[ℂ] ℋ₁ ⊗[ℂ] ℋ₂) : (ℋ₁ ⊗[ℂ] ℋ₂) →ₗ[ℂ] (ℋ₁ ⊗[ℂ] ℋ₂) := sorry

/--
Joint quantum entropy
https://arxiv.org/abs/1106.1445
-/
def joint_entropy (ρ : ℋ₁ ⊗ ℋ₂ →ₗ[ℂ] (ℋ₁ ⊗ ℋ₂)) : ℝ :=
( Tr ( ρ ∘ (log_bp ρ) ) ).re