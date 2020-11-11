import linear_algebra.eigenspace
import linear_algebra.tensor_product
import shannon_theory

import tut3
import tut5
-- import tut13_ptrace

---- QUANTUM ENTROPY

open_locale tensor_product big_operators

noncomputable theory

variables 
{ℋ : Type} [complex_hilbert_space ℋ]
{ℋ₁ : Type} [complex_hilbert_space ℋ₁]
{ℋ₂ : Type} [complex_hilbert_space ℋ₂]

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
lemma sum_eigenvalues_eq_one_of_trace_one (ι : Type x) (ρ : module.End ℂ ℋ) {s : finset ι}
{e : ι → ℝ} {he : ∀ i ∈ s, ρ.has_eigenvalue (e i)}: 
(Tr ρ = 1) → (∑ i in s, e i = 1) := 
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
theorem entropy_nonneg (ι : Type x) {ρ : module.End ℂ ℋ} {s : finset ι}
{e : ι → ℝ} {he : ∀ i ∈ s, ρ.has_eigenvalue (e i)} [quantum_state ρ] : entropy ρ ≥ 0 := 
begin
    have : entropy ρ = - ∑ i in s, (e i) * real.log(e i), {sorry},
    rw this,
    clear this,
    -- All the eignevalues are nonnegative because the state is positive semidefinite
    have he1 : ∀ i ∈ s, (e i) ≥ 0, {
        intros,
        apply quantum_state_pos_semidef ρ,
        exact he i H,
    },
    -- The eigenvalues sum to 1 because the state has trace 1.
    have he2 : ∑ i in s, (e i) = 1, {
        apply sum_eigenvalues_eq_one_of_trace_one ι ρ quantum_state.trace_one,
        exact he,
    },
    -- The remaining term looks Shannon entropy, so we use that Shannon 
    -- entropy is nonegative to finish the proof.
    have he3 : Shannon_entropy s e he1 he2 ≥ 0, by exact Shannon_entropy_nonneg s e,
    rw Shannon_entropy at he3,
    exact he3,
end

def rnd_var {ι : Type x} (s : finset ι) (pₓ : ι → ℝ) :=
(∀ i ∈ s, pₓ i ≥ 0) ∧ (∑ i in s, pₓ i = 1)

/--
Convacity of the entropy
-/
theorem entropy_concave 
(ι : Type x) {sₓ : finset ι} {ρ : module.End ℂ ℋ}
{sₑ : finset ι} {e : ι → ℝ} {he : ∀ i ∈ sₑ, ρ.has_eigenvalue (e i)}
(pₓ : ι → ℝ) [hpₓ : rnd_var sₓ pₓ] (ρₓ : ι → module.End ℂ ℋ)
(hρ : ρ = ∑ i in sₓ, (pₓ i) • (ρₓ i)) : 
entropy ρ ≥ ∑ i in sₓ, (pₓ i) * entropy (ρₓ i) := 
begin
    rw rnd_var at hpₓ,
    have : entropy ρ = - ∑ i in sₑ, (e i) * real.log(e i), {sorry},
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