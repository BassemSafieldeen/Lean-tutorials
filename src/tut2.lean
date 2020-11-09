import linear_algebra.finite_dimensional
import analysis.normed_space.inner_product
import data.complex.basic

/--
Hilbert space
-/
class complex_hilbert_space (V : Type) extends inner_product_space ℂ V :=
(hilbert_ness: 1=1)

variables {ℋ : Type} [complex_hilbert_space ℋ]

#check ∥(0 : ℋ)∥

/--
The Trace of a linear map on a complex Hilbert space.
-/
noncomputable def Tr := linear_map.trace ℂ ℋ

/--
A quantum state is a linear map from a Hilbert space to itself -- 
a.k.a., a linear operator -- with trace one and an additional axiom.
-/
class quantum_state (ρ : module.End ℂ ℋ) :=
(trace_one : Tr ρ = 1)
(axiom_2 : 1=1)

variables {ρ σ : module.End ℂ ℋ} [quantum_state ρ] [quantum_state σ]

example : Tr ρ = 1 := 
begin
    exact quantum_state.trace_one,
end