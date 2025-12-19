# FOL Compactness

Theorem: If $L$ is a first order language with $T$ an $L$ theory, then TFAE:

1. Every finite subset of $T$ is satisfiable (eg has a model)
2. $T$ is satisfiable.

Proof: 
<- If $T$ is satisfiable, clearly all finite subsets of $T$ are satisfiable.
-> If every finite subset of $T$ is satisfiable, then every finite subset of $T$ is consistent by soundness. Thus, by the $T$ is consistent by compactness of propositional logic. Thus, by completeness, $T$ is satisfiable.

Thus, we must prove:
- If every finite subset of $T$ is consistent, then $T$ is consistent.
- If $T$ is consistent, then $T$ has a model. (Completeness theorem)

Additionally, the encoding of
- First order logic 
- Propositional logic
- Soundness theorem
- Completeness theorem for propositional logic
- Henkin's construction
are required.

We do so under Kripke semantics, because it's easier to formalize. Tarskian semantics can be recovered from Kripke semantics by considering only models with one world.