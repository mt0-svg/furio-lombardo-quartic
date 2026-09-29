# loader.sage: loader of the third (Sage) implementation. Run scripts from code/second-implementations/local-group-covering.
# Reused unchanged from code/second-implementations/local-group-covering (written independently of the PARI code): genus2_group_law.sage (group law),
# genus2_log.sage (logarithm with explicit tail and perturbation bounds); quad_roots is replaced by the version of
# abel_prym.sage with a certified square root.
load('genus2_group_law.sage')
load('genus2_log.sage')
load('exact_data.sage')
load('completion_kv_eisenstein.sage')
load('abel_prym.sage')
