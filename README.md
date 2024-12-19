# Dependent Lambda

A dependently-typed lambda calculus based on MLTT and inspired by Agda.  

Currently, it features dependent product types, non-cumulative universes, built-in naturals, and intensional equality, along with their corresponding elimination rules (pattern matching) and primitive recursion, with generalized inductive datatypes coming soon.  

It aims to support indexed datatype elimination based on simple unification à la Agda.  
Additionally, it would be nice to eventually add some form of meta-variable solving to support implicit arguments.  

Another possible extension could be multiple-argument recursion, either via straightforward sugaring or more involved termination checking.
