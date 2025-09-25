# Poly-Simpl

Coq learning project in which i design polynomial simplification function and
prove its correctness and cannonality*.

## Project structure
Project is an extension of 2nd book of Software foundation, therefore
syntax is derived from there.


Whole algorithm is defined in file Algorithm.v.
It's properties are proven in PolySimplProps.v, while using lemmas from
other files.

## Results
Algorithm is proven to be correct.
There is small caveat to cannonality, it is proven while taking two assumptions:
1. small lemma on transitivity of Coq's comparison of ascii characters.
2. because it's not the goal of this project, I assume the truth of one of
fundamental theorems of algebra


## Possible improvements and future work
Possible ways to address above mentioned issues include:
1. Changing representation of variables from string to nat. That would be
    straying from Software Foundation further than was acceptable during writing of
    this project, but could be acceptable if done in a smart way (for example by
    only using this representation internally).
2. Making more change to internal representation, for example by translating to
    Horner's scheme. This is more less the way it is done in Coq's Stdlib, and
    so gives us hope to circumvent problem of Fundamental Theorem of Algebra.

