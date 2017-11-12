# Smart Contract as Automata

State-Transition Systems for Smart Contracts: semantics and
properties.

## Building Instructions

### Requirements

* Coq 8.7, available from https://coq.inria.fr/download
* Mathematical Components Library 1.6.4, available from
  https://math-comp.github.io/math-comp/
  
For the installation, follow instructions in the corresponding README files.

Alternatively, Coq and mathcomp can be installed via the opam package
manager, by executing the following commands in the console:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```

### Building the project

```
make clean; make
```
