# Smart Contract as Automata

State-Transition Systems for Smart Contracts: semantics and
properties.

## Building Instructions

### Requirements

* [Coq v 8.7 - 8.9](https://coq.inria.fr)
* [Mathematical Components 1.6.4 or 1.7.0](https://math-comp.github.io/math-comp) (`ssreflect`)
* [FCSL-PCM 1.0.0](https://github.com/imdea-software/fcsl-pcm)
  
We recommend installing the requirements via [opam](https://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-fcsl-pcm
```

### Building the project

```
make clean; make -j
```

## Project Structure

* `Core/Automata2.v` - definition of the automata-based language semantics;
* `Contracts/Puzzle.v` - a simple puzzle-solving game contract and its properties;
* `Contracts/Crowdfunding.v` - the Crowdfunding contract and its properties;
