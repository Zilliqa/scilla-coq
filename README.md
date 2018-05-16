# Smart Contract as Automata

State-Transition Systems for Smart Contracts: semantics and
properties.

## Building Instructions

### Requirements

* [Coq 8.7 or 8.8](https://coq.inria.fr)
* [Mathematical Components 1.6.4 or 1.7.0](http://math-comp.github.io/math-comp/) (`ssreflect`)
  
We recommend installing the requirements via [OPAM](https://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```

### Building the project

```
make clean; make
```

## Project Structure

* `Core/Automata2.v` - definition of the automata-based language
  semantics;
* `Contracts/Puzzle.v` - a simple puzzle-solving game contract and its properties;
* `Contracts/Crowdfunding.v` - the Crowdfunding contract and its properties;
