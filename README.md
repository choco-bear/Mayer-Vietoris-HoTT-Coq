# Mayer-Vietoris-HoTT-Coq
This repository contains the Rocq formalization of the construction of the Mayer-Vietoris long exact sequence in HoTT.

## Setup
This version is known to compile with rocq-prover 9.0.0.

The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create <opam-switch-name> 5.3.0
opam switch link <opam-switch-name> .
```
3. Add the Coq opam repository.
```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam update
```
4. Install the right version of the dependencies.
```
opam install rocq-prover.9.0.1
opam install coq-hott.9.0
```

## How to Compile
You can compile this with the command below:
```
make -j
```
To clean the build files, use:
```
make clean
```