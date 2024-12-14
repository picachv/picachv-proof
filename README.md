# PCD-Proof

This repository contains formalization for the dataframe data model and relational algebra semantics that captures the privacy policy and mechanically checked proofs of the correctness.

## Prerequisites

You should install Coq >= 8.18.0 to ensure that this project compiles.

## Compile the projects

```sh
$ cd ./theories
$ coq_makefile -f ./_CoqProject -o Makefile
$ make
```

Or you can use the Python script to type check the Coq project.

```sh
$ ./run
```

If the code compiles, all the proofs are successfully validated by Coq's type checker.

# Note

The codebase of Picachv's Coq formalism is still untidy and will be cleaned up as soon as possible. As for now, there might some naming issues and/or inconsistent terms between the Coq code and paper descriptions. We sincerely apologize for any inconvenince and will fix it.
