# Interact

Interact is both an interaction tree library for agda and a model
for executing C code.

Interaction Trees in this library are based on the [Interaction Trees paper](https://arxiv.org/abs/1906.00046?context=cs) and the [Interaction Trees coq library](https://github.com/DeepSpec/InteractionTrees)

## Development Environment

You will either need a recent version of agda and make
or you can use the nix flake provided.

A nix development environment can be accessed using

```bash
nix develop
```

## Building

The project can be built with nix using `nix build`
or can be built from make using `make interact` or `make app` to build the library or application respectively.
