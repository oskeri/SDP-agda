# Agda-SDP

A small library for solving sequential decision problems in Agda.

For an overview of the modules, see `Everything.agda`

To test the examples, build with `make` or `agda --compile Main.agda`.
The executable can run 4 examples (The parameters `t`, `n`, `α` and `β` should be positive integers):

- `./Main rw t n` runs the random walk example for n steps starting at time t
- `./Main gd+ t n α β` or `./Main gd+½ t n α β`runs the generation dilemma example for n steps starting at time t with weights α and β for two of the transitions. In the first case, rewards of each generation are added while the in the latter case, each generation is valued half as much as the one before.
- `./Main cc t n` runs the car crash example for n steps starting at time t

Tested using Agda-2.6.4 and version 2.0 of the Agda standard library.
