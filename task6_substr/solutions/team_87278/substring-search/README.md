# substring-search

This projects presents formal verification for substring search problem in Lean 4 using [Loom framework](https://github.com/verse-lab/loom).

## Build

To build the project, you will need Lean 4 theorem prover installed. Instructions are provided [here](https://lean-lang.org/install/).
You will need z3 SMT solver available on PATH which can be installed by running:

```
brew install z3
```
On MacOS

```
sudo apt install z3-solver
```
On Linux

After finishing the setup, run
```
lake build
```

in terminal in project directory. This will build the project.
Please note that the whole process can take up to 30mins of time in total.