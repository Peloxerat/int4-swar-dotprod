# swar int4 dot product

this repo contains the development, automated synthesis, and formal verification of a highly optimized SWAR (SIMD Within A Register) algorithm for computing the dot product of 4-bit signed integers (INT4) packed into a 32-bit register.

the algorithm is designed for fast dot product computation in quantized neural networks on architectures without native INT4 vector instructions.

## structure

- **`swar_z3_synthesizer.py`** — z3 SMT solver script that automatically synthesized the bitwise hack.
- **`swar_dot_product_final.py`** — final python implementation. includes packing functions, the ground truth calculation, and testing against random vectors.
- **`swar_verify/`** — lean 4 project. `SwarVerify/Basic.lean` contains the full formal mathematical proof that our optimized SWAR algorithm is strictly equivalent to naive multiplication for all possible values.

## how to run checks

### 1. python tests
make sure your virtual env is active and run the tests:

```bash
source .venv/bin/activate
python swar_dot_product_final.py
```
this runs a test on 1,000,000 randomly generated vectors to make sure the SWAR function always matches the ground truth.

### 2. run the z3 synthesizer (optional)
if you want to see how the SMT solver deduces the bit masks and operations from scratch:

```bash
source .venv/bin/activate
python swar_z3_synthesizer.py
```
*synthesis takes a bit and outputs the exact formula.*

### 3. formal verification (lean 4)
to mathematically verify the proof (which checks all possible $2^{64}$ input combinations via the `bv_decide` SAT solver and `omega` algebra tactics), run:

```bash
cd swar_verify
~/.elan/bin/elan run leanprover/lean4:v4.32.2 lean SwarVerify/Basic.lean
```
*if the command finishes without errors and returns 0, it means the theorem `swar_is_correct` is fully proven and the algorithm has no mathematical flaws.*
