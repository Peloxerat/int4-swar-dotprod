import random
import time

from z3 import *

MASK32 = 4294967295


def pack_int4(arr):
    packed = 0
    for i in range(8):
        packed |= (arr[i] & 15) << i * 4
    return packed


def unpack_int4(packed):
    arr = []
    for i in range(8):
        val = packed >> i * 4 & 15
        if val & 8:
            val -= 16
        arr.append(val)
    return arr


def ground_truth(ap, bp):
    return sum((a * b for a, b in zip(unpack_int4(ap), unpack_int4(bp))))


def z3_spec(a, b):
    total = BitVecVal(0, 32)
    for i in range(8):
        sa = SignExt(28, Extract(i * 4 + 3, i * 4, a))
        sb = SignExt(28, Extract(i * 4 + 3, i * 4, b))
        total = total + sa * sb
    return total


def candidate_direct_unpack(a, b):
    total = BitVecVal(0, 32)
    for i in range(8):
        ni_a = LShR(a, BitVecVal(i * 4, 32)) & BitVecVal(15, 32)
        ni_b = LShR(b, BitVecVal(i * 4, 32)) & BitVecVal(15, 32)
        sa = (ni_a ^ BitVecVal(8, 32)) - BitVecVal(8, 32)
        sb = (ni_b ^ BitVecVal(8, 32)) - BitVecVal(8, 32)
        total = total + sa * sb
    return total


def candidate_even_odd_split(a, b):
    ea = a & BitVecVal(252645135, 32)
    eb = b & BitVecVal(252645135, 32)
    oa = LShR(a, BitVecVal(4, 32)) & BitVecVal(252645135, 32)
    ob = LShR(b, BitVecVal(4, 32)) & BitVecVal(252645135, 32)
    sea = ea | (ea & BitVecVal(134744072, 32)) * BitVecVal(30, 32)
    seb = eb | (eb & BitVecVal(134744072, 32)) * BitVecVal(30, 32)
    soa = oa | (oa & BitVecVal(134744072, 32)) * BitVecVal(30, 32)
    sob = ob | (ob & BitVecVal(134744072, 32)) * BitVecVal(30, 32)
    total = BitVecVal(0, 32)
    for i in range(4):
        ae = SignExt(24, Extract(i * 8 + 7, i * 8, sea))
        be = SignExt(24, Extract(i * 8 + 7, i * 8, seb))
        ao = SignExt(24, Extract(i * 8 + 7, i * 8, soa))
        bo = SignExt(24, Extract(i * 8 + 7, i * 8, sob))
        total = total + ae * be + ao * bo
    return total


def candidate_perfect_swar(a, b):
    BIAS = BitVecVal(2290649224, 32)
    au = a ^ BIAS
    bu = b ^ BIAS

    def nibble_sum(x):
        even = x & BitVecVal(252645135, 32)
        odd = LShR(x, BitVecVal(4, 32)) & BitVecVal(252645135, 32)
        byte_sums = even + odd
        s = (byte_sums & BitVecVal(16711935, 32)) + (
            LShR(byte_sums, BitVecVal(8, 32)) & BitVecVal(16711935, 32)
        )
        return s + LShR(s, BitVecVal(16, 32)) & BitVecVal(255, 32)

    sa = nibble_sum(au)
    sb = nibble_sum(bu)
    ea = au & BitVecVal(252645135, 32)
    eb = bu & BitVecVal(252645135, 32)
    oa = LShR(au, BitVecVal(4, 32)) & BitVecVal(252645135, 32)
    ob = LShR(bu, BitVecVal(4, 32)) & BitVecVal(252645135, 32)
    ea_low = ea & BitVecVal(16711935, 32)
    eb_low = eb & BitVecVal(16711935, 32)
    eb_low_rev = LShR(eb_low, 16) | eb_low << 16
    udp_even_low = LShR(ea_low * eb_low_rev, 16)
    ea_high = LShR(ea, 8) & BitVecVal(16711935, 32)
    eb_high = LShR(eb, 8) & BitVecVal(16711935, 32)
    eb_high_rev = LShR(eb_high, 16) | eb_high << 16
    udp_even_high = LShR(ea_high * eb_high_rev, 16)
    oa_low = oa & BitVecVal(16711935, 32)
    ob_low = ob & BitVecVal(16711935, 32)
    ob_low_rev = LShR(ob_low, 16) | ob_low << 16
    udp_odd_low = LShR(oa_low * ob_low_rev, 16)
    oa_high = LShR(oa, 8) & BitVecVal(16711935, 32)
    ob_high = LShR(ob, 8) & BitVecVal(16711935, 32)
    ob_high_rev = LShR(ob_high, 16) | ob_high << 16
    udp_odd_high = LShR(oa_high * ob_high_rev, 16)
    udp = udp_even_low + udp_even_high + udp_odd_low + udp_odd_high
    return udp - BitVecVal(8, 32) * sa - BitVecVal(8, 32) * sb + BitVecVal(512, 32)


def verify(candidate_fn, name, timeout_ms=60000):
    a = BitVec("a", 32)
    b = BitVec("b", 32)
    s = SolverFor("QF_BV")
    s.set("timeout", timeout_ms)
    s.add(z3_spec(a, b) != candidate_fn(a, b))
    t0 = time.time()
    result = s.check()
    dt = time.time() - t0
    if result == unsat:
        print(f"  ✓ [{name}] verified for all a, b  ({dt:.2f}s)")
        return True
    elif result == sat:
        m = s.model()
        ca, cb = (m.eval(a).as_long(), m.eval(b).as_long())
        print(f"  ✗ [{name}] disproved ({dt:.2f}s)")
        print(f"    a=0x{ca:08x}, b=0x{cb:08x}, exp={ground_truth(ca, cb)}")
        return False
    else:
        print(f"  ? [{name}] timeout ({dt:.2f}s)")
        return None


def cegis(num_instr, timeout_ms=30000, max_rounds=20):
    CONSTS = [252645135, 134744072, 2290649224, 286331153]
    CNAMES = ["0x0F", "0x08", "0x88", "0x11"]
    NI = 2 + len(CONSTS)
    OP_NAMES = [
        "AND",
        "OR",
        "XOR",
        "ADD",
        "SUB",
        "MUL",
        "SHL1",
        "SHL2",
        "SHL4",
        "SHL8",
        "SHR1",
        "SHR2",
        "SHR4",
        "SHR8",
    ]
    NOP = len(OP_NAMES)
    ops = [Int(f"o{i}") for i in range(num_instr)]
    s1 = [Int(f"x{i}") for i in range(num_instr)]
    s2 = [Int(f"y{i}") for i in range(num_instr)]
    bounds = []
    for i in range(num_instr):
        ri = NI + i
        bounds += [
            And(ops[i] >= 0, ops[i] < NOP),
            And(s1[i] >= 0, s1[i] < ri),
            And(s2[i] >= 0, s2[i] < ri),
        ]

    def sym_exec(av, bv):
        regs = [BitVecVal(av, 32), BitVecVal(bv, 32)]
        regs += [BitVecVal(c, 32) for c in CONSTS]
        for i in range(num_instr):
            ri = NI + i
            r1 = regs[0]
            for k in range(1, ri):
                r1 = If(s1[i] == k, regs[k], r1)
            r2 = regs[0]
            for k in range(1, ri):
                r2 = If(s2[i] == k, regs[k], r2)
            r = If(
                ops[i] == 0,
                r1 & r2,
                If(
                    ops[i] == 1,
                    r1 | r2,
                    If(
                        ops[i] == 2,
                        r1 ^ r2,
                        If(
                            ops[i] == 3,
                            r1 + r2,
                            If(
                                ops[i] == 4,
                                r1 - r2,
                                If(
                                    ops[i] == 5,
                                    r1 * r2,
                                    If(
                                        ops[i] == 6,
                                        r1 << 1,
                                        If(
                                            ops[i] == 7,
                                            r1 << 2,
                                            If(
                                                ops[i] == 8,
                                                r1 << 4,
                                                If(
                                                    ops[i] == 9,
                                                    r1 << 8,
                                                    If(
                                                        ops[i] == 10,
                                                        LShR(r1, BitVecVal(1, 32)),
                                                        If(
                                                            ops[i] == 11,
                                                            LShR(r1, BitVecVal(2, 32)),
                                                            If(
                                                                ops[i] == 12,
                                                                LShR(
                                                                    r1, BitVecVal(4, 32)
                                                                ),
                                                                LShR(
                                                                    r1, BitVecVal(8, 32)
                                                                ),
                                                            ),
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            )
            regs.append(r)
        return regs[-1]

    def py_exec(fo, fs1, fs2, av, bv):
        regs = [av, bv] + CONSTS[:]
        for i in range(num_instr):
            r1, r2 = (regs[fs1[i]], regs[fs2[i]])
            o = fo[i]
            if o == 0:
                r = r1 & r2
            elif o == 1:
                r = r1 | r2
            elif o == 2:
                r = r1 ^ r2
            elif o == 3:
                r = r1 + r2 & MASK32
            elif o == 4:
                r = r1 - r2 & MASK32
            elif o == 5:
                r = r1 * r2 & MASK32
            elif o == 6:
                r = r1 << 1 & MASK32
            elif o == 7:
                r = r1 << 2 & MASK32
            elif o == 8:
                r = r1 << 4 & MASK32
            elif o == 9:
                r = r1 << 8 & MASK32
            elif o == 10:
                r = r1 >> 1
            elif o == 11:
                r = r1 >> 2
            elif o == 12:
                r = r1 >> 4
            else:
                r = r1 >> 8
            regs.append(r)
        return regs[-1] & MASK32

    random.seed(42)
    examples = []
    for _ in range(3):
        aa = [random.randint(-8, 7) for _ in range(8)]
        bb = [random.randint(-8, 7) for _ in range(8)]
        ap, bp = (pack_int4(aa), pack_int4(bb))
        examples.append((ap, bp, ground_truth(ap, bp) & MASK32))
    print(f"  {num_instr} instructions, {NI} regs, {NOP} ops, {len(examples)} examples")
    for rnd in range(max_rounds):
        print(f"  round {rnd + 1} ({len(examples)} examples)...", end=" ", flush=True)
        solver = Solver()
        solver.set("timeout", timeout_ms)
        solver.add(bounds)
        for av, bv, exp in examples:
            solver.add(sym_exec(av, bv) == BitVecVal(exp, 32))
        t0 = time.time()
        result = solver.check()
        dt = time.time() - t0
        if result == unsat:
            print(f"UNSAT ({dt:.1f}s)")
            print(f"  == proved: {num_instr} instructions is not enough ==")
            return "unsat"
        elif result != sat:
            print(f"TIMEOUT ({dt:.1f}s)")
            return "timeout"
        m = solver.model()
        fo = [m.eval(ops[i]).as_long() for i in range(num_instr)]
        fs1 = [m.eval(s1[i]).as_long() for i in range(num_instr)]
        fs2 = [m.eval(s2[i]).as_long() for i in range(num_instr)]
        print(f"SAT ({dt:.1f}s)", end=" ")
        fail = False
        for _ in range(500):
            ta = [random.randint(-8, 7) for _ in range(8)]
            tb = [random.randint(-8, 7) for _ in range(8)]
            tap, tbp = (pack_int4(ta), pack_int4(tb))
            exp = ground_truth(tap, tbp) & MASK32
            got = py_exec(fo, fs1, fs2, tap, tbp)
            if got != exp:
                examples.append((tap, tbp, exp))
                fail = True
                break
        if fail:
            print(f"-> dropped by python. examples: {len(examples)}")
            continue
        rnames = ["a", "b"] + CNAMES[:]
        print("-> passed 500 tests!")
        for i in range(num_instr):
            rn = f"r{NI + i}"
            rnames.append(rn)
            on = OP_NAMES[fo[i]]
            s1n, s2n = (rnames[fs1[i]], rnames[fs2[i]])
            if fo[i] < 6:
                print(f"    {rn} = {s1n} {on} {s2n}")
            else:
                print(f"    {rn} = {on}({s1n})")

        def make_fn(fo_, fs1_, fs2_):

            def fn(a, b):
                regs = [a, b] + [BitVecVal(c, 32) for c in CONSTS]
                for i in range(num_instr):
                    rv1, rv2 = (regs[fs1_[i]], regs[fs2_[i]])
                    o = fo_[i]
                    if o == 0:
                        r = rv1 & rv2
                    elif o == 1:
                        r = rv1 | rv2
                    elif o == 2:
                        r = rv1 ^ rv2
                    elif o == 3:
                        r = rv1 + rv2
                    elif o == 4:
                        r = rv1 - rv2
                    elif o == 5:
                        r = rv1 * rv2
                    elif o == 6:
                        r = rv1 << 1
                    elif o == 7:
                        r = rv1 << 2
                    elif o == 8:
                        r = rv1 << 4
                    elif o == 9:
                        r = rv1 << 8
                    elif o == 10:
                        r = LShR(rv1, BitVecVal(1, 32))
                    elif o == 11:
                        r = LShR(rv1, BitVecVal(2, 32))
                    elif o == 12:
                        r = LShR(rv1, BitVecVal(4, 32))
                    else:
                        r = LShR(rv1, BitVecVal(8, 32))
                    regs.append(r)
                return regs[-1]

            return fn

        print("  z3 ForAll...", end=" ", flush=True)
        ok = verify(make_fn(fo, fs1, fs2), f"d{num_instr}", timeout_ms=60000)
        if ok is True:
            print("\n  =========================================")
            print("    boom! program verified by z3!!!        ")
            print("  =========================================")
            return "found"
        elif ok is False:
            a_v = BitVec("a", 32)
            b_v = BitVec("b", 32)
            sc = SolverFor("QF_BV")
            sc.set("timeout", 30000)
            sc.add(z3_spec(a_v, b_v) != make_fn(fo, fs1, fs2)(a_v, b_v))
            if sc.check() == sat:
                mc = sc.model()
                ca, cb = (mc.eval(a_v).as_long(), mc.eval(b_v).as_long())
                examples.append((ca, cb, ground_truth(ca, cb) & MASK32))
            print(f"  examples: {len(examples)}")
        else:
            return "timeout"
    return "exhausted"


def main():
    print("=" * 60)
    print(" swar int4 dot product — z3 verifier + cegis v3")
    print(f" z3 version: {get_version_string()}")
    print("=" * 60)
    print("\n> verifying swar approaches (SolverFor QF_BV)")
    print("\n1. direct nibble extract + sign extend (x^8)-8:")
    verify(candidate_direct_unpack, "direct-unpack")
    print("\n2. even/odd split + sign extend + byte extract:")
    verify(candidate_even_odd_split, "even-odd-split")
    print("\n3. perfect swar (reversed multiplier hack):")
    verify(candidate_perfect_swar, "perfect-swar")
    print("\n" + "=" * 60)
    print(" cegis: searching for minimal program")
    print("=" * 60)
    for d in [4, 5, 6, 7, 8]:
        print(f"\n--- depth {d} ---")
        r = cegis(d, timeout_ms=30000, max_rounds=15)
        if r == "unsat":
            continue
        elif r == "found":
            break
        else:
            print(f"  timeout at depth {d}, moving on...")
    print("\n" + "=" * 60)
    print(" done!")
    print("=" * 60)


if __name__ == "__main__":
    main()
