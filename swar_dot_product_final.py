import random


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


def ground_truth_dot_product(ap, bp):
    return sum((a * b for a, b in zip(unpack_int4(ap), unpack_int4(bp))))


def swar_dot_product(a, b):
    au = a ^ 2290649224
    bu = b ^ 2290649224

    def nibble_sum(x):
        even = x & 252645135
        odd = x >> 4 & 252645135
        byte_sums = even + odd
        s = (byte_sums & 16711935) + (byte_sums >> 8 & 16711935)
        return s + (s >> 16) & 255

    sa = nibble_sum(au)
    sb = nibble_sum(bu)
    ea = au & 252645135
    eb = bu & 252645135
    oa = au >> 4 & 252645135
    ob = bu >> 4 & 252645135
    ea_low = ea & 16711935
    eb_low = eb & 16711935
    eb_low_rev = (eb_low >> 16 | eb_low << 16) & 4294967295
    udp_even_low = (ea_low * eb_low_rev & 4294967295) >> 16
    ea_high = ea >> 8 & 16711935
    eb_high = eb >> 8 & 16711935
    eb_high_rev = (eb_high >> 16 | eb_high << 16) & 4294967295
    udp_even_high = (ea_high * eb_high_rev & 4294967295) >> 16
    oa_low = oa & 16711935
    ob_low = ob & 16711935
    ob_low_rev = (ob_low >> 16 | ob_low << 16) & 4294967295
    udp_odd_low = (oa_low * ob_low_rev & 4294967295) >> 16
    oa_high = oa >> 8 & 16711935
    ob_high = ob >> 8 & 16711935
    ob_high_rev = (ob_high >> 16 | ob_high << 16) & 4294967295
    udp_odd_high = (oa_high * ob_high_rev & 4294967295) >> 16
    udp = udp_even_low + udp_even_high + udp_odd_low + udp_odd_high
    res = udp - 8 * sa - 8 * sb + 512
    return res & 4294967295


def run_tests(num_tests=1000000):
    print(f"running {num_tests} tests...")
    passed = 0
    random.seed(42)
    for i in range(num_tests):
        a_arr = [random.randint(-8, 7) for _ in range(8)]
        b_arr = [random.randint(-8, 7) for _ in range(8)]
        a_packed = pack_int4(a_arr)
        b_packed = pack_int4(b_arr)
        expected = ground_truth_dot_product(a_packed, b_packed) & 4294967295
        actual = swar_dot_product(a_packed, b_packed)
        if expected == actual:
            passed += 1
        else:
            print(f"test {i + 1} failed!")
            print(f"  a: {a_arr}")
            print(f"  b: {b_arr}")
            print(f"  expected (gt): {expected}")
            print(f"  got (swar): {actual}")
            break
    if passed == num_tests:
        print(f"success! all {passed} tests passed. swar hack is solid.")
    else:
        print("tests failed with errors.")


if __name__ == "__main__":
    run_tests()
