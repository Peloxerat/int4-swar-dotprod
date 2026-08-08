import Std.Tactic.BVDecide

def extract_unsigned_nibble (x : BitVec 32) (i : Nat) : BitVec 32 :=
  (x >>> (i * 4)) &&& 0xF#32

def extract_signed_nibble (a : BitVec 32) (i : Nat) : BitVec 32 :=
  let val := (a >>> (i * 4)) &&& 0xF#32
  if (val &&& 0x8#32) != 0#32 then
    val ||| 0xFFFFFFF0#32
  else
    val

def ground_truth_dot_product (a b : BitVec 32) : BitVec 32 :=
  (extract_signed_nibble a 0 * extract_signed_nibble b 0) +
  (extract_signed_nibble a 1 * extract_signed_nibble b 1) +
  (extract_signed_nibble a 2 * extract_signed_nibble b 2) +
  (extract_signed_nibble a 3 * extract_signed_nibble b 3) +
  (extract_signed_nibble a 4 * extract_signed_nibble b 4) +
  (extract_signed_nibble a 5 * extract_signed_nibble b 5) +
  (extract_signed_nibble a 6 * extract_signed_nibble b 6) +
  (extract_signed_nibble a 7 * extract_signed_nibble b 7)

def nibble_sum (x : BitVec 32) : BitVec 32 :=
  let even := x &&& 0x0F0F0F0F#32
  let odd := (x >>> 4) &&& 0x0F0F0F0F#32
  let byte_sums := even + odd
  let s := (byte_sums &&& 0x00FF00FF#32) + ((byte_sums >>> 8) &&& 0x00FF00FF#32)
  (s + (s >>> 16)) &&& 0xFF#32

def swar_dot_product (a b : BitVec 32) : BitVec 32 :=
  let au := a ^^^ 0x88888888#32
  let bu := b ^^^ 0x88888888#32
  
  let sa := nibble_sum au
  let sb := nibble_sum bu
  
  let ea := au &&& 0x0F0F0F0F#32
  let eb := bu &&& 0x0F0F0F0F#32
  let oa := (au >>> 4) &&& 0x0F0F0F0F#32
  let ob := (bu >>> 4) &&& 0x0F0F0F0F#32
  
  -- Even low
  let ea_low := ea &&& 0x00FF00FF#32
  let eb_low := eb &&& 0x00FF00FF#32
  let eb_low_rev := (eb_low >>> 16) ||| (eb_low <<< 16)
  let udp_even_low := (ea_low * eb_low_rev) >>> 16
  
  -- Even high
  let ea_high := (ea >>> 8) &&& 0x00FF00FF#32
  let eb_high := (eb >>> 8) &&& 0x00FF00FF#32
  let eb_high_rev := (eb_high >>> 16) ||| (eb_high <<< 16)
  let udp_even_high := (ea_high * eb_high_rev) >>> 16
  
  -- Odd low
  let oa_low := oa &&& 0x00FF00FF#32
  let ob_low := ob &&& 0x00FF00FF#32
  let ob_low_rev := (ob_low >>> 16) ||| (ob_low <<< 16)
  let udp_odd_low := (oa_low * ob_low_rev) >>> 16
  
  -- Odd high
  let oa_high := (oa >>> 8) &&& 0x00FF00FF#32
  let ob_high := (ob >>> 8) &&& 0x00FF00FF#32
  let ob_high_rev := (ob_high >>> 16) ||| (ob_high <<< 16)
  let udp_odd_high := (oa_high * ob_high_rev) >>> 16
  
  let udp := udp_even_low + udp_even_high + udp_odd_low + udp_odd_high
  
  -- Correction
  udp - (8#32 * sa) - (8#32 * sb) + 512#32

-- Леммы для декомпозиции
theorem lemma_nibble_sum (x : BitVec 32) :
  nibble_sum x =
    extract_unsigned_nibble x 0 + extract_unsigned_nibble x 1 +
    extract_unsigned_nibble x 2 + extract_unsigned_nibble x 3 +
    extract_unsigned_nibble x 4 + extract_unsigned_nibble x 5 +
    extract_unsigned_nibble x 6 + extract_unsigned_nibble x 7 := by
  unfold nibble_sum extract_unsigned_nibble; bv_decide

theorem lemma_even_low (au bu : BitVec 32) :
  let ea := au &&& 0x0F0F0F0F#32
  let eb := bu &&& 0x0F0F0F0F#32
  let ea_low := ea &&& 0x00FF00FF#32
  let eb_low := eb &&& 0x00FF00FF#32
  let eb_low_rev := (eb_low >>> 16) ||| (eb_low <<< 16)
  (ea_low * eb_low_rev) >>> 16 =
    extract_unsigned_nibble au 0 * extract_unsigned_nibble bu 0 +
    extract_unsigned_nibble au 4 * extract_unsigned_nibble bu 4 := by
  unfold extract_unsigned_nibble; bv_decide

theorem lemma_even_high (au bu : BitVec 32) :
  let ea := au &&& 0x0F0F0F0F#32
  let eb := bu &&& 0x0F0F0F0F#32
  let ea_high := (ea >>> 8) &&& 0x00FF00FF#32
  let eb_high := (eb >>> 8) &&& 0x00FF00FF#32
  let eb_high_rev := (eb_high >>> 16) ||| (eb_high <<< 16)
  (ea_high * eb_high_rev) >>> 16 =
    extract_unsigned_nibble au 2 * extract_unsigned_nibble bu 2 +
    extract_unsigned_nibble au 6 * extract_unsigned_nibble bu 6 := by
  unfold extract_unsigned_nibble; bv_decide

theorem lemma_odd_low (au bu : BitVec 32) :
  let oa := (au >>> 4) &&& 0x0F0F0F0F#32
  let ob := (bu >>> 4) &&& 0x0F0F0F0F#32
  let oa_low := oa &&& 0x00FF00FF#32
  let ob_low := ob &&& 0x00FF00FF#32
  let ob_low_rev := (ob_low >>> 16) ||| (ob_low <<< 16)
  (oa_low * ob_low_rev) >>> 16 =
    extract_unsigned_nibble au 1 * extract_unsigned_nibble bu 1 +
    extract_unsigned_nibble au 5 * extract_unsigned_nibble bu 5 := by
  unfold extract_unsigned_nibble; bv_decide

theorem lemma_odd_high (au bu : BitVec 32) :
  let oa := (au >>> 4) &&& 0x0F0F0F0F#32
  let ob := (bu >>> 4) &&& 0x0F0F0F0F#32
  let oa_high := (oa >>> 8) &&& 0x00FF00FF#32
  let ob_high := (ob >>> 8) &&& 0x00FF00FF#32
  let ob_high_rev := (ob_high >>> 16) ||| (ob_high <<< 16)
  (oa_high * ob_high_rev) >>> 16 =
    extract_unsigned_nibble au 3 * extract_unsigned_nibble bu 3 +
    extract_unsigned_nibble au 7 * extract_unsigned_nibble bu 7 := by
  unfold extract_unsigned_nibble; bv_decide

-- Леммы покомпонентного соответствия
theorem lemma_index_0 (a b : BitVec 32) :
  extract_unsigned_nibble (a ^^^ 0x88888888#32) 0 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 0 =
    extract_signed_nibble a 0 * extract_signed_nibble b 0 +
    8#32 * extract_unsigned_nibble (a ^^^ 0x88888888#32) 0 + 8#32 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 0 - 64#32 := by
  unfold extract_unsigned_nibble extract_signed_nibble; bv_decide

theorem lemma_index_1 (a b : BitVec 32) :
  extract_unsigned_nibble (a ^^^ 0x88888888#32) 1 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 1 =
    extract_signed_nibble a 1 * extract_signed_nibble b 1 +
    8#32 * extract_unsigned_nibble (a ^^^ 0x88888888#32) 1 + 8#32 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 1 - 64#32 := by
  unfold extract_unsigned_nibble extract_signed_nibble; bv_decide

theorem lemma_index_2 (a b : BitVec 32) :
  extract_unsigned_nibble (a ^^^ 0x88888888#32) 2 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 2 =
    extract_signed_nibble a 2 * extract_signed_nibble b 2 +
    8#32 * extract_unsigned_nibble (a ^^^ 0x88888888#32) 2 + 8#32 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 2 - 64#32 := by
  unfold extract_unsigned_nibble extract_signed_nibble; bv_decide

theorem lemma_index_3 (a b : BitVec 32) :
  extract_unsigned_nibble (a ^^^ 0x88888888#32) 3 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 3 =
    extract_signed_nibble a 3 * extract_signed_nibble b 3 +
    8#32 * extract_unsigned_nibble (a ^^^ 0x88888888#32) 3 + 8#32 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 3 - 64#32 := by
  unfold extract_unsigned_nibble extract_signed_nibble; bv_decide

theorem lemma_index_4 (a b : BitVec 32) :
  extract_unsigned_nibble (a ^^^ 0x88888888#32) 4 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 4 =
    extract_signed_nibble a 4 * extract_signed_nibble b 4 +
    8#32 * extract_unsigned_nibble (a ^^^ 0x88888888#32) 4 + 8#32 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 4 - 64#32 := by
  unfold extract_unsigned_nibble extract_signed_nibble; bv_decide

theorem lemma_index_5 (a b : BitVec 32) :
  extract_unsigned_nibble (a ^^^ 0x88888888#32) 5 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 5 =
    extract_signed_nibble a 5 * extract_signed_nibble b 5 +
    8#32 * extract_unsigned_nibble (a ^^^ 0x88888888#32) 5 + 8#32 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 5 - 64#32 := by
  unfold extract_unsigned_nibble extract_signed_nibble; bv_decide

theorem lemma_index_6 (a b : BitVec 32) :
  extract_unsigned_nibble (a ^^^ 0x88888888#32) 6 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 6 =
    extract_signed_nibble a 6 * extract_signed_nibble b 6 +
    8#32 * extract_unsigned_nibble (a ^^^ 0x88888888#32) 6 + 8#32 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 6 - 64#32 := by
  unfold extract_unsigned_nibble extract_signed_nibble; bv_decide

theorem lemma_index_7 (a b : BitVec 32) :
  extract_unsigned_nibble (a ^^^ 0x88888888#32) 7 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 7 =
    extract_signed_nibble a 7 * extract_signed_nibble b 7 +
    8#32 * extract_unsigned_nibble (a ^^^ 0x88888888#32) 7 + 8#32 * extract_unsigned_nibble (b ^^^ 0x88888888#32) 7 - 64#32 := by
  unfold extract_unsigned_nibble extract_signed_nibble; bv_decide

-- Главная теорема корректности
set_option maxHeartbeats 800000 in
theorem swar_is_correct (a b : BitVec 32) : swar_dot_product a b = ground_truth_dot_product a b := by
  unfold swar_dot_product ground_truth_dot_product
  dsimp
  rw [lemma_even_low, lemma_even_high, lemma_odd_low, lemma_odd_high, lemma_nibble_sum, lemma_nibble_sum]
  rw [lemma_index_0, lemma_index_1, lemma_index_2, lemma_index_3, lemma_index_4, lemma_index_5, lemma_index_6, lemma_index_7]
  -- After all rewrites, the goal is a pure algebraic identity over BitVec 32:
  -- Σ(signed_i + 8*ua_i + 8*ub_i - 64) - 8*Σ(ua_i) - 8*Σ(ub_i) + 512 = Σ(signed_i)
  -- Convert to Nat modular arithmetic and let omega handle the cancellation
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

