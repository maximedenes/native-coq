#define uint63_of_value(val) ((uint64)(val) >> 1)

/* 2^63 * y + x as a value */
#define Val_intint(x,y) ((value)(((uint64)(x)) << 1 + ((uint64)(y) << 64)))

#define uint63_zero ((value) 1) /* 2*0 + 1 */
#define uint63_one ((value) 3) /* 2*1 + 1 */

#define uint63_eq(x,y) ((x) == (y))
#define uint63_eq0(x) ((x) == (uint64)1)
#define uint63_lt(x,y) ((uint64) (x) < (uint64) (y))
#define uint63_leq(x,y) ((uint64) (x) <= (uint64) (y))

#define uint63_add(x,y) ((value)((uint64) (x) + (uint64) (y) - 1))
#define uint63_addcarry(x,y) ((value)((uint64) (x) + (uint64) (y) + 1))
#define uint63_sub(x,y) ((value)((uint64) (x) - (uint64) (y) + 1))
#define uint63_subcarry(x,y) ((value)((uint64) (x) - (uint64) (y) - 1))
#define uint63_mul(x,y) (Val_long(Long_val(x) * Long_val(y)))
#define uint63_div(x,y) (Val_long(Long_val(x) / Long_val(y)))
#define uint63_mod(x,y) (Val_long(Long_val(x) % Long_val(y)))

#define uint63_lxor(x,y) ((value)(((uint64)(x) ^ (uint64)(y)) | 1))
#define uint63_lor(x,y) ((value)((uint64)(x) | (uint64)(y)))
#define uint63_land(x,y) ((value)((uint64)(x) & (uint64)(y)))

/* TODO: is + or | better? OCAML uses + */
/* TODO: is - or ^ better? */
#define uint63_lsl(x,y) ((y) < (uint64) 127 ? ((value)((((uint64)(x)-1) << (uint63_of_value(y))) | 1)) : uint63_zero)
#define uint63_lsr(x,y) ((y) < (uint64) 127 ? ((value)(((uint64)(x) >> (uint63_of_value(y))) | 1)) : uint63_zero)
#define uint63_lsl1(x) ((value)((((uint64)(x)-1) << 1) +1))
#define uint63_lsr1(x) ((value)(((uint64)(x) >> 1) |1))

/* addmuldiv(p,x,y) = x * 2^p + y / 2 ^ (63 - p) */
/* (modulo 2^63) for p <= 63 */
value uint63_addmuldiv(p,x,y) {
  uint64 shiftby = uint63_of_value(p);
  value r = (value)((x^1) << shiftby);
  r = (value)(r | (((uint64)y) >> (63-shiftby)) | 1);
  return r;
}

value uint63_head0(uint64 x) {
  int r = 0;
  if (!(x & 0xFFFFFFFF00000000)) { x <<= 32; r += 32; }
  if (!(x & 0xFFFF000000000000)) { x <<= 16; r += 16; }
  if (!(x & 0xFF00000000000000)) { x <<= 8;  r += 8; }
  if (!(x & 0xF000000000000000)) { x <<= 4;  r += 4; }
  if (!(x & 0xC000000000000000)) { x <<= 2;  r += 2; }
  if (!(x & 0x8000000000000000)) { x <<=1;   r += 1; }
  return Val_int(r);
}

value uint63_tail0(uint64 x) {
  int r = 0;
  x >>= 1;
  if (!(x & 0xFFFFFFFF)) { x >>= 32; r += 32; }
  if (!(x & 0x0000FFFF)) { x >>= 16; r += 16; }
  if (!(x & 0x000000FF)) { x >>= 8;  r += 8; }
  if (!(x & 0x0000000F)) { x >>= 4;  r += 4; }
  if (!(x & 0x00000003)) { x >>= 2;  r += 2; }
  if (!(x & 0x00000001)) { x >>=1;   r += 1; }
  return Val_int(r);
}
