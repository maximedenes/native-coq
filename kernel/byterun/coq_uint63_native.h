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

/* TODO: is + or | better? */
/* TODO: is - or ^ better? */
#define uint63_lsl(x,y) ((y) < (uint64) 127 ? ((value)((((uint64)(x)-1) << (uint63_of_value(y))) | 1)) : uint63_zero)
#define uint63_lsr(x,y) ((y) < (uint64) 127 ? ((value)(((uint64)(x) >> (uint63_of_value(y))) | 1)) : uint63_zero)
#define uint63_lsl1(x) ((value)((((uint64)(x)-1) << 1) +1))
#define uint63_lsr1(x) ((value)(((uint64)(x) >> 1) |1))

#define uint63_addmuldiv(p,x,y) ((value)((((x)^1) << (p)) | ((y) >> (63-(p))) | 1))
