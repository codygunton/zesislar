/* Dedicated platform layer for the selected stock ZisK ELF. */
$include <prelude.sail>
$include <flow.sail>
$include <vector_dec.sail>

type xlenbits = bits(64)
type mem_meta = unit
union ExceptionType = {
  E_Fetch_Access_Fault : unit,
  E_Load_Access_Fault : unit,
  E_SAMO_Access_Fault : unit
}
union AccessType ('a : Type) = { Read : 'a, Write : 'a, Execute : unit }
union MemoryOpResult ('a : Type) = { MemValue : 'a, MemException : ExceptionType }
enum write_kind = { Write_plain, Write_RISCV_release, Write_RISCV_strong_release,
 Write_RISCV_conditional, Write_RISCV_conditional_release,
 Write_RISCV_conditional_strong_release }
register zisk_input_end : bits(64)
register zisk_free_input : bits(64)

/* These declarations link to byte-identical pinned model implementations. */
val phys_mem_read : forall 'n, 0 < 'n <= 8.
 (AccessType(unit), xlenbits, atom('n), bool, bool, bool, bool) -> MemoryOpResult((bits(8 * 'n), unit))
val phys_mem_write : forall 'n, 0 < 'n <= 8.
 (write_kind, xlenbits, atom('n), bits(8 * 'n), unit) -> MemoryOpResult(bool)

val zisk_width : int -> bool
function zisk_width(w) = w == 1 | w == 2 | w == 4 | w == 8

/* Integer endpoints reject wrap and the complete access must fit. */
val zisk_contains : (bits(64), int, int, int) -> bool
function zisk_contains(a, w, lo, hi) =
 zisk_width(w) & unsigned(a) >= lo & unsigned(a) + w <= hi

val checked_mem_read : forall 'n, 0 < 'n <= 8.
 (AccessType(unit), xlenbits, atom('n), bool, bool, bool, bool) -> MemoryOpResult((bits(8 * 'n), unit))
function checked_mem_read(t, a, w, aq, rl, res, meta) = {
 match t {
  Execute() => if zisk_contains(a, w, 2147483648, 2148597112)
   then phys_mem_read(t, a, w, aq, rl, res, meta)
   else MemException(E_Fetch_Access_Fault()),
  Read(_) => {
   if zisk_contains(a, w, 2684354560, 3221225472)
   then phys_mem_read(t, a, w, aq, rl, res, meta)
   else if unsigned(a) == 1073741824 & w == 8
   then MemValue(sail_zero_extend(zisk_free_input, 8 * w), ())
   else if (zisk_contains(a, w, 1073741824, 2147483648) &
            zisk_contains(a, w, 1073741824, unsigned(zisk_input_end))) |
           zisk_contains(a, w, 2148597120, 2148632184)
   then phys_mem_read(t, a, w, aq, rl, res, meta)
   else if zisk_contains(a, w, 1073741832, 2147483648)
   then MemValue(sail_zero_extend(0b0, 8 * w), ())
   else MemException(E_Load_Access_Fault())
  },
  _ => MemException(E_SAMO_Access_Fault())
 }
}

val checked_mem_write : forall 'n, 0 < 'n <= 8.
 (write_kind, xlenbits, atom('n), bits(8 * 'n), unit) -> MemoryOpResult(bool)
function checked_mem_write(wk, a, w, data, meta) =
 if zisk_contains(a, w, 2684354560, 3221225472)
 then phys_mem_write(wk, a, w, data, meta)
 else MemException(E_SAMO_Access_Fault())

val within_phys_mem : (bits(64), int) -> bool
function within_phys_mem(a, w) =
 zisk_contains(a, w, 1073741824, 2147483648) |
 zisk_contains(a, w, 2147483648, 2148597112) |
 zisk_contains(a, w, 2148597120, 2148632184) |
 zisk_contains(a, w, 2684354560, 3221225472)

val within_mmio_readable : (bits(64), int) -> bool
function within_mmio_readable(a, w) = false
val within_mmio_writable : (bits(64), int) -> bool
function within_mmio_writable(a, w) = false

/* Test entry point for the instruction-fetch platform hook. */
register x10 : bits(64)
val check_cycle_count = "cycle_count" : unit -> unit
val zisk_smoke_fetch : bits(32) -> unit
function zisk_smoke_fetch(address) = {
 check_cycle_count();
 let result = checked_mem_read(Execute(), sail_zero_extend(address, 64), 4, false, false, false, false);
 x10 = match result { MemValue(_) => 0x0000000000000001, MemException(_) => 0x0000000000000000 };
 ()
}
