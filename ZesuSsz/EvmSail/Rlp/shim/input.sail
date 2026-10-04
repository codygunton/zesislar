/* The register contains the complete immutable input envelope. The evaluator
 * installs it after sail_model_init. Upstream host/region_access.sail:16-18
 * requires an in-bounds byte access. Lines 82-88 specify a big-endian word,
 * zero padding past the slice end. Lines 153-162 guard byte_at with off < len;
 * lines 405-419 guard load_n_word with off < len.
 */
register shim_input_bytes : list(byte) = [||]

val shim_input_length : list(byte) -> int
function shim_input_length(bytes) =
    match bytes {
        [||] => 0,
        _ :: tail => 1 + shim_input_length(tail),
    }

val shim_byte_at : (list(byte), int) -> byte
function shim_byte_at(bytes, index) =
    match bytes {
        [||] => { assert(false, "input index outside backing bytes"); 0x00 },
        head :: tail => if index == 0 then head else shim_byte_at(tail, index - 1),
    }

function stateless_input_byte_at(s, off) = {
    assert(0 <= s.bytes & 0 <= s.len & s.bytes + s.len <= shim_input_length(shim_input_bytes),
           "input slice outside backing bytes");
    assert(0 <= off & off < s.len, "input byte offset outside slice");
    shim_byte_at(shim_input_bytes, s.bytes + off)
}

val shim_load_n : (StatelessInputSlice, int, int, int) -> int
function shim_load_n(s, off, remaining, value) =
    if remaining == 0 then value
    else {
        let next = if off < s.len then unsigned(shim_byte_at(shim_input_bytes, s.bytes + off)) else 0;
        shim_load_n(s, off + 1, remaining - 1, value * 256 + next)
    }
termination_measure shim_load_n(s, off, remaining, value) = remaining

function stateless_input_load_n_word(s, off, n) = {
    assert(0 <= s.bytes & 0 <= s.len & s.bytes + s.len <= shim_input_length(shim_input_bytes),
           "input slice outside backing bytes");
    assert(0 <= off & off < s.len, "input word offset outside slice");
    word_from_bits(get_slice_int(256, shim_load_n(s, off, n, 0), 0))
}
