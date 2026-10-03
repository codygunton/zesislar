// ABI required by stock zesu d8071c4, src/zkvm/root.zig.
// ZisK v1.2.0-alpha terminates through syscall 93.
export fn zkvm_exit(code: i32) noreturn {
    asm volatile ("ecall"
        :
        : [code] "{a0}" (code),
          [syscall] "{a7}" (@as(u32, 93)),
        : .{ .memory = true });
    unreachable;
}
