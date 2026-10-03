/* The stock ZisK script supplies the complete guest heap bounds. */
.section .data,"aw",@progbits
.balign 8
.global ZKVM_HEAP_POS
.type ZKVM_HEAP_POS,@object
ZKVM_HEAP_POS:
.quad _heap_bottom
.size ZKVM_HEAP_POS,8
.global ZKVM_HEAP_TOP
.type ZKVM_HEAP_TOP,@object
ZKVM_HEAP_TOP:
.quad _heap_top
.size ZKVM_HEAP_TOP,8
