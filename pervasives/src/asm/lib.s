.text
.create_array_int:
  mv  a2, a0
  mv  a0, hp
  add hp, hp, a2
  mv  a2, a0
.loop_create_array_int:
  sw  a1, 0(a2)
  addi  a2, a2, 1
  blt a2, hp, .loop_create_array_int
  ret
.create_array_float:
  mv  a2, a0
  mv  a0, hp
  add hp, hp, a2
  mv  a2, a0
.loop_create_array_float:
  fsw fa0, 0(a2)
  addi  a2, a2, 1
  blt a2, hp, .loop_create_array_float
  ret
.print_128:
  li  a0, 49
  li  a1, 50
  li  a2, 56
  outb  a0
  outb  a1
  outb  a2
  ret
.print_255:
  li  a0, 50
  li  a1, 53
  outb  a0
  outb  a1
  outb  a1
  ret
.print_512:
  li  a0, 53
  li  a1, 49
  li  a2, 50
  outb  a0
  outb  a1
  outb  a2
  ret
.print_16:
  li  a0, 49
  li  a1, 54
  outb  a0
  outb  a1
  ret
.print_4:
  li  a0, 52
  outb  a0
  ret
.print_int:
  li  a1, 128
  li  a2, 255
  beq a0, a1, .print_128
  beq a0, a2, .print_255
  li  a1, 512
  li  a2, 16
  beq a0, a1, .print_512
  li  a1, 4
  beq a0, a2, .print_16
  beq a0, a1, .print_4
  ret
