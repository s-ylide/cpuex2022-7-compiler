# cpuex2022-7-compiler

2022 年度 CPU 実験 7 班のコンパイラです．

CPU 実験で配布されるレイトレーシングプログラムのコードは含まれていません．

CPU 実験で使用する場合に限りライセンスの明記は不要とします．

## ISA (1st/2nd)

| format | mnemonic |       full name        | description                  | opcode | funct3 |
| :----: | :------- | :--------------------: | :--------------------------- | :----: | :----: |
|   R    | add      |          add           | `rd = rs1 + rs2`             |  0000  |   0    |
|   R    | xor      |          xor           | `rd = rs1 ^ rs2`             |  0000  |   4    |
|   R    | min      |        minimum         | `rd = min(rs1, rs2)`         |  0000  |   1    |
|   R    | max      |        maximum         | `rd = max(rs1, rs2)`         |  0000  |   3    |
|   I    | addi     |     add immediate      | `rd = rs1 + rs2`             |  0010  |   0    |
|   I    | xori     |     xor immediate      | `rd = rs1 ^ rs2`             |  0010  |   4    |
|   I    | slli     | shift left logical imm | `rd = rs1 << imm[0:4]`       |  0010  |   2    |
|   I    | lw       |       load word        | `rd = M[rs1+imm]`            |  0110  |   f3   |
|   S    | sw       |       store word       | `M[rs1+imm] = rs2`           |  0100  |   f3   |
|   B    | beq      |      branch if eq      | `if(rs1 eq rs2) PC += imm`   |  1000  |   0    |
|   B    | bne      |      branch if ne      | `if(rs1 ne rs2) PC += imm`   |  1000  |   1    |
|   B    | blt      |      branch if lt      | `if(rs1 lt rs2) PC += imm`   |  1000  |   4    |
|   B    | bge      |      branch if ge      | `if(rs1 ge rs2) PC += imm`   |  1000  |   5    |
|   B    | bxor     |     branch if xor      | `if(rs1 xor rs2) PC += imm`  |  1000  |   2    |
|   B    | bxnor    |     branch if xnor     | `if(rs1 xnor rs2) PC += imm` |  1000  |   3    |
|   P    | beqi     |    branch if eq imm    | `if(rs1 eq imm2) PC += imm1` |  1100  |   0    |
|   P    | bnei     |    branch if ne imm    | `if(rs1 ne imm2) PC += imm1` |  1100  |   1    |
|   P    | blti     |    branch if lt imm    | `if(rs1 lt imm2) PC += imm1` |  1100  |   4    |
|   P    | bgei     |    branch if ge imm    | `if(rs1 ge imm2) PC += imm1` |  1100  |   5    |
|   P    | bgti     |    branch if gt imm    | `if(rs1 gt imm2) PC += imm1` |  1100  |   6    |
|   P    | blei     |    branch if le imm    | `if(rs1 le imm2) PC += imm1` |  1100  |   7    |
|   J    | jal      |     jump and link      | `rd = PC+4; PC += imm`       |  1110  |   -    |
|   I    | jalr     |   jump and link reg    | `rd = PC+4; PC = rs1 + imm`  |  1010  |   0    |

| format | mnemonic       | full name               | description                                       | opcode | funct3 | funct5 | funct2 | sign |
| :----: | :------------- | ----------------------- | ------------------------------------------------- | ------ | ------ | ------ | ------ | ---- |
|   E    | fadd           | flt add                 | `f[rd] = f[rs1] + f[rs2]`                         | 0001   | 000    | 00000  | 00     |      |
|   E    | fsub           | flt sub                 | `f[rd] = f[rs1] - f[rs2]`                         | 0001   | 000    | 00001  | 00     |      |
|   E    | fmul           | flt mul                 | `f[rd] = f[rs1] * f[rs2]`                         | 0001   | 000    | 00010  | 00     |      |
|   E    | fdiv           | flt div                 | `f[rd] = f[rs1] / f[rs2]`                         | 0001   | 000    | 00011  | 00     |      |
|   G    | fmadd          | flt fused mul-add       | `f[rd] = f[rs1] * f[rs2] + f[rs3]`                | 0001   | 001    |        |        | 0    |
|   G    | fmsub          | flt fused mul-sub       | `f[rd] = f[rs1] * f[rs2] - f[rs3]`                | 0001   | 010    |        |        | 0    |
|   G    | fnmadd         | flt neg fused mul-add   | `f[rd] = -f[rs1] * f[rs2] + f[rs3]`               | 0001   | 101    |        |        | 0    |
|   G    | fnmsub         | flt neg fused mul-sub   | `f[rd] = -f[rs1] * f[rs2] - f[rs3]`               | 0001   | 110    |        |        | 0    |
|   H    | fsqrt          | flt sqrt                | `f[rd] = sqrt(f[rs1])`                            | 0001   | 000    | 00100  | 00     |      |
|   H    | fhalf          | flt half                | `f[rd] = f[rs1] / 2.0`                            | 0001   | 000    | 00101  | 00     |      |
|   H    | finv           | flt inverse             | `f[rd] = 1.0 / f[rs1]`                            | 0001   | 000    | 01011  | 00     |      |
|   E    | fsgnj          | flt sign injection      | `f[rd] = {f[rs2][31], f[rs1][30:0]}`              | 0001   | 000    | 00110  | 00     |      |
|   E    | fsgnjn         | flt sign neg injection  | `f[rd] = {~f[rs2][31], f[rs1][30:0]}`             | 0001   | 000    | 00111  | 00     |      |
|   E    | fsgnjx         | flt sign xor injection  | `f[rd] = {f[rs1][31] ^ f[rs2][31], f[rs1][30:0]}` | 0001   | 000    | 01000  | 00     |      |
|   H    | ffloor         | flt floor               | `f[rd] = floor(f[rs1])`                           | 0001   | 000    | 01001  | 00     |      |
|   K    | flt            | float less than         | `x[rd] = f[rs1] < f[rs2]`                         | 0001   | 001    | 10100  | 01     |      |
|   Y    | fiszero (feqz) | float equal to zero     | `x[rd] = f[rs1] == 0`                             | 0001   | 100    | 10100  | 01     |      |
|   Y    | fispos (fgtz)  | float greater than zero | `x[rd] = f[rs1] > 0`                              | 0001   | 101    | 10100  | 01     |      |
|   Y    | fisneg (fltz)  | float less than zero    | `x[rd] = f[rs1] < 0`                              | 0001   | 110    | 10100  | 01     |      |
|   Y    | fftoi          | float to int            | `x[rd] = round(f[rs1])`                           | 0001   | 000    | 10001  | 01     |      |
|   X    | fitof          | int to float            | `f[rd] = float(x[rs1])`                           | 0001   | 000    | 11001  | 10     |      |
|   W    | fblt           | branch if float lt      | branch if `f[rs1] < f[rs2]`                       | 1001   | 001    |        |        |      |
|   W    | fbge           | branch if float ge      | branch if `f[rs1] < f[rs2]`                       | 1001   | 010    |        |        |      |
|   V    | fbeqz          | branch if float eq zero | branch if `f[rs1] == 0`                           | 1001   | 100    |        |        |      |
|   V    | fbnez          | branch if float ne zero | branch if `f[rs1] != 0`                           | 1001   | 111    |        |        |      |
|   V    | fbgtz          | branch if float gt zero | branch if `f[rs1] > 0`                            | 1001   | 101    |        |        |      |
|   V    | fbltz          | branch if float lt zero | branch if `f[rs1] < 0`                            | 1001   | 110    |        |        |      |
|   FI   | flw            | load float              | `f[rd] = M[x[rs1] + sext(imm)][31:0]`             | 0111   | f3     |        |        |      |
|   FS   | fsw            | store float             | `M[x[rs1] + sext(imm)] = f[rs2][31:0]`            | 0101   | f3     |        |        |      |

| format | mnemonic |     full name      | opcode | funct3 |
| :----: | :------- | :----------------: | :----: | :----: |
|   IO   | inw      |     read word      |  0011  |  001   |
|   IO   | outb     |     write byte     |  0011  |  010   |
|   IO   | finw     | read word as float |  0011  |  100   |

### ISA format (1st)

| name |    1    |       6       |      5       |     5      |     3      |      5       |    7    |
| :--: | :-----: | :-----------: | :----------: | :--------: | :--------: | :----------: | :-----: |
|      |   31    |     30:25     |    24:20     |   19:15    |   14:12    |     11:7     |   6:0   |
|  R   | funct7  |               |     rs2      |    rs1     |     f3     |      rd      | opcode  |
|  I   | imm[11] |   imm[10:5]   |   imm[4:0]   |    rs1     |     f3     |      rd      | opcode  |
|  S   | imm[11] |   imm[10:5]   |     rs2      |    rs1     |     f3     |   imm[4:0]   | opcode  |
|  B   | imm[12] |   imm[10:5]   |     rs2      |    rs1     |     f3     | imm[4:1\|11] | opcode  |
|  J   | imm[20] |   imm[10:5]   | imm[4:1\|11] | imm[19:15] | imm[14:12] |      rd      | opcode  |
|      |         |               |              |            |            |              |         |
|  E   |         |  fpu_control  |     frs2     |    frs1    |    000     |     frd      | 1010011 |
|  H   |         |  fpu_control  |    00000     |    frs1    |    000     |     frd      | 1010011 |
|  K   |         |  fpu_control  |     frs2     |    frs1    |    001     |      rd      | 1010011 |
|  X   |         |  fpu_control  |    00000     |    rs1     |    000     |     frd      | 1010011 |
|  Y   |         |  fpu_control  |    00000     |    frs1    |     f3     |      rd      | 1010011 |
|  V   |         | imm[12\|10:5] |    00000     |    frs1    |     f3     | imm[4:1\|11] | 1010111 |
|  W   |         | imm[12\|10:5] |     frs2     |    frs1    |     f3     | imm[4:1\|11] | 1010111 |
|  FI  |         |   imm[11:5]   |   imm[4:0]   |    rs1     |    010     |      rd      | 0000111 |
|  FS  |         |   imm[11:5]   |     rs2      |    rs1     |    010     |   imm[4:0]   | 0100111 |

### ISA format (2nd)

| name |      1      |     6     |        6        |     6      |     3      |        6        |   4    |
| :--: | :---------: | :-------: | :-------------: | :--------: | :--------: | :-------------: | :----: |
|      |     31      |   30:25   |      24:19      |   18:13    |   12:10    |       9:4       |  3:0   |
|  R   |      0      |  000000   |       rs2       |    rs1     |     f3     |       rd        |  0000  |
|  I   |   imm[12]   | imm[11:6] |    imm[5:0]     |    rs1     |     f3     |       rd        | opcode |
|  S   |   imm[12]   | imm[11:6] |       rs2       |    rs1     |     f3     |    imm[5:0]     |  0100  |
|  B   |   imm[14]   | imm[11:6] |       rs2       |    rs1     |     f3     | imm[5:2\|13:12] |  1000  |
|  P   |   imm[14]   | imm[11:6] |    imm2[5:0]    |    rs1     |     f3     | imm[5:2\|13:12] |  1100  |
|  J   |   imm[23]   | imm[11:6] | imm[5:2\|13:12] | imm[22:17] | imm[16:14] |       rd        |  1110  |
|      |             |           |                 |            |            |                 |        |
|  E   | fpu_control |    ->     |      frs2       |    frs1    |    000     |       frd       |  0001  |
|  G   |      0      |   frs3    |      frs2       |    frs1    |     f3     |       frd       |  0001  |
|  H   | fpu_control |    ->     |      00000      |    frs1    |    000     |       frd       |  0001  |
|  K   | fpu_control |    ->     |      frs2       |    frs1    |    001     |       rd        |  0001  |
|  X   | fpu_control |    ->     |      00000      |    rs1     |    000     |       frd       |  0001  |
|  Y   | fpu_control |    ->     |      00000      |    frs1    |     f3     |       rd        |  0001  |
|  V   |   imm[14]   | imm[11:6] |      00000      |    frs1    |     f3     | imm[5:2\|13:12] |  1001  |
|  W   |   imm[14]   | imm[11:6] |      frs2       |    frs1    |     f3     | imm[5:2\|13:12] |  1001  |
|  FI  |   imm[12]   | imm[11:6] |    imm[5:0]     |    rs1     |     f3     |       rd        |  0111  |
|  FS  |   imm[12]   | imm[11:6] |       rs2       |    rs1     |     f3     |    imm[5:0]     |  0101  |
