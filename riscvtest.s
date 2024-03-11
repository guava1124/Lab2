# riscvtest.s
# Sarah.Harris@unlv.edu
# David_Harris@hmc.edu
# 27 Oct 2020
#
# Test the RISC-V processor.  
#  add, sub, and, or, slt, addi, lw, sw, beq, jal
# If successful, it should write the value 25 to address 100

#       RISC-V Assembly         Description               Address   Machine Code
main:   addi x2, x0, 5          # x2 = 5                  0         00500113   
        addi x3, x0, 12         # x3 = 12                 4         00C00193
        addi x7, x3, -9         # x7 = (12 - 9) = 3       8         FF718393
        or   x4, x7, x2         # x4 = (3 OR 5) = 7       C         0023E233
        and  x5, x3, x4         # x5 = (12 AND 7) = 4     10        0041F2B3
        add  x5, x5, x4         # x5 = (4 + 7) = 11       14        004282B3
        beq  x5, x7, fail        # shouldn't be taken      18        02728863
        slt  x4, x3, x4         # x4 = (12 < 7) = 0       1C        0041A233
        beq  x4, x0, around     # should be taken         20        00020463
        addi x5, x0, 0          # shouldn't happen        24        00000293
around: slt  x4, x7, x2         # x4 = (3 < 5)  = 1       28        0023A233
        add  x7, x4, x5         # x7 = (1 + 11) = 12      2C        005203B3
        sub  x7, x7, x2         # x7 = (12 - 5) = 7       30        402383B3
        li   x7, 0x96
        li   x3, -3
        li   x5, -3
        sb   x3, 0(x7)          #storing -3 in x7 address 96
        lb   x4, 0(x7)          #loading the value -3 from address 96 into x4
        bne  x4, x5, fail       #checks if the process didn't work
        li   x3, 3          #putting 3 in reg x3
        li   x5, 3
        sb   x3, 0(x7)          #storing 3 in x7 address 96
        lbu  x4, 0(x7)          #loading unsigned value 3 from address 96 into x4
        bne  x4, x5, fail       #checks if the process didn't work
        li   x3, 0xffffffff
        li   x5, 0xffffffff
        sh   x3, 0(x7)          #storing 0xffffffff (negative number) in x7 address 96 
        lh   x4, 0(x7)          #loading the value 0xffffffff from address 96 into x4
        bne  x4, x5, fail       #checks if the process didn't work
        li   x3, 0x7fff     #loads 0111-1111-1111-1111 into x3
        li   x5, 0x7fff
        sh   x3, 0(x7)          #storing 0x7fff (positive number) in x7 address 96 
        lhu   x4, 0(x7)          #loading the value 0x7fff from address 96 into x4
        bne  x4, x5, fail       #checks if the process didn't work
        li   x3, 0xffffffff     #loads 0xffffffff into x3
        li   x5, 0xffffffff
        sw   x3, 0(x7)         # [96] = 7                34        0471AA23 
        lw   x4, 96(x0)         # x2 = [96] = 7           38        06002103 
        bne  x4, x5, fail       #checks if the process didn't work
pass:   ecall
fail:   ecall
end:

		
		