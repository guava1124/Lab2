// riscvsingle.sv

// RISC-V single-cycle processor
// From Section 7.6 of Digital Design & Computer Architecture
// 27 April 2020
// David_Harris@hmc.edu 
// Sarah.Harris@unlv.edu

// run 210
// Expect simulator to print "Simulation succeeded"
// when the value 25 (0x19) is written to address 100 (0x64)

//   Instruction  opcode    funct3    funct7
//   add          0110011   000       0000000
//   sub          0110011   000       0100000
//   and          0110011   111       0000000
//   or           0110011   110       0000000
//   slt          0110011   010       0000000
//   addi         0010011   000       immediate
//   andi         0010011   111       immediate
//   ori          0010011   110       immediate
//   slti         0010011   010       immediate
//   beq          1100011   000       immediate
//   lw	          0000011   010       immediate
//   sw           0100011   010       immediate
//   jal          1101111   immediate immediate

module testbench();

   logic        clk;
   logic        reset;

   logic [31:0] WriteData;
   logic [31:0] DataAdr;
   logic        MemWrite;

   // instantiate device to be tested
   top dut(clk, reset, WriteData, DataAdr, MemWrite);

   initial
     begin
	string memfilename;
        memfilename = {"../riscvtest/riscvtest.memfile"}; //../riscvtest/riscvtest.memfile //../proj1Tests/testing/sb.memfile
        $readmemh(memfilename, dut.imem.RAM);
     end

   
   // initialize test
   initial
     begin
	reset <= 1; # 22; reset <= 0;
     end

   // generate clock to sequence tests
   always
     begin
	clk <= 1; # 5; clk <= 0; # 5;
     end
  /*
   // check results, used for the riscv test debugging, not needed except for that.
   always @(negedge clk)
     begin
	if(MemWrite) begin
           if(DataAdr === 100 & WriteData === 25) begin
              $display("Simulation succeeded");
              $stop;
           end else if (DataAdr !== 96) begin
              $display("Simulation failed");
              $stop;
           end
	end
     end
  */
endmodule // testbench

module riscvsingle (input logic clk, reset, //just under top of the modules, instantiates logic modules for controllers, and datapath signals 
		    output logic [31:0] PC,
		    input  logic [31:0] Instr,
		    output logic 	MemWrite,
		    output logic [31:0] ALUResult, WriteData,
        output logic [2:0] funct3,
		    input  logic [31:0] ReadData);
   
   logic ALUSrc, RegWrite, Jump, Zero, v, n, cout;
   logic [1:0] ResultSrc, PCSrc;
   logic [2:0] ImmSrc;
   logic [3:0] ALUControl;
   
   controller c (Instr[6:0], Instr[14:12], Instr[30], Zero, v, n, cout,
		 ResultSrc, MemWrite, PCSrc,
		 ALUSrc, RegWrite, Jump,
		 ImmSrc, ALUControl);
   datapath dp (clk, reset, ResultSrc, PCSrc,
		ALUSrc, RegWrite,
		ImmSrc, ALUControl,
		Zero, v, n, cout, PC, Instr,
		ALUResult, WriteData, funct3, ReadData);
   
endmodule // riscvsingle

module controller (input  logic [6:0] op, //controller instantiates the controller logic, along with the main decoder and alu decoder
		   input  logic [2:0] funct3,
		   input  logic       funct7b5,
		   input  logic       Zero, v, n, cout,
		   output logic [1:0] ResultSrc,
		   output logic       MemWrite,
		   output logic [1:0] PCSrc,
       output logic       ALUSrc,
		   output logic       RegWrite, Jump,
		   output logic [2:0] ImmSrc,
		   output logic [3:0] ALUControl);
   
   logic [1:0] ALUOp;
   logic Branch;
   
   maindec md (op, ResultSrc, MemWrite, Branch, //instantiates the main decoder module
	       ALUSrc, RegWrite, Jump, ImmSrc, ALUOp);
   aludec ad (op[5], funct3, funct7b5, ALUOp, op, ALUControl); //instantiates the alu decoder module


    //checks beq or bne and jal and branches on successful compare
    always_comb
    begin
      //checks bne and beq, jal, blt, bge, bltu, bgeu
      if((Branch & (funct3 == 3'b000 | funct3 == 3'b001) & (Zero ^ funct3[0])) == 1 | (Jump & op == 7'b1101111) == 1 | (funct3 == 3'b100 & Branch & (n ^ v)) | (funct3 == 3'b101 & Branch & (~(n ^ v) | Zero)) | (funct3 == 3'b110 & Branch & ~cout) | (funct3 == 3'b111 & Branch & (cout | Zero))) //logic for deciding if the pc uses the +4 or branch option if branch instruction is detected for branchsignal, & with zero check or if jump is flagged, then it will use different pc source
        PCSrc = 2'b01; 
      
      else if((Jump & op == 7'b1100111) == 1) //checks for jalr
        PCSrc = 2'b10; 
    
      else //just do pc + 4 on a failed check branch or something
        PCSrc = 2'b00;
    end
   
   //{instr[31:12], {12{0}}}

endmodule // controller

module maindec (input  logic [6:0] op, //main decoder takes logic and makes an 11 bit controller signal which takes in the opcode and sets the corresponding control values based on the opcode.
		output logic [1:0] ResultSrc,
		output logic 	   MemWrite,
		output logic 	   Branch, ALUSrc,
		output logic 	   RegWrite, Jump,
		output logic [2:0] ImmSrc,
		output logic [1:0] ALUOp);
   
   logic [11:0] 		   controls;
   
   //assigns continuously control signals based on the opcode input.
   assign {RegWrite, ImmSrc, ALUSrc, MemWrite,
	   ResultSrc, Branch, ALUOp, Jump} = controls;
   
   always_comb
     case(op)
     //we will need to make sure this is all 12bits long because we are adding another bit for the immediates.
       // RegWrite_ImmSrc_ALUSrc_MemWrite_ResultSrc_Branch_ALUOp_Jump
       7'b0000011: controls = 12'b1_000_1_0_01_0_00_0; // lw
       7'b0100011: controls = 12'b0_001_1_1_xx_0_00_0; // sw or maybe all of s types?
       7'b0110011: controls = 12'b1_xxx_0_0_00_0_10_0; // R–type
       7'b1100011: controls = 12'b0_010_0_0_00_1_01_0; // beq
       7'b0010011: controls = 12'b1_000_1_0_00_0_10_0; // I–type ALU
       7'b1101111: controls = 12'b1_011_0_0_10_0_00_1; // jal
       7'b0110111: controls = 12'b1_100_1_0_00_0_11_0; // lui
       7'b0010111: controls = 12'b1_100_x_0_11_0_xx_0;  //auipc
       7'b1100111: controls = 12'b1_000_1_0_10_0_00_1;  //jalr
       default: controls = 12'bx_xxx_x_x_xx_x_xx_x; // ???
     endcase // case (op)
   
endmodule // maindec

module aludec (input  logic       opb5, //alu decoder takes in logic from instruction required by the alu, then sets the alu to perform the specified operation based on brancing logic in case statements.
	       input  logic [2:0] funct3,
	       input  logic 	  funct7b5,
	       input  logic [1:0] ALUOp,
         input  logic [6:0] op,
	       output logic [3:0] ALUControl);
   
   logic 			  RtypeSub;
   logic        SraType;
   
   assign RtypeSub = funct7b5 & opb5; // TRUE for checking if there is an R–type subtraction
   assign SraType = funct7b5; // TRUE for checking if there is an sra type in the R-type or I-types
   always_comb
     case(ALUOp)
       2'b00: ALUControl = 4'b0000; // addition for non-regular R or I types
       2'b01: ALUControl = 4'b0001; // subtraction for branch instructions
       2'b11: case(op) //branch type alu stuff that's not beq or bne
              7'b0110111: ALUControl = 4'b1001; //lui instruction
              //7'b0010111: ALUControl = 4'b1001; //auipc instruction, not needed because you can use pctarget instead for the result
              default: ALUControl = 3'bxxx; // ???
              endcase
       default: case(funct3) // R–type or I–type ALU
                  3'b000: if (RtypeSub)
                    ALUControl = 4'b0001; // sub
                  else
                    ALUControl = 4'b0000; // add, addi
                  3'b010: ALUControl = 4'b0101; // slt, slti, funct3 2
                  3'b011: ALUControl = 4'b1011; // sltu, sltiu, funct3 3
                  3'b110: ALUControl = 4'b0011; // or, ori, funct3 6
                  3'b111: ALUControl = 4'b0010; // and, andi, funct3 7
                  3'b100: ALUControl = 4'b0100; //xor, xori, funct3 4
                  3'b001: ALUControl = 4'b0111; //sll, slli, funct3 1
                  3'b101: if(SraType)
                    ALUControl = 4'b0110; //sra, srai, funct3 5
                  else
                    ALUControl = 4'b1000; //srl, srli, funct3 5

                  default: ALUControl = 4'bxxxx; // ???
                endcase // case (funct3)       
     endcase // case (ALUOp)
   
endmodule // aludec

module datapath (input logic clk, reset,
		 input  logic [1:0]  ResultSrc,
		 input  logic [1:0]  PCSrc,
     input  logic 	     ALUSrc,
		 input  logic 	     RegWrite,
		 input  logic [2:0]  ImmSrc,
		 input  logic [3:0]  ALUControl,
		 output logic 	     Zero, v, n, cout,
		 output logic [31:0] PC,
		 input  logic [31:0] Instr,
		 output logic [31:0] ALUResult, WriteData,
     output logic [2:0] funct3,
		 input  logic [31:0] ReadData);
   
   logic [31:0] 		     PCNext, PCPlus4, PCTarget;
   logic [31:0] 		     ImmExt;
   logic [31:0] 		     SrcA, SrcB;
   logic [31:0] 		     Result;
   logic [31:0]          RD; //read data from Imem after muxes

   assign funct3 = Instr[14:12];
   
   //adds the connections to the modules that make up the single cycle cpu such as the register file, pc counter register, pc add + 4, and pc add branch, and sign extension, and srcbmux, and the alu, and the result mux from the alu
   // next PC logic
   flopr #(32) pcreg (clk, reset, PCNext, PC);
   adder  pcadd4 (PC, 32'd4, PCPlus4);
   adder  pcaddbranch (PC, ImmExt, PCTarget);
   mux4 #(32)  pcmux (PCPlus4, PCTarget, ALUResult, PCPlus4, PCSrc,PCNext); //4 way mux to select the PCNext, d3(11) set to default to PCPlus4 in the event of a bit error, ALUresult 2'b10 is for Jalr where PC = rs1 + imm
   // register file logic
   regfile  rf (clk, RegWrite, Instr[19:15], Instr[24:20], //instantiation of the register file
	       Instr[11:7], Result, SrcA, WriteData);
   extend  ext (Instr[31:7], ImmSrc, ImmExt);
   // ALU logic
   mux2 #(32)  srcbmux (WriteData, ImmExt, ALUSrc, SrcB); //mux for using either rd2 or immediate extension
   alu  alu (SrcA, SrcB, ALUControl, ALUResult, Zero, v, n, cout); 
   //the following are the required resultsrc values for the mux: //(PCTarget) = 2'b11, (PCPlus4) = 2'b10, (ReadData) = 2'b01, (ALUResult) = 2'b00 for the resultMux
   mux4 #(32) resultmux (ALUResult, ReadData, PCPlus4, PCTarget, ResultSrc, Result); //mux for the output of the result signal Needs to have a connection from PC Target so that we can use the result for AUIPC going to wd3, then we make the pc mux go to pc + 4 becasue jump aint ready yet.
   //subWordByteMask ImemByteMask(SrcB, ALUResult, Instr[14:12], funct3);
   //subWordRead ImemRead(ReadData, ALUResult, Instr[14:12], RD);

endmodule // datapath

module adder (input  logic [31:0] a, b, //module for addition operation in the alu
	      output logic [31:0] y);
   
   assign y = a + b;
   
endmodule

module extend (input  logic [31:7] instr, //module for sign extension operation, has different types depending on the instruction type.
	       input  logic [2:0]  immsrc,
	       output logic [31:0] immext);
   
   always_comb
     case(immsrc)
       // I−type
       3'b000:  immext = {{20{instr[31]}}, instr[31:20]};
       // S−type (stores)
       3'b001:  immext = {{20{instr[31]}}, instr[31:25], instr[11:7]};
       // B−type (branches)
       3'b010:  immext = {{20{instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};       
       // J−type (jal)
       3'b011:  immext = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
       // U-type
       3'b100:  immext = {instr[31:12], 12'h000}; //gets the top 20 bits, and sets the lower 12 bits to 0 //oldversion {instr[31:12], {12}{1'b0}};
       //default case
       default: immext = 32'bx; // undefined
     endcase // case (immsrc)
   
endmodule // extend

module flopr #(parameter WIDTH = 8)
   (input  logic             clk, reset,
    input logic [WIDTH-1:0]  d,
    output logic [WIDTH-1:0] q);
   
   always_ff @(posedge clk, posedge reset)
     if (reset) q <= 0;
     else  q <= d;
   
endmodule // flopr

module flopenr #(parameter WIDTH = 8)
   (input  logic             clk, reset, en,
    input logic [WIDTH-1:0]  d,
    output logic [WIDTH-1:0] q);
   
   always_ff @(posedge clk, posedge reset)
     if (reset)  q <= 0;
     else if (en) q <= d;
   
endmodule // flopenr

module mux2 #(parameter WIDTH = 8)
   (input  logic [WIDTH-1:0] d0, d1,
    input logic 	     s,
    output logic [WIDTH-1:0] y);
   
  assign y = s ? d1 : d0;
   
endmodule // mux2

module mux3 #(parameter WIDTH = 8)
   (input  logic [WIDTH-1:0] d0, d1, d2,
    input logic [1:0] 	     s,
    output logic [WIDTH-1:0] y);
   
  assign y = s[1] ? d2 : (s[0] ? d1 : d0);
   
endmodule // mux3

module mux4 #(parameter WIDTH = 8)
   (input  logic [WIDTH-1:0] d0, d1, d2, d3, //d3(novalue) = 2'bxx, d2(PCPlus4) = 2'b10, d1(ReadData) = 2'b01, d0(ALUResult) = 2'b00 for the resultMux
    input logic [1:0] s, //2bit source logic
    output logic [WIDTH-1:0] y);
   
  assign y = s[1] ? (s[0] ? d3 : d2) : (s[0] ? d1 : d0); //changed it to mux4
   
endmodule // mux4

module top (input  logic        clk, reset, //the top module where everything starts. all the big stuff is instantiated here. like rv32single, imem, and dmem.
	    output logic [31:0] WriteData, DataAdr,
	    output logic 	MemWrite);
   
   logic [31:0] 		PC, Instr, ReadData;
   logic [2:0] funct3;
   
   // instantiate processor and memories
   riscvsingle rv32single (clk, reset, PC, Instr, MemWrite, DataAdr,
			   WriteData, funct3, ReadData);
   imem imem (PC, Instr); //instruction memory
   dmem dmem (clk, MemWrite, DataAdr, WriteData, funct3, ReadData); //data memory
   
endmodule // top

//memory to store the instructions, 32 bits long
module imem (input  logic [31:0] a,
	     output logic [31:0] rd);
   
   logic [31:0] 		 RAM[511:0]; //RAM[255:0]; //old one RAM[63:0];
   
   assign rd = RAM[a[31:2]]; // word aligned
   
endmodule // imem

module dmem (input  logic clk, //data memory //clk
       input logic we, // byte write enable
	     input  logic [31:0] a, wd, //data address, writedata
       input logic [2:0] funct3, //mask for
	     output logic [31:0] RD); //read data
   
   logic [31:0] 		 RAM[511:0]; //RAM[255:0];

   //logic for writing
   logic [3:0] byteMask;
   logic [3:0] selectionBits;
   logic [31:0] writeword;

   logic [7:0] tempByte; //for reading
   logic [15:0] tempHalfWord; //for reading
   logic [31:0] ReadData;
   
   assign ReadData = RAM[a[31:2]]; //data read, lw, word aligned, alligned to get rid of the last 2 bytes because you don't care about them.

    //read stuff part
    always_comb
    case (funct3)
      3'b000: RD = {{24{tempByte[7]}}, tempByte}; //lb
      3'b100: RD = {{24{0'b0}}, tempByte}; //lbu
      3'b001: RD = {{16{tempHalfWord[15]}}, tempHalfWord}; //lh
      3'b101: RD = {{16{0'b0}}, tempHalfWord}; //lhu
      3'b010: RD = ReadData; //lw
      default: RD = 32'bx; //don't care
    endcase

    always_comb
    case(a[1:0])
      2'b00: begin
             tempByte = ReadData[7:0]; 
             tempHalfWord = ReadData[15:0];
      end
      2'b01: tempByte = ReadData[15:8];
      2'b10: begin
             tempByte = ReadData[23:16]; 
             tempHalfWord = ReadData[31:16];
      end
      2'b11: tempByte = ReadData[31:24];
      default: tempByte = 8'bx;
    endcase



    //write stuff part
    assign selectionBits = {funct3[1:0], a[1:0]};

    //still reads the whole word, but we just select a byte to write to per check
    always_ff @(posedge clk)
      if(we != 0) begin
        if(byteMask[0]) RAM[a[31:2]][7:0] <= writeword[7:0];
        if(byteMask[1]) RAM[a[31:2]][15:8] <= writeword[15:8];
        if(byteMask[2]) RAM[a[31:2]][23:16] <= writeword[23:16]; 
        if(byteMask[3]) RAM[a[31:2]][31:24] <= writeword[31:24];
      end

   //select the correct wd based on the we
   always_comb
     case (selectionBits)
       //4'b0000: //no byte write //0
       4'b0000: begin writeword = {24'b0, wd[7:0]}; //byte 0001 written //1
                byteMask = 4'b0001; end
       4'b0001: begin writeword = {16'b0, wd[7:0], 8'b0}; //byte 0010 being written //2
                byteMask = 4'b0010; end
       4'b0010: begin writeword = {8'b0, wd[7:0], 16'b0}; //byte 0100 being written //4
                byteMask = 4'b0100; end
       4'b0011: begin writeword = {wd[7:0], 24'b0}; //byte 1000 being written //8
                byteMask = 4'b1000; end
       4'b0100: begin writeword = {16'b0, wd[15:0]}; //lower two bytes 0011 being written //3
                byteMask = 4'b0011; end
       4'b0110: begin writeword = {wd[15:0], 16'b0}; //upper two bytes 1100 being written //12
                byteMask = 4'b1100; end
       4'b1000: begin writeword = wd[31:0]; //whole word being written
                byteMask = 4'b1111; end
       default: byteMask = 4'bx; //catches all the other cases that shouldn't happen
     endcase

    /*
     //still reads the whole word, can we just select a byte from memory?
    always_ff @(posedge clk)
      if(we != 0) begin

        RAM[a[31:2]] <= RAM[a[31:2]] & ~byteMask;
        RAM[a[31:2]] <= RAM[a[31:2]] | writeword;
      end

   //select the correct wd based on the we
   always_comb
     case (selectionBits)
       //4'b0000: //no byte write //0
       4'b0000: begin writeword = {{24{1'b0}}, wd[7:0]}; //byte 0001 written //1
                byteMask = 32'h00000011; end
       4'b0001: begin writeword = {{16{1'b0}}, wd[15:8], {8{1'b0}}}; //byte 0010 being written //2
                byteMask = 32'h00001100; end
       4'b0010: begin writeword = {{8{1'b0}}, wd[23:16], {16{1'b0}}}; //byte 0100 being written //4
                byteMask = 32'h00110000; end
       4'b0011: begin writeword = {wd[31:24], {24{1'b0}}}; //byte 1000 being written //8
                byteMask = 32'h11000000; end
       4'b0100: begin writeword = {{16{1'b0}}, wd[15:0]}; //lower two bytes 0011 being written //3
                byteMask = 32'h00001111; end
       4'b0110: begin writeword = {wd[31:16], {16{1'b0}}}; //upper two bytes 1100 being written //12
                byteMask = 32'h11110000; end
       4'b1000: begin writeword = wd[31:0]; //whole word being written
                byteMask = 32'h11111111; end
       default: writeword = wd; //catches all the other cases that shouldn't happen
     endcase
     */
   
endmodule // dmem

module alu (input  logic [31:0] a, b, //for doing operations and comparisons based on control logic and input logic from reg file.
            input  logic [3:0] 	alucontrol,
            output logic [31:0] result,
            output logic 	zero, v, n, cout //zerobit, overflowflag, negativeflag, coutflag
            );

   logic [31:0] 	       condinvb, sum;
   logic 		       isAddSub;       // true when is add or subtract operation

   assign condinvb = alucontrol[0] ? ~b : b; //if alucontrol bit 0 is 1, then condinvb is set to the negation of the b input
   assign {cout, sum} = a + condinvb + alucontrol[0]; //does twos complement addition, if alucontrol[0] is 1 then it adds the 1 bit for the negative twos complement number(subtraction), else it adds 0 so it just adds normally, //carry out bit is high if the carry out of the adder is 1 and the ALU is adding or subtracting
   assign isAddSub = ~alucontrol[2] & ~alucontrol[1] | //if alu control is 00x or x01 then it's an add or subtract signal
                     ~alucontrol[1] & alucontrol[0];   

   always_comb
     case (alucontrol)
       4'b0000:  result = sum;         // add 0
       4'b0001:  result = sum;         // subtract 1
       4'b0010:  result = a & b;       // and 2
       4'b0011:  result = a | b;       // or 3
       4'b0101:  result = sum[31] ^ v; // slt 5 //checks if the result of the twos complement sum is positive or negative, then xors that sign bit with V which is 1 if there was an overflow?
       4'b0100:  result = a ^ b;       // xor 4
       4'b0110:  result = $signed(a) >>> b[4:0];     // sra 6 >>> is supossedly arithmetic shifts while >> is logical
       4'b0111:  result = a << b[4:0];      // sll 7
       4'b1000:  result = a >> b[4:0];      // srl 8
       4'b1001:  result = b;           // lui
       4'b1011:  result = (b[31] == 1 & a[31] != 1) ? 1 : (b[31] == 1 & a[31] == 1) ? (sum[31]) : (b[31] == 0 & a[31] == 1) ? 0 : (sum[31] ^ v); //sltu since 1100 alucontrol[0] = 0 this means it will add
       
       default: result = 32'bx;
     endcase

   //assign compareSuccess = (result == 32'd1);
   assign zero = (result == 32'b0); //assigns zero to 1 if the result is zero, 0 otherwise.
   assign v = ~(alucontrol[0] ^ a[31] ^ b[31]) & (a[31] ^ sum[31]) & isAddSub; //logic to handle overflows //first part results in 1 if there is no overflow, 0 otherwise, and is anded with the overflow result of the addition detection in the 2nd part and is anded with isaddsub to ensure this checking only during addition and subtraction
   assign n = (result[31] == 1); //means that the result is negative

endmodule // alu

module regfile (input  logic clk, //logic that makes the register file.
		input  logic 	    we3, 
		input  logic [4:0]  a1, a2, a3, 
		input  logic [31:0] wd3, 
		output logic [31:0] rd1, rd2);

   logic [31:0] 		    rf[31:0];

   // three ported register file
   // read two ports combinationally (A1/RD1, A2/RD2)
   // write third port on rising edge of clock (A3/WD3/WE3)
   // register 0 hardwired to 0

    //code that implements register file quickly and easily.
   always_ff @(posedge clk)
     if (we3) rf[a3] <= wd3;	

   assign rd1 = (a1 != 0) ? rf[a1] : 0;
   assign rd2 = (a2 != 0) ? rf[a2] : 0;
   
endmodule // regfile

