module riscvpipeline (
    input 	  clk,
    input 	  reset,
    output [31:0] PC,
    input  [31:0] Instr,
    output [31:0] Address,  
    output [31:0] WriteData, 
    output        MemWrite,  
    input  [31:0] ReadData);

   /* The 10 "recognizers" for the 10 codeops */
   function isALUreg; input [31:0] I; isALUreg=(I[6:0]==7'b0110011); endfunction
   function isALUimm; input [31:0] I; isALUimm=(I[6:0]==7'b0010011); endfunction
   function isBranch; input [31:0] I; isBranch=(I[6:0]==7'b1100011); endfunction
   function isJALR;   input [31:0] I; isJALR  =(I[6:0]==7'b1100111); endfunction
   function isJAL;    input [31:0] I; isJAL   =(I[6:0]==7'b1101111); endfunction
   function isAUIPC;  input [31:0] I; isAUIPC =(I[6:0]==7'b0010111); endfunction
   function isLUI;    input [31:0] I; isLUI   =(I[6:0]==7'b0110111); endfunction
   function isLoad;   input [31:0] I; isLoad  =(I[6:0]==7'b0000011); endfunction
   function isStore;  input [31:0] I; isStore =(I[6:0]==7'b0100011); endfunction
   function isSYSTEM; input [31:0] I; isSYSTEM=(I[6:0]==7'b1110011); endfunction

   /* Register indices */
   function [4:0] rs1Id; input [31:0] I; rs1Id = I[19:15];      endfunction
   function [4:0] rs2Id; input [31:0] I; rs2Id = I[24:20];      endfunction
   function [4:0] shamt; input [31:0] I; shamt = I[24:20];      endfunction
   function [4:0] rdId;  input [31:0] I; rdId  = I[11:7];       endfunction
   function [1:0] csrId; input [31:0] I; csrId = {I[27],I[21]}; endfunction

   /* funct3 and funct7 */
   function [2:0] funct3; input [31:0] I; funct3 = I[14:12]; endfunction
   function [6:0] funct7; input [31:0] I; funct7 = I[31:25]; endfunction

   /* EBREAK and CSRRS instruction "recognizers" */
   function isEBREAK; input [31:0] I; isEBREAK = (isSYSTEM(I) && funct3(I) == 3'b000); endfunction

   /* The 5 immediate formats */
   function [31:0] Uimm; input [31:0] I; Uimm={I[31:12],{12{1'b0}}}; endfunction
   function [31:0] Iimm; input [31:0] I; Iimm={{21{I[31]}},I[30:20]}; endfunction
   function [31:0] Simm; input [31:0] I; Simm={{21{I[31]}},I[30:25],I[11:7]}; endfunction
   function [31:0] Bimm; input [31:0] I; Bimm = {{20{I[31]}},I[7],I[30:25],I[11:8],1'b0}; endfunction
   function [31:0] Jimm; input [31:0] I; Jimm = {{12{I[31]}},I[19:12],I[20],I[30:21],1'b0}; endfunction

   /* Read/Write tests */
   function writesRd; input [31:0] I; writesRd = !isStore(I) && !isBranch(I); endfunction
   function readsRs1; input [31:0] I; readsRs1 = !(isJAL(I) || isAUIPC(I) || isLUI(I)); endfunction
   function readsRs2; input [31:0] I; readsRs2 = isALUreg(I) || isBranch(I) || isStore(I); endfunction

/**********************  F: Instruction fetch *********************************/
   localparam NOP = 32'b0000000_00000_00000_000_00000_0110011;
   reg [31:0] F_PC;
   reg [31:0] FD_PC;
   reg [31:0] FD_instr;
   reg        FD_nop;
   assign PC = F_PC;

   /** These two signals come from the Execute stage **/
   wire [31:0] jumpOrBranchAddress;
   wire        jumpOrBranch;

   // --- STALL LOGIC DECLARATION (Used in Fetch and Decode) ---
    // Detecta Load-Use Hazard: Instrução no estágio Execute é Load e o destino dela 
    // é usado como fonte pela instrução no estágio Decode (que é FD_instr aqui).
    wire stall; 
    // Nota: A logica de stall precisa checar a instrução que está SAINDO do decode (DE_instr)
    // contra a que está ENTRANDO (FD_instr). Mas DE_instr é definido no bloco D.
    // Vamos definir a logica de stall mais abaixo e usar aqui.

    always @(posedge clk) begin
       // FLUSH: Se jumpOrBranch for 1, precisamos "matar" a instrução que acabou de ser buscada.
       // STALL: Se stall for 1, não atualizamos o PC e mantemos o pipeline register.

       if (!stall) begin 
           FD_instr <= jumpOrBranch ? NOP : Instr; // Se branch tomado, descarta a inst buscada (Flush)
      FD_PC    <= F_PC;
           
      if (jumpOrBranch)
              F_PC <= jumpOrBranchAddress;
           else
              F_PC <= F_PC + 4;
       end else begin
           // Durante o stall, mantemos os valores de FD (simulando a bolha acima)
           // e não incrementamos o PC.
           FD_instr <= FD_instr;
           FD_PC    <= FD_PC;
           F_PC     <= F_PC; 
       end

      FD_nop <= reset;
      if (reset)
    	   F_PC <= 0;
   end

/************************ D: Instruction decode *******************************/
   reg [31:0] DE_PC;
   reg [31:0] DE_instr;
   reg [31:0] DE_rs1;
   reg [31:0] DE_rs2;

   /* These three signals come from the Writeback stage */
   wire        writeBackEn;
   wire [31:0] writeBackData;
   wire [4:0]  wbRdId;

   reg [31:0] RegisterBank [0:31];
 // --- STALL LOGIC IMPLEMENTATION ---
    // Stall acontece quando a instrução em DE (agora em Execute) é um Load
    // E a instrução em FD (agora em Decode) usa o registrador de destino do Load.
    assign stall = isLoad(DE_instr) && (
        (rs1Id(FD_instr) == rdId(DE_instr) && readsRs1(FD_instr) && rdId(DE_instr) != 0) ||
        (rs2Id(FD_instr) == rdId(DE_instr) && readsRs2(FD_instr) && rdId(DE_instr) != 0)
    );

    // --- REGISTER FILE BYPASS (Write-First) ---
    // Verifica se estamos escrevendo e lendo o mesmo registrador no mesmo ciclo.
    wire [31:0] bypass_rs1 = (writeBackEn && wbRdId != 0 && wbRdId == rs1Id(FD_instr)) ? writeBackData : RegisterBank[rs1Id(FD_instr)];
    wire [31:0] bypass_rs2 = (writeBackEn && wbRdId != 0 && wbRdId == rs2Id(FD_instr)) ? writeBackData : RegisterBank[rs2Id(FD_instr)];

   always @(posedge clk) begin
      DE_PC    <= FD_PC;
       
       // Priority: Reset > Flush (Jump) > Stall
       if (FD_nop || reset) begin
           DE_instr <= NOP;
       end else if (jumpOrBranch) begin
           // FLUSH: Se o branch foi tomado no Execute, a instrução que estava em Decode
           // (indo para Execute agora) deve ser anulada.
           DE_instr <= NOP;
       end else if (stall) begin
           // STALL: Inserimos uma bolha (NOP) para o estágio Execute, 
           // permitindo que o Load no estágio Memory termine.
           DE_instr <= NOP;
       end else begin
           DE_instr <= FD_instr;
       end
       
       // Leitura dos registradores com Bypass
       DE_rs1 <= rs1Id(FD_instr) ? bypass_rs1 : 32'b0;
       DE_rs2 <= rs2Id(FD_instr) ? bypass_rs2 : 32'b0;

      if (writeBackEn)
	      RegisterBank[wbRdId] <= writeBackData;
   end

/************************ E: Execute *****************************************/
   reg [31:0] EM_PC;
   reg [31:0] EM_instr;
   reg [31:0] EM_rs2;
   reg [31:0] EM_Eresult;
   reg [31:0] EM_addr;
   
    // --- FORWARDING LOGIC ---
    // Precisamos saber se as instruções nos estágios M e W escrevem em registradores
    wire [4:0] E_rs1Id = rs1Id(DE_instr);
    wire [4:0] E_rs2Id = rs2Id(DE_instr);
    
    // Sinais vindos dos estágios M e W (via pipe regs ou regs de saida)
    wire [4:0] M_rdId = rdId(EM_instr);
    wire M_writesRd = writesRd(EM_instr);
    wire [4:0] W_rdId = rdId(MW_instr); // MW_instr vem do estágio M->W
    wire W_writesRd = writesRd(MW_instr);

    // Seleção dos dados com Forwarding
    // Prioridade: Memory Stage (mais recente) > Writeback Stage > Valor Original (DE)
    
    // Forwarding para RS1
    wire [31:0] E_aluIn1_fwd = 
        (M_writesRd && M_rdId != 0 && M_rdId == E_rs1Id) ? EM_Eresult :
        (W_writesRd && W_rdId != 0 && W_rdId == E_rs1Id) ? writeBackData :
        DE_rs1;

    // Forwarding para RS2 (Usado tanto para ALU quanto para Store Data)
    wire [31:0] E_aluIn2_fwd = 
        (M_writesRd && M_rdId != 0 && M_rdId == E_rs2Id) ? EM_Eresult :
        (W_writesRd && W_rdId != 0 && W_rdId == E_rs2Id) ? writeBackData :
        DE_rs2;

   wire [31:0] E_aluIn1 = E_aluIn1_fwd;
   // O Mux do imediato deve acontecer APÓS o forwarding do RS2
    wire [31:0] E_aluIn2 = isALUreg(DE_instr) | isBranch(DE_instr) ? E_aluIn2_fwd : Iimm(DE_instr);
    
    wire [4:0]  E_shamt  = isALUreg(DE_instr) ? E_aluIn2_fwd[4:0] : shamt(DE_instr); // Cuidado: shift amount usa rs2
   wire E_minus = DE_instr[30] & isALUreg(DE_instr);
   wire E_arith_shift = DE_instr[30];

   // The adder is used by both arithmetic instructions and JALR.
   wire [31:0] E_aluPlus = E_aluIn1 + E_aluIn2;

   // Use a single 33 bits subtract to do subtraction and all comparisons
   // (trick borrowed from swapforth/J1)
   wire [32:0] E_aluMinus = {1'b1, ~E_aluIn2} + {1'b0,E_aluIn1} + 33'b1;
   wire        E_LT  = (E_aluIn1[31] ^ E_aluIn2[31]) ? E_aluIn1[31] : E_aluMinus[32];
   wire        E_LTU = E_aluMinus[32];
   wire        E_EQ  = (E_aluMinus[31:0] == 0);

   // Flip a 32 bit word. Used by the shifter (a single shifter for
   // left and right shifts, saves silicium !)
   function [31:0] flip32;
      input [31:0] x;
      flip32 = {x[ 0], x[ 1], x[ 2], x[ 3], x[ 4], x[ 5], x[ 6], x[ 7],
		x[ 8], x[ 9], x[10], x[11], x[12], x[13], x[14], x[15],
		x[16], x[17], x[18], x[19], x[20], x[21], x[22], x[23],
		x[24], x[25], x[26], x[27], x[28], x[29], x[30], x[31]};
   endfunction

   wire [31:0] E_shifter_in = funct3(DE_instr) == 3'b001 ? flip32(E_aluIn1) : E_aluIn1;
   // Usar E_aluIn2[4:0] para shift imediato ou reg, mas precisamos garantir que usamos o valor correto
   // Se for immediate shift (SRAI, SRLI), shamt vem da instrução. Se for Reg (SRA, SRL), vem de rs2.
   // O codigo original usava E_aluIn2[4:0], que já passou pelo Mux do Iimm.
   // Porém, para Shifts tipo R, E_aluIn2 contem rs2 forwarded. Para Shifts tipo I, contem Iimm.
   // O shift amount deve ser pego corretamente.
   wire [4:0] shift_amount = isALUreg(DE_instr) ? E_aluIn2_fwd[4:0] : shamt(DE_instr);

   wire [31:0] E_shifter = $signed({E_arith_shift & E_aluIn1[31], E_shifter_in}) >>> E_aluIn2[4:0];
   wire [31:0] E_leftshift = flip32(E_shifter);

   reg [31:0] E_aluOut;
   always @(*) begin
      case(funct3(DE_instr))
         3'b000: E_aluOut = E_minus ? E_aluMinus[31:0] : E_aluPlus;
         3'b001: E_aluOut = E_leftshift;
         3'b010: E_aluOut = {31'b0, E_LT};
         3'b011: E_aluOut = {31'b0, E_LTU};
         3'b100: E_aluOut = E_aluIn1 ^ E_aluIn2;
         3'b101: E_aluOut = E_shifter;
         3'b110: E_aluOut = E_aluIn1 | E_aluIn2;
         3'b111: E_aluOut = E_aluIn1 & E_aluIn2;
      endcase
   end

   /*********** Branch, JAL, JALR ***********************************/
   reg E_takeBranch;
   always @(*) begin
      case (funct3(DE_instr))
         3'b000: E_takeBranch = E_EQ;
         3'b001: E_takeBranch = !E_EQ;
         3'b100: E_takeBranch = E_LT;
         3'b101: E_takeBranch = !E_LT;
         3'b110: E_takeBranch = E_LTU;
         3'b111: E_takeBranch = !E_LTU;
         default: E_takeBranch = 1'b0;
      endcase
   end

   wire E_JumpOrBranch = (
         isJAL(DE_instr)  ||
         isJALR(DE_instr) ||
         (isBranch(DE_instr) && E_takeBranch)
   );

   wire [31:0] E_JumpOrBranchAddr =
	isBranch(DE_instr) ? DE_PC + Bimm(DE_instr) :
	isJAL(DE_instr)    ? DE_PC + Jimm(DE_instr) :
	/* JALR */           {E_aluPlus[31:1],1'b0} ;

   wire [31:0] E_result =
	(isJAL(DE_instr) | isJALR(DE_instr)) ? DE_PC+4                :
	isLUI(DE_instr)                      ? Uimm(DE_instr)         :
	isAUIPC(DE_instr)                    ? DE_PC + Uimm(DE_instr) :
                                          E_aluOut               ;

  always @(posedge clk) begin
       EM_PC    <= DE_PC;
       EM_instr <= DE_instr; // Flush/Stall handled in Decode regarding instr passing
       EM_rs2   <= E_aluIn2_fwd; // Store Data must be the Forwarded Value!
      EM_Eresult <= E_result;
       EM_addr  <= isStore(DE_instr) ? E_aluIn1_fwd + Simm(DE_instr) :
                                       E_aluIn1_fwd + Iimm(DE_instr) ;
   end

/************************ M: Memory *******************************************/
   reg [31:0] MW_PC;
   reg [31:0] MW_instr;
   reg [31:0] MW_Eresult;
   reg [31:0] MW_addr;
   reg [31:0] MW_Mdata;
   reg [31:0] MW_IOresult;
   reg [31:0] MW_CSRresult;
   wire [2:0] M_funct3 = funct3(EM_instr);
   wire M_isB = (M_funct3[1:0] == 2'b00);
   wire M_isH = (M_funct3[1:0] == 2'b01);
   assign halt = !reset & isEBREAK(MW_instr);

   /*************** STORE **************************/
   wire [31:0] M_STORE_data = EM_rs2;
   assign Address  = EM_addr;
   assign MemWrite    = isStore(EM_instr);
   assign WriteData = EM_rs2;

   always @(posedge clk) begin
      MW_PC        <= EM_PC;
      MW_instr     <= EM_instr;
      MW_Eresult   <= EM_Eresult;
      MW_Mdata     <= ReadData;
      MW_addr      <= EM_addr;
   end

/************************ W: WriteBack ****************************************/

   wire [2:0] W_funct3 = funct3(MW_instr);
   wire W_isB = (W_funct3[1:0] == 2'b00);
   wire W_isH = (W_funct3[1:0] == 2'b01);
   wire W_sext = !W_funct3[2];
   wire W_isIO = MW_addr[22];

   /*************** LOAD ****************************/
   assign writeBackData = isLoad(MW_instr) ? MW_Mdata : MW_Eresult;
   assign writeBackEn = writesRd(MW_instr) && rdId(MW_instr) != 0;
   assign wbRdId = rdId(MW_instr);

   assign jumpOrBranchAddress = E_JumpOrBranchAddr;
   assign jumpOrBranch        = E_JumpOrBranch;

/******************************************************************************/

   always @(posedge clk) begin
      if (halt) begin
         $writememh("regs.out", RegisterBank);
         $finish();
      end
   end
endmodule
