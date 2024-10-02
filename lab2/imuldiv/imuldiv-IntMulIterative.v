//========================================================================
// Lab 1 - Iterative Mul Unit
//========================================================================

`ifndef RISCV_INT_MUL_ITERATIVE_V
`define RISCV_INT_MUL_ITERATIVE_V

module imuldiv_IntMulIterative
(
  input                clk,
  input                reset,

  input  [31:0] mulreq_msg_a,
  input  [31:0] mulreq_msg_b,
  input         mulreq_val,
  output        mulreq_rdy,

  output [63:0] mulresp_msg_result,
  output        mulresp_val,
  input         mulresp_rdy
);

  imuldiv_IntMulIterativeDpath dpath
  (
    .clk                (clk),
    .reset              (reset),
    .mulreq_msg_a       (mulreq_msg_a),
    .mulreq_msg_b       (mulreq_msg_b),
    .mulreq_val         (mulreq_val),
    .mulreq_rdy         (mulreq_rdy),
    .mulresp_msg_result (mulresp_msg_result),
    .mulresp_val        (mulresp_val),
    .mulresp_rdy        (mulresp_rdy)
  );

endmodule

//------------------------------------------------------------------------
// Datapath
//------------------------------------------------------------------------

module imuldiv_IntMulIterativeDpath
(
  input         clk,
  input         reset,

  input  [31:0] mulreq_msg_a,       // Operand A
  input  [31:0] mulreq_msg_b,       // Operand B
  input         mulreq_val,         // Request val Signal
  output        mulreq_rdy,         // Request rdy Signal
  output [63:0] mulresp_msg_result, // Result of operation
  output        mulresp_val,        // Response val Signal
  input         mulresp_rdy         // Response rdy Signal
);

  //----------------------------------------------------------------------
  // Sequential Logic
  //----------------------------------------------------------------------

  reg  [63:0] a_reg;       // Register for storing operand A
  reg  [63:0] b_reg;       // Register for storing operand B
  reg program_start;
  reg starting=1;
  wire  [4:0]  counter_reg;  // moved to ctrl module
  wire a_mux_sel;
  wire b_mux_sel;
  wire result_mux_sel;
  wire sign_en;
  wire counter_en;
  wire mulreq_rdy;
  wire mulresp_val;
  reg [63:0] result_reg;
  reg sign_reg;

  imuldiv_IntMulIterativeCtrl dpathctrl
  (
    .clk(clk),         // Clock signal
    .reset(reset),       // Reset signal
    .mulreq_val(mulreq_val),  // Request valid signal
    .mulresp_rdy(mulresp_rdy), // Response ready signal
    .program_start(program_start),
    .a_mux_sel(a_mux_sel),   // Select for A register mux
    .b_mux_sel(b_mux_sel),   // Select for B register mux
    .mulreq_rdy(mulreq_rdy),
    .mulresp_val(mulresp_val),
    .result_mux_sel(result_mux_sel), // Select for result register mux
    .sign_en(sign_en),
    .counter_en(counter_en),
    .counter_reg(counter_reg)
  );

  always @(posedge clk) begin
    if (reset) 
      program_start <= 0;
    else
      program_start <= 1;
  end
  always @(negedge clk) begin
    if (reset) 
      starting <= 1;
    else
      starting <= 0;
  end





  //----------------------------------------------------------------------
  // Combinational Logic
  //----------------------------------------------------------------------

  // Extract sign bits

  wire sign_bit_a = mulreq_msg_a[31];
  wire sign_bit_b = mulreq_msg_b[31];

  // Unsign operands if necessary

  wire [31:0] unsigned_a = ( sign_bit_a ) ? (~mulreq_msg_a + 1'b1) : mulreq_msg_a;
  wire [31:0] unsigned_b = ( sign_bit_b ) ? (~mulreq_msg_b + 1'b1) : mulreq_msg_b;

  wire [63:0] a_shift_out = a_reg << 1;
  wire [63:0] b_shift_out = b_reg >> 1;
  wire [63:0] add_mux_out = b_reg[0]==1'b1 ? a_reg+result_reg : result_reg;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      sign_reg <= 0;
      a_reg <= 64'b0;
      b_reg <= 64'b0;
    end
    else begin
      if (sign_en)
        sign_reg <= sign_bit_a ^ sign_bit_b;

      a_reg <= (a_mux_sel) ? a_shift_out : {32'b0,unsigned_a};
      b_reg <= (b_mux_sel) ? b_shift_out : {32'b0,unsigned_b};
    end
  end

  // Counter logic

  
  // Shift logic for A and B registers
  assign a_shift_out = a_reg << 1;
  assign b_shift_out = b_reg >> 1;
  
  // Adder logic
  assign add_mux_out = (b_reg[0]==1'b1) ? a_reg + result_reg : result_reg;
  
  // Result register logic
  always @(posedge clk or posedge reset) begin
    if (reset)
      result_reg <= 64'b0;
    else //if (result_en)
      result_reg <= (result_mux_sel) ? add_mux_out : 64'b0;
  end
  


  // Determine whether or not result is signed. Usually the result is
  // signed if one and only one of the input operands is signed. In other
  // words, the result is signed if the xor of the sign bits of the input
  // operands is true. Remainder opeartions are a bit trickier, and here
  // we simply assume that the result is signed if the dividend for the
  // rem operation is signed.


  assign mulresp_msg_result  = ( sign_reg ) ? (~result_reg + 1'b1) : result_reg;

  // Set the val/rdy signals. The request is ready when the response is
  // ready, and the response is valid when there is valid data in the
  // input registers.

  // assign mulreq_rdy  = ((counter_reg==5'd31) && (counter_en==1'b0));
  // assign mulresp_val = (counter_reg==5'b0);// && (~((program_start)&&(~mulreq_val)&&(counter_en == 1'b0))));
endmodule

//------------------------------------------------------------------------
// Control Logic
//------------------------------------------------------------------------

module imuldiv_IntMulIterativeCtrl
(
  input         clk,         // Clock signal
  input         reset,       // Reset signal
  input         mulreq_val,  // Request valid signal
  input         mulresp_rdy, // Response ready signal
  input         program_start,
  output reg    mulreq_rdy,
  output reg    mulresp_val,
  output reg    a_mux_sel,   // Select for A register mux
  output reg    b_mux_sel,   // Select for B register mux
  output reg    result_mux_sel, // Select for result register mux
  output        sign_en,
  //output reg    val_reg,     // Register for storing valid bit
  output reg counter_en, // Enable for the counter
  output reg [4:0] counter_reg
);

  assign sign_en = ((counter_reg==5'd31) && (counter_en==1'b0));
  

  always @(posedge clk or posedge reset) begin
    if (counter_en) begin
      // Decrement the counter during the iterative process
      counter_reg <= counter_reg - 1;
    end
    if (reset) begin
      // Reset counter to default value
      counter_reg <= 5'd31;
      a_mux_sel      <= 1'b0; // Default to loading unsigned A
      b_mux_sel      <= 1'b0; // Default to loading unsigned B
      result_mux_sel <= 1'b0; // Default to initializing result
      counter_en     <= 1'b0;
      mulreq_rdy     <= 1'b1;
      mulresp_val    <= 1'b0;
    end
    else if ((counter_en == 1'b0) && (counter_reg == 5'd31)) begin
      // During the first cycle, load initial values
      // a_mux_sel      <= 1'b1;
      // b_mux_sel      <= 1'b1;
      // result_mux_sel <= 1'b1;
      if(mulreq_val) begin
        a_mux_sel      <= 1'b1;
        b_mux_sel      <= 1'b1;
        result_mux_sel <= 1'b1;
        counter_en     <= 1'b1; // Enable counter decrementing
        mulreq_rdy     <= 1'b0;
      end
      else begin
        a_mux_sel      <= 1'b0;
        b_mux_sel      <= 1'b0;
        result_mux_sel <= 1'b0;
        mulreq_rdy     <= 1'b1;//about to end
        a_mux_sel      <= 1'b0; // Default to loading unsigned A
        b_mux_sel      <= 1'b0; // Default to loading unsigned B
      end
        
      mulresp_val    <= 1'b0;
    end
    else if ( (counter_reg == 5'b0)) begin
      a_mux_sel      <= 1'b0; // Select the shifted A value
      b_mux_sel      <= 1'b0; // Select the shifted B value
      result_mux_sel <= 1'b0; // Select the adder output for result
      counter_en     <= 1'b0; // Disable counter decrementing
      mulreq_rdy     <= 1'b1;
      mulresp_val<= 1'b1;
    end
  end

endmodule
`endif