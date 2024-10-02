//========================================================================
// Lab 1 - Iterative Div Unit
//========================================================================

`ifndef RISCV_INT_DIV_ITERATIVE_V
`define RISCV_INT_DIV_ITERATIVE_V

`include "imuldiv-DivReqMsg.v"

module imuldiv_IntDivIterative
(

  input         clk,
  input         reset,

  input         divreq_msg_fn,
  input  [31:0] divreq_msg_a,
  input  [31:0] divreq_msg_b,
  input         divreq_val,
  output        divreq_rdy,

  output [63:0] divresp_msg_result,
  output        divresp_val,
  input         divresp_rdy
);

  imuldiv_IntDivIterativeDpath dpath
  (
    .clk                (clk),
    .reset              (reset),
    .divreq_msg_fn      (divreq_msg_fn),
    .divreq_msg_a       (divreq_msg_a),
    .divreq_msg_b       (divreq_msg_b),
    .divreq_val         (divreq_val),
    .divreq_rdy         (divreq_rdy),
    .divresp_msg_result (divresp_msg_result),
    .divresp_val        (divresp_val),
    .divresp_rdy        (divresp_rdy)
  );


endmodule

//------------------------------------------------------------------------
// Datapath
//------------------------------------------------------------------------

module imuldiv_IntDivIterativeDpath
(
  input         clk,
  input         reset,

  input         divreq_msg_fn,      // Function of MulDiv Unit
  input  [31:0] divreq_msg_a,       // Operand A
  input  [31:0] divreq_msg_b,       // Operand B
  input         divreq_val,         // Request val Signal
  output        divreq_rdy,         // Request rdy Signal

  output [63:0] divresp_msg_result, // Result of operation
  output        divresp_val,        // Response val Signal
  input         divresp_rdy         // Response rdy Signal
);

  //----------------------------------------------------------------------
  // Sequential Logic
  //----------------------------------------------------------------------

  reg  [64:0] a_reg;       // Register for storing operand A
  reg  [64:0] b_reg;       // Register for storing operand B
  reg fn_reg;
  reg program_start;
  reg starting=1;
  wire  [4:0]  counter_reg;  // moved to ctrl module
  wire a_mux_sel;
  wire b_mux_sel;
  wire result_mux_sel;
  wire sign_en;
  wire counter_en;
  reg sign_div_reg;
  reg sign_rem_reg;
  imuldiv_IntDivIterativeCtrl dpathctrl
  (
    .clk(clk),         // Clock signal
    .reset(reset),       // Reset signal
    .divreq_val(divreq_val),  // Request valid signal
    .divresp_rdy(divresp_rdy), // Response ready signal
    .a_mux_sel(a_mux_sel),   // Select for A register mux
    .b_mux_sel(b_mux_sel),   // Select for B register mux
    .divreq_rdy(divreq_rdy),
    .divresp_val(divresp_val),
    .result_mux_sel(result_mux_sel), // Select for result register mux
    .sign_en(sign_en)
  );
//program start
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

  wire sign_bit_a = divreq_msg_a[31];
  wire sign_bit_b = divreq_msg_b[31];

  // Unsign operands if necessary

  wire [31:0] unsigned_a = ( divreq_msg_fn == `IMULDIV_DIVREQ_MSG_FUNC_SIGNED && sign_bit_a ) ? (~divreq_msg_a + 1'b1) : divreq_msg_a;
  wire [31:0] unsigned_b = ( divreq_msg_fn == `IMULDIV_DIVREQ_MSG_FUNC_SIGNED && sign_bit_b ) ? (~divreq_msg_b + 1'b1) : divreq_msg_b;

  
  wire [64:0] a_shift_out = a_reg << 1;
  wire [64:0] sub_out = a_shift_out-b_reg;
  wire [64:0] sub_mx_out = (sub_out[64]==1'b0) ? {sub_out[64:1],1'b1} : a_shift_out;
  
  // Computation logic

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      sign_div_reg <= 0;
      sign_rem_reg <= 0;
    end
    else if (sign_en) begin
      sign_div_reg <= sign_bit_a ^ sign_bit_b;
      sign_rem_reg <= sign_bit_a;
    end
  end
  
  // A register logic

  
  always @(posedge clk or posedge reset) begin
    if (reset) begin
      a_reg <= 65'b0;
      b_reg <= 65'b0;
      fn_reg <= 1'b0;
    end
  else begin
    a_reg <= (a_mux_sel) ? sub_mx_out : {33'b0,unsigned_a};

    if (~b_mux_sel) begin
      b_reg <= {1'b0,unsigned_b,32'b0};
      fn_reg <= divreq_msg_fn;
    end
  end
end


  // wire [31:0] unsigned_quotient;

  // wire [31:0] unsigned_remainder
  //   = ( fn_reg == `IMULDIV_DIVREQ_MSG_FUNC_SIGNED )   ? unsigned_a % unsigned_b
  //   : ( fn_reg == `IMULDIV_DIVREQ_MSG_FUNC_UNSIGNED ) ? a_reg % b_reg
  //   :                                                   32'bx;

  // Determine whether or not result is signed. Usually the result is
  // signed if one and only one of the input operands is signed. In other
  // words, the result is signed if the xor of the sign bits of the input
  // operands is true. Remainder opeartions are a bit trickier, and here
  // we simply assume that the result is signed if the dividend for the
  // rem operation is signed.

  wire is_result_signed_div = sign_div_reg;
  wire is_result_signed_rem = sign_rem_reg;

  // Sign the final results if necessary

  wire [31:0] signed_quotient
    = ( fn_reg == `IMULDIV_DIVREQ_MSG_FUNC_SIGNED
     && is_result_signed_div ) ? ~{a_reg[31:0]} + 1'b1
    :                            {a_reg[31:0]};

  wire [31:0] signed_remainder
    = ( fn_reg == `IMULDIV_DIVREQ_MSG_FUNC_SIGNED
     && is_result_signed_rem )   ? ~{a_reg[63:32]} + 1'b1
   :                              {a_reg[63:32]};

  assign divresp_msg_result = { signed_remainder, signed_quotient };


  // Set the val/rdy signals. The request is ready when the response is
  // ready, and the response is valid when there is valid data in the
  // input registers.


endmodule

//------------------------------------------------------------------------
// Control Logic
//------------------------------------------------------------------------

module imuldiv_IntDivIterativeCtrl
(
  input         clk,         // Clock signal
  input         reset,       // Reset signal
  input         divreq_val,  // Request valid signal
  input         divresp_rdy, // Response ready signal
  output reg    divreq_rdy,
  output reg    divresp_val,
  output reg    a_mux_sel,   // Select for A register mux
  output reg    b_mux_sel,   // Select for B register mux
  output reg    result_mux_sel, // Select for result register mux
  output        sign_en
);
  assign sign_en = ((counter_reg==5'd31) && (counter_en==1'b0));
  reg counter_en;
  reg [4:0] counter_reg;
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
      divreq_rdy     <= 1'b1;
      divresp_val    <= 1'b0;
    end
    else if ((counter_en == 1'b0) && (counter_reg == 5'd31)) begin
      // During the first cycle, load initial values
      if(divreq_val) begin
          a_mux_sel      <= 1'b1;
          b_mux_sel      <= 1'b1;
          result_mux_sel <= 1'b1;
        counter_en     <= 1'b1; // Enable counter decrementing
          divreq_rdy     <= 1'b0;
        end
      else begin
          result_mux_sel <= 1'b0;
          divreq_rdy     <= 1'b1;//about to end
          a_mux_sel      <= 1'b0; // Default to loading unsigned A
          b_mux_sel      <= 1'b0; // Default to loading unsigned B
        end
        divresp_val    <= 1'b0;
    end
    else if ( (counter_reg == 5'b0)) begin
      a_mux_sel      <= 1'b0; // Select the shifted A value
      b_mux_sel      <= 1'b0; // Select the shifted B value
      result_mux_sel <= 1'b0; // Select the adder output for result
      counter_en     <= 1'b0; // Disable counter decrementing
      divreq_rdy     <= 1'b1;
      divresp_val<= 1'b1;
    end
  end
endmodule


`endif