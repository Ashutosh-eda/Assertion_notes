`timescale 1ns/1ps

module fsm_top (
  input  logic       clk,
  input  logic       rst,
  input  logic       d,      // serial data in
  output logic       out     // high for one cycle when “101” is seen
);

  //––– State encoding –––
  typedef enum logic [1:0] {
    S0 = 2'b00,   // waiting for ‘1’
    S1 = 2'b01,   // saw ‘1’
    S2 = 2'b10    // saw “10”
  } state_t;

  state_t    state, next_state;

  //––– State register + output logic –––
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      state <= S0;
      out   <= 1'b0;
    end else begin
      state <= next_state;
      // output is only asserted in S2 when the new bit is ‘1’
      case (state)
        S0, S1: out <= 1'b0;
        S2:     out <= (d == 1'b1);
        default: out <= 1'b0;
      endcase
    end
  end

  //––– Next‐state combinational logic –––
  always_comb begin
    case (state)
      S0: next_state = d ? S1 : S0;
      S1: next_state = d ? S1 : S2;
      S2: next_state = d ? S1 : S0;
      default: next_state = S0;
    endcase
  end

  //==================================================================
  // SVA properties for each state
  //==================================================================

  // 1) On reset, we must end up in S0 with out==0
  property p_reset;
    @(posedge clk) rst |=> (state == S0 && out == 1'b0);
  endproperty
  RESET_ASSERT: assert property (p_reset);

  // 2) When in S0, next state & out depend on d
  property p_s0;
    @(posedge clk)
      disable iff (rst)
      (state == S0)
        |=> ( ($past(d) ? state == S1 : state == S0)
             && out == 1'b0 );
  endproperty
  S0_TRANSITION: assert property (p_s0);

  // 3) When in S1, next state & out depend on d
  property p_s1;
    @(posedge clk)
      disable iff (rst)
      (state == S1)
        |=> ( ($past(d) ? state == S1 : state == S2)
             && out == 1'b0 );
  endproperty
  S1_TRANSITION: assert property (p_s1);

  // 4) When in S2, seeing a ‘1’ => detect “101” (out=1), else back to S0
  property p_s2;
    @(posedge clk)
      disable iff (rst)
      (state == S2)
        |=> ( $past(d)
               ? (state == S1 && out == 1'b1)
               : (state == S0 && out == 1'b0) );
  endproperty
  S2_TRANSITION: assert property (p_s2);

endmodule
