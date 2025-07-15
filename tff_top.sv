module tff_top (
  input  bit       clk,
  input  bit       rst,
  input  bit       t,
  output reg  bit  q
);

  // p: on reset, q must go to 0 on the next clock
  property p;
    @(posedge clk) rst |=> (q == 0);
  endproperty

  // p1: when not t, q must hold its previous value (unless rst)
  property p1;
    @(posedge clk)
      disable iff (rst)
      !t |=> (q == $past(q,1));
  endproperty

  // p2: when t, q must toggle
  property p2;
    @(posedge clk)
      disable iff (rst)
      t |=> (q == ~$past(q,1));
  endproperty

  // Label all assertions; no error-display statements
  HANDSHAKE: assert property (p);
  HOLD:      assert property (p1);
  TOGGLE:    assert property (p2);

endmodule
