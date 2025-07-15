`timescale 1ns/1ps

module count_top (
  input  logic        clk,
  input  logic        rst,
  input  logic        load,
  input  logic        up,
  input  logic [3:0]  data,
  output logic [3:0]  count
);

  // Sequential counter logic
  always_ff @(posedge clk) begin
    if (rst)
      count <= 4'b0;
    else if (load)
      count <= data;
    else if (up)
      count <= count + 1;
    else
      count <= count - 1;
  end

  //==================================================================
  // Properties
  //==================================================================

  // p1: on a synchronous reset, next count must be 0
  property p1;
    @(posedge clk)
      rst |=> (count == 4'b0);
  endproperty

  // p2: when load is asserted, next count must equal data
  property p2;
    @(posedge clk)
      load |=> (count == data);
  endproperty

  // p3: when up && !load, count increments by 1 (unless rst)
  property p3;
    @(posedge clk)
      disable iff (rst)
      (up && !load) |=> (count == $past(count) + 1);
  endproperty

  // p4: when !up && !load, count decrements by 1 (unless rst)
  property p4;
    @(posedge clk)
      disable iff (rst)
      (!up && !load) |=> (count == $past(count) - 1);
  endproperty

  //==================================================================
  // Labelled Assertions
  //==================================================================
  RESET_ASSERT:     assert property (p1);
  LOAD_ASSERT:      assert property (p2);
  INCREMENT_ASSERT: assert property (p3);
  DECREMENT_ASSERT: assert property (p4);

endmodule
