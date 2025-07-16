// assertion.sv

module memory_asrt #(
  parameter DEPTH       = 16,
  parameter WIDTH       = 16,
  parameter ADDR_WIDTH  = $clog2(DEPTH)
)(
  input  logic                   clk_i,
  input  logic                   rst_i,
  input  logic                   wr_rd_i,    // 1 = write, 0 = read
  input  logic                   valid_i,
  input  logic [ADDR_WIDTH-1:0]  addr_i,
  input  logic [WIDTH-1:0]       wdata_i,
  input  logic [WIDTH-1:0]       rdata_o,
  input  logic                   ready_o
);

  //— p: whenever valid_i is asserted, ready_o must be high in that same cycle
  property p;
    @(posedge clk_i)
      disable iff (rst_i)
      valid_i == 1 |-> ready_o == 1;
  endproperty
  p_assert: assert property (p)
    else $error("[%0t] ASSERTION p FAILED: valid_i ⇒ ready_o", $time);


  //— p1: during handshake, wr_rd_i must be a known 0 or 1 (not X/Z)
  property p1;
    @(posedge clk_i)
      disable iff (rst_i)
      valid_i && ready_o |-> (wr_rd_i === 1 || wr_rd_i === 0);
  endproperty
  p1_assert: assert property (p1)
    else $error("[%0t] ASSERTION p1 FAILED: wr_rd_i is X/Z during handshake", $time);


  //— p2: addr_i must never be unknown when wr_rd_i is 0 or 1
  property p2;
    @(posedge clk_i)
      disable iff (rst_i)
      (wr_rd_i === 1 || wr_rd_i === 0) |-> !($isunknown(addr_i));
  endproperty
  p2_assert: assert property (p2)
    else $error("[%0t] ASSERTION p2 FAILED: addr_i is unknown", $time);


  //— p4: on write, wdata_i must never be unknown
  property p4;
    @(posedge clk_i)
      disable iff (rst_i)
      (wr_rd_i === 1) |-> !($isunknown(wdata_i));
  endproperty
  p4_assert: assert property (p4)
    else $error("[%0t] ASSERTION p4 FAILED: wdata_i is unknown on write", $time);


  //— p5: on read, rdata_o must never be unknown
  property p5;
    @(posedge clk_i)
      disable iff (rst_i)
      (wr_rd_i === 0) |-> !($isunknown(rdata_o));
  endproperty
  p5_assert: assert property (p5)
    else $error("[%0t] ASSERTION p5 FAILED: rdata_o is unknown on read", $time);

endmodule

