// tb.sv

`timescale 1ns/1ps


`include "assertion.sv"

module tb;
  // parameters
  localparam DEPTH      = 16;
  localparam WIDTH      = 16;
  localparam ADDR_WIDTH = $clog2(DEPTH);

  // DUT signals
  logic                   clk_i, rst_i;
  logic                   wr_rd_i, valid_i;
  logic [ADDR_WIDTH-1:0]  addr_i;
  logic [WIDTH-1:0]       wdata_i, rdata_o;
  logic                   ready_o;

  // instantiate DUT
  memory #(.DEPTH(DEPTH), .WIDTH(WIDTH)) uut (
    .clk_i   (clk_i),
    .rst_i   (rst_i),
    .wr_rd_i (wr_rd_i),
    .valid_i (valid_i),
    .addr_i  (addr_i),
    .wdata_i (wdata_i),
    .rdata_o (rdata_o),
    .ready_o (ready_o)
  );

  // instantiate assertions
  memory_asrt #(.DEPTH(DEPTH), .WIDTH(WIDTH)) asrt (
    .clk_i   (clk_i),
    .rst_i   (rst_i),
    .wr_rd_i (wr_rd_i),
    .valid_i (valid_i),
    .addr_i  (addr_i),
    .wdata_i (wdata_i),
    .rdata_o (rdata_o),
    .ready_o (ready_o)
  );

  // clock
  initial clk_i = 0;
  always #5 clk_i = ~clk_i;

  initial begin
    // reset
    rst_i    = 1;
    valid_i  = 0;
    wr_rd_i  = 0;
    addr_i   = 0;
    wdata_i  = 0;
    #20;
    rst_i = 0;

    // --- normal write @addr=3 ---
    @(posedge clk_i);
      valid_i = 1;
      wr_rd_i = 1;
      addr_i  = 3;
      wdata_i = 16'hABCD;
    @(posedge clk_i);
      valid_i = 0;
    @(posedge clk_i);

    // --- normal read @addr=3 ---
    @(posedge clk_i);
      valid_i = 1;
      wr_rd_i = 0;
      addr_i  = 3;
    @(posedge clk_i);
      valid_i = 0;
    @(posedge clk_i);

    // --- p: valid⇒ready violation (as before) ---
    #20;
    $display("\n*** p: Injecting valid⇒ready violation ***\n");
    force uut.ready_o = 1'b0;
    @(posedge clk_i);
      valid_i = 1;
      wr_rd_i = 0;
      addr_i  = 5;
    @(posedge clk_i);
      valid_i = 0;
    release uut.ready_o;
    @(posedge clk_i);

    // --- p1: wr_rd_i unknown during handshake ---
    #20;
    $display("\n*** p1: Injecting wr_rd_i unknown during handshake ***\n");
    force wr_rd_i = 1'bx;
    @(posedge clk_i);
      valid_i = 1;
      // wr_rd_i is now X
      addr_i  = 6;
      wdata_i = 16'h0123;
    @(posedge clk_i);
      valid_i = 0;
    release wr_rd_i;
    @(posedge clk_i);

    // --- p2: addr_i unknown when wr_rd_i known ---
    #20;
    $display("\n*** p2: Injecting addr_i unknown while wr_rd_i known ***\n");
    force addr_i = {ADDR_WIDTH{1'bx}};
    @(posedge clk_i);
      wr_rd_i = 1;   // known
      valid_i = 0;   // valid not needed
    @(posedge clk_i);
    release addr_i;
    @(posedge clk_i);

    // --- p4: wdata_i unknown during write ---
    #20;
    $display("\n*** p4: Injecting wdata_i unknown during write ***\n");
    force wdata_i = {WIDTH{1'bx}};
    @(posedge clk_i);
      wr_rd_i = 1;   // write
      valid_i = 0;
    @(posedge clk_i);
    release wdata_i;
    @(posedge clk_i);

    // --- p5: rdata_o unknown during read ---
    #20;
    $display("\n*** p5: Injecting rdata_o unknown during read ***\n");
    force uut.rdata_o = {WIDTH{1'bx}};
    @(posedge clk_i);
      wr_rd_i = 0;   // read
    @(posedge clk_i);
    release uut.rdata_o;
    @(posedge clk_i);

    #20;
    $finish;
  end
endmodule
