export const defaultExample =
`module main(input clk);
  reg [31:0] data = 1;
  always_ff @(posedge clk) data++;
  p0: assert property (@(posedge clk) data != 5);
endmodule
`;

export const defaultVcd =
`$date
Thu Jun 19 11:38:18 2025
$end
$timescale
1ns
$end
$scope module fsm $end
$var wire 2 fsm.STATE_1 STATE_1 [1:0] $end
$var wire 2 fsm.STATE_2 STATE_2 [1:0] $end
$var wire 2 fsm.STATE_3 STATE_3 [1:0] $end
$var wire 1 fsm.clk clk [0:0] $end
$var wire 1 fsm.rst rst [0:0] $end
$var reg 2 fsm.state_r state_r [1:0] $end
$upscope $end
$enddefinitions $end
#0
b0 fsm.rst
b00 fsm.STATE_1
b01 fsm.STATE_2
b10 fsm.STATE_3
b01 fsm.state_r
#1
b10 fsm.state_r
#2
`
