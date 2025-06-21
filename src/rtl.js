export const defaultExample =
`module fsm (
    input logic clk,
    input logic rst,
    input logic en
);

    typedef enum logic[1:0] {
        STATE_1,
        STATE_2,
        STATE_3
    } state_t;

    state_t state_r;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state_r <= STATE_1;
        end else begin
            if (en) begin
                case (state_r)
                    STATE_1: state_r <= STATE_2;
                    STATE_2: state_r <= STATE_3;
                    STATE_3: state_r <= STATE_1;
                endcase
            end
        end
    end

    a0: assert property (@(posedge clk) disable iff (rst) state_r != STATE_3);
    c0: cover property (@(posedge clk) rst == 0 ##1 $stable(state_r));
endmodule`;

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
