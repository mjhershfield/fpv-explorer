"use strict";
var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {
    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
};
var ace;
var editor = ace.edit("editor");
//editor.setTheme("ace/theme/monokai");
editor.session.setMode("ace/mode/verilog");
const printToOutput = (function () {
    var element = document.getElementById('output');
    return function (text) {
        element.innerHTML += text.replace(new RegExp('\n', 'g'), '<br>') + '<br>';
    };
})();
const printToOutputRed = (function () {
    var element = document.getElementById('output');
    return function (text) {
        var x = '<font color="#ff0000">' + text.replace(new RegExp('\n', 'g'), '<br>') + '<br>'
            + '</font>\n';
        element.innerHTML += x;
    };
})();
function refresh() {
    console.log("got refresh");
    worker.postMessage({ kind: "Properties", text: editor.getValue() });
}
function setupPropertyTable() {
    const table = document.createElement('table');
    table.style.width = '100%';
    table.style.borderSpacing = '0';
    table.style.padding = '10px';
    table.style.borderCollapse = 'collapse';
    table.style.border = '1px solid black';
    document.getElementById('properties').appendChild(table);
    return table;
}
const property_table = setupPropertyTable();
// property IDs whose witnesses are shown
var visible = new Set();
function waveformHTML(states) {
    // find the signal names, and sort them
    var signals = new Set();
    for (let state of states)
        for (let assignment of state)
            if (assignment.value != "")
                signals.add(assignment.display_name);
    let signals_sorted = [];
    for (let display_name of signals)
        signals_sorted.push(display_name);
    signals_sorted.sort();
    // build the table
    var table = "<table style='border-collapse: collapse;'>\n";
    table += "<tr><td style='border-width: 0px 1px 1px 0px; border-style: solid;'></td>";
    for (let index = 0; index < states.length; index++) {
        table += "<td align='center'";
        table += " style='width: 2em; border-width: 0px 0px 1px 0px; border-style: solid;";
        if (index % 2)
            table += " background: #e0e0e0;'";
        table += "'>" + index + "</td>";
    }
    table += "</tr>\n";
    for (let display_name of signals_sorted) {
        table += "<tr><td style='border-width: 0px 1px 0px 0px; border-style: solid;'>";
        table += display_name;
        table += "</td>";
        for (let index = 0; index < states.length; index++) {
            let value = "";
            for (let assignment of states[index])
                if (assignment.display_name == display_name)
                    value = assignment.value;
            table += "<td align='center'";
            table += " style='";
            if (index % 2)
                table += " background: #e0e0e0;'";
            table += "'>" + value + "</td>";
        }
        table += "</tr>\n";
    }
    table += "</table>";
    return table;
}
var FS;
function updatePropertyTable(properties) {
    while (property_table.rows.length != 0)
        property_table.deleteRow(-1); // deletes last row
    for (let property of properties) {
        // property row
        let p_row = property_table.insertRow();
        let td0 = p_row.insertCell();
        td0.innerHTML = "&#8987;"; // hourglass
        td0.style.fontSize = '12px';
        td0.style.padding = '3px';
        td0.style.borderCollapse = 'collapse';
        td0.style.border = '1px solid black';
        td0.style.whiteSpace = 'nowrap';
        td0.style.width = '100px';
        let td1 = p_row.insertCell();
        td1.style.fontFamily = 'monospace';
        td1.style.fontSize = '12px';
        td1.appendChild(document.createTextNode(property.name));
        td1.style.padding = '3px';
        td1.style.borderCollapse = 'collapse';
        td1.style.border = '1px solid black';
        td1.style.whiteSpace = 'nowrap';
        td1.style.width = '100px';
        let td2 = p_row.insertCell();
        td2.style.fontFamily = 'monospace';
        td2.style.fontSize = '12px';
        td2.appendChild(document.createTextNode(property.description));
        td2.style.border = '0';
        td2.style.padding = '3px';
        td2.style.borderCollapse = 'collapse';
        td2.style.border = '1px solid black';
        // witness row, initially hidden
        let w_row = property_table.insertRow();
        let w_cell = w_row.insertCell();
        w_cell.innerHTML = "witness";
        w_cell.colSpan = 3;
        if (!visible.has(property.name))
            w_cell.style.display = 'none';
    }
}
function toggleTrace(index) {
    let p_row = property_table.rows[index * 2];
    let w_row = property_table.rows[index * 2 + 1];
    let w_cell = w_row.cells[0];
    let property_name = p_row.cells[1].innerText;
    if (w_cell.style.display == '') {
        w_cell.style.display = 'none'; // make invisible
        visible.delete(property_name);
    }
    else {
        w_cell.style.display = ''; // make visible
        visible.add(property_name);
    }
}
function version_response(m) {
    return __awaiter(this, void 0, void 0, function* () {
        const version = m.text;
        let buttons = document.getElementById('buttons');
        var html = '<span id="refresh" onclick="refresh()">&#x21bb; Run';
        html += ' EBMC ' + version;
        html += '</span><span id="spinning"></span>';
        buttons.innerHTML = html;
        // initial source code
        selectExample("counter1");
    });
}
// To store the properties, for the benefit of verify_response
var stored_properties = [];
function properties_response(m) {
    return __awaiter(this, void 0, void 0, function* () {
        if (m.properties)
            console.log("got", m.properties.length, "properties");
        if (m.errors)
            console.log("got", m.errors.length, "errors");
        // clear output
        let output_element = document.getElementById('output');
        output_element.innerHTML = "";
        printToOutput(m.stdout);
        printToOutputRed(m.stderr);
        // clear any earlier syntax errors
        editor.getSession().setAnnotations([]);
        if (m.errors == null) {
            // store, for the benefit of verify_response
            stored_properties = m.properties;
            updatePropertyTable(stored_properties);
            // Turn on the spinning
            {
                let spinning = document.getElementById('spinning');
                var html = '&nbsp;<img src="working.gif" width="15px" style="vertical-align: baseline;">';
                spinning.innerHTML = html;
            }
            // now ask the worker to verify
            worker.postMessage({ kind: "Verify" });
        }
        else {
            // We've got syntax errors
            editor.getSession().setAnnotations(m.errors);
        }
    });
}
function verify_response(m) {
    return __awaiter(this, void 0, void 0, function* () {
        // Turn the spinning off again
        {
            let spinning = document.getElementById('spinning');
            var html = '';
            spinning.innerHTML = html;
        }
        let properties = m.properties;
        for (let index in properties) {
            let index_number = index;
            let status = properties[index_number].status;
            let p_row = property_table.rows[index_number * 2];
            let w_row = property_table.rows[index_number * 2 + 1];
            p_row.cells[0].innerText = status;
            let trace = properties[index_number].trace;
            let w_cell = w_row.cells[0];
            if (trace != null) {
                let no_states = trace.states.length;
                p_row.cells[0].innerHTML +=
                    " <button onclick='toggleTrace(" + index_number + ")'>" +
                        "trace</button>";
                w_cell.innerHTML = waveformHTML(trace.states);
            }
            else {
                w_cell.style.display = 'none';
            }
        }
    });
}
const worker = new Worker('ebmc-worker.js');
worker.onerror = e => { console.log("error from worker"); };
worker.onmessage = function (e) {
    console.log("message from worker", e.data);
    switch (e.data.kind) {
        case "Ready":
            // ask for the EMBC version
            worker.postMessage({ kind: "Version" });
            break;
        case "Version":
            version_response(e.data);
            break;
        case "Properties":
            properties_response(e.data);
            break;
        case "Verify":
            verify_response(e.data);
            break;
        default:
            console.log("unexpected message from worker: ", e.data.kind);
    }
};
document.addEventListener('DOMContentLoaded', function () {
    // nothing
}, false);
// read text from URL
function getText(url) {
    return __awaiter(this, void 0, void 0, function* () {
        const response = yield fetch(url);
        if (!response.ok)
            return "error fetching " + url;
        else
            return response.text();
    });
}
function selectExample(value) {
    return __awaiter(this, void 0, void 0, function* () {
        let text = "";
        let getExample = function (value) {
            return __awaiter(this, void 0, void 0, function* () {
                if (value == "blank") {
                    return new Promise((resolve, reject) => { resolve('\n'); });
                }
                else if (value == "counter1") {
                    return new Promise((resolve, reject) => {
                        resolve('module main(input clk);\n' +
                            '  reg [31:0] data = 1;\n' +
                            '  always_ff @(posedge clk) data++;\n' +
                            '  p0: assert property (@(posedge clk) data != 5);\n' +
                            'endmodule');
                    });
                }
                else if (value == "gray") {
                    return new Promise((resolve, reject) => {
                        resolve('module gray_counter#(N = 4) (input clk, output [N-1:0] out);\n' +
                            '\n' +
                            '  reg [N-1:0] state = 0;\n' +
                            '  assign out = {state[N-1], state[N-1:1] ^ state[N-2:0]};\n' +
                            '\n' +
                            '  always_ff @(posedge clk) state++;\n' +
                            '\n' +
                            '  // two successive values differ in one bit exactly\n' +
                            '  p0: assert property (@(posedge clk)\n' +
                            '    ##1 $countones($past(out) ^ out) == 1);\n' +
                            '\n' +
                            'endmodule');
                    });
                }
                else if (value == "riscv-alu") {
                    return getText("https://www.cprover.org/ebmc/web/riscv-alu.sv");
                }
                else
                    return new Promise((resolve, reject) => { reject("unknown value"); });
            });
        };
        getExample(value).then((text) => {
            editor.getSession().setValue(text, 1);
            worker.postMessage({ kind: "Properties", text: editor.getValue() });
        });
    });
}
function selectExampleChanged() {
    let select_element = document.getElementById("select_example");
    let value = select_element.value;
    selectExample(value);
}
