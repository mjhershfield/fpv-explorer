"use strict";
var modulePrint = function (text) { };
var modulePrintErr = function (text) { };
var Module = {
    print: function (text) { modulePrint(text); },
    printErr: function (text) { modulePrintErr(text); },
    canvas: null,
    noInitialRun: true
};
importScripts("ebmc.js");
function ebmcVersion() {
    let callMain = Module['callMain'];
    var stdout = "";
    modulePrint = function (text) { stdout += text; };
    callMain(["--version"]);
    return stdout;
}
class EbmcProperty {
    constructor() {
        this.name = "";
        this.description = "";
        this.identifier = "";
    }
}
class EbmcError {
    constructor() {
        this.row = 0;
        this.column = 0;
        this.text = "";
        this.type = ""; // error, warning, information
    }
}
function parseSyntaxErrors(stderr) {
    let errors = [];
    var rx = /.*line (\d+): (.*)/g;
    var lines = stderr.split('\n');
    for (let line of lines) {
        var data = rx.exec(line);
        if (data != null) {
            errors.push({
                row: parseInt(data[1]) - 1, // starts at 0
                column: 0,
                text: data[2],
                type: "error" // also warning and information
            });
        }
    }
    return errors;
}
var FS;
function ebmcProperties(file_data) {
    FS.writeFile('module.sv', file_data);
    var stdout = "";
    var stderr = "";
    modulePrint = function (text) { stdout += text + '\n'; };
    modulePrintErr = function (text) { stderr += text + '\n'; };
    let callMain = Module['callMain'];
    let exit_code = callMain(["module.sv", "--json-properties", "properties.json"]);
    if (exit_code != 0) {
        console.log("--json-properties gave exit code", exit_code);
        let errors = parseSyntaxErrors(stderr);
        return { errors: errors, stdout: stdout, stderr: stderr };
    }
    let properties_text = FS.readFile('properties.json', { encoding: 'utf8' });
    let properties = JSON.parse(properties_text);
    return { properties: properties, stdout: stdout, stderr: stderr };
}
function ebmcVerify(bound) {
    var stdout = "";
    var stderr = "";
    modulePrint = function (text) { stdout += text + '\n'; };
    modulePrintErr = function (text) { stderr += text + '\n'; };
    let callMain = Module['callMain'];
    let exit_code = callMain(["module.sv", "--json-result", "result.json", "--bound", bound.toString(), "--reset", "rst==1"]);
    let result_text = FS.readFile('result.json', { encoding: 'utf8' });
    let results = JSON.parse(result_text);
    return { properties: results.properties, stdout: stdout, stderr: stderr };
}
