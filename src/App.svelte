<script lang="ts">
import { PaneGroup, Pane, PaneResizer } from "paneforge";
import DotsSixVertical from "phosphor-svelte/lib/DotsSixVertical";
import DotsSix from "phosphor-svelte/lib/DotsSix";
import renderWaveForm from "wavedrom/lib/render-wave-form.js"
import skin from "wavedrom/skins/default.js";

import Editor from './Editor.svelte';
import { defaultExample, defaultVcd } from "./rtl.js";

let editor = $state();
let surfer = $state();
let property_list = $state([]);
let bound = $state(10);

window.WaveSkin = skin;
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

function status_emoji(status) {
    if (status == null) {
        return "⏳";
    } else if (status == "REFUTED") {
        return "❌";
    } else {
        return "✅";
    }
}

function version_response(data) {
    console.log("version was read: ", data);
    // we know that the service worker is initialized, show the main UI
    editor.getSession().setValue(defaultExample, 1);
    worker.postMessage({ kind: "Properties", text: editor.getValue() });
}

function properties_response(data) {
    // Clear syntax errors
    editor.getSession().setAnnotations([]);
    if (data.errors == null) {
        console.log("properties read: ", data.properties);
        // update properties shown on the UI. use 'identifier' for tracking properties, and
        // 'name' and 'description' for property showing. Also have a status from verification phase
        property_list = data.properties;
        // TIME TO VERIFY
        worker.postMessage({ kind: "Verify", bound: bound });
    } else {
        console.log("syntax errors just dropped: ", data.errors);
        editor.getSession().setAnnotations(data.errors);
    }
}

function verify_response(data) {
    console.log("verification completed: ", data);
    if (data.properties == null) {
        console.log("verification failed!?");
    } else {
        console.log("look at these verified properties: ", data.properties);
        for (const prop of data.properties) {
            let current_prop = property_list.find((element)=>element.identifier==prop.identifier);
            current_prop.status=prop.status;
            current_prop.trace=prop.trace;
        }
    }
}

function run_ebmc() {
    console.log("running ebmc");
    worker.postMessage({ kind: "Properties", text: editor.getValue() });
}

function ebmc_trace_to_wavejson(prop) {
    let trace = prop.trace;
    let wavejson = {
        signal:[],
        head: { text: prop.name, tick:0, every:1 },
        config: { hscale: 2 }
    };

    // Add signals to the waveform
    for (const signal of trace.states[0]) {
       wavejson.signal.push({name: signal.base_name, wave: "", data: []});
    }

    // Plot signal values for each
    for (const timestep of trace.states) {
        for (const signal of timestep) {
            if (signal.base_name == "clk") continue;
            let json_sig = wavejson.signal.find((e)=> e.name == signal.base_name);
            if (signal.lhs_type == "bool") {
                if (json_sig.wave.length == 0) {
                    json_sig.wave += signal.value;
                    continue;
                }
                for (let i = json_sig.wave.length-1; i >= 0; i--) {
                    if (json_sig.wave.at(i) == ".") {continue;}
                    if (json_sig.wave.at(i) == signal.value) {json_sig.wave += ".";}
                    else {json_sig.wave += signal.value;}
                    break;
                }
            } else if (signal.lhs_type == "[0:0]") {
                if (json_sig.wave.length == 0) {
                    json_sig.wave += signal.value.at(-1);
                    continue;
                }
                for (let i = json_sig.wave.length-1; i >= 0; i--) {
                    if (json_sig.wave.at(i) == ".") {continue;}
                    if (json_sig.wave.at(i) == signal.value.at(-1)) {json_sig.wave += ".";}
                    else {json_sig.wave += signal.value.at(-1);}
                    break;
                }
            } else {
                // number type
                if (json_sig.data.at(-1) == signal.value.split(".").at(-1)) json_sig.wave += "."
                else {
                    json_sig.wave += "=";
                    json_sig.data.push(signal.value.split(".").at(-1));
                }
            }
        }
    }

    // Handle clk
    let clk = wavejson.signal.find((e)=> e.name == "clk");
    clk.wave = "P".padEnd(trace.states.length, ".");

    // For safety, add one more cycle to the end of the sim
    for (const signal of trace.states[0]) {
        let json_sig = wavejson.signal.find((e)=> e.name == signal.base_name);
        if (json_sig.name == "clk") json_sig.wave += "l";
        else json_sig.wave += ".";
    }

    // Delete signals that are constant for the whole time
        for (const signal of trace.states[0]) {
            let json_sig = wavejson.signal.find((e)=> e.name == signal.base_name);
            if (json_sig.name[0].toUpperCase() == json_sig.name[0]) {
                wavejson.signal = wavejson.signal.filter(s => s.name != signal.base_name)
            }
        }

    // Add red arrow to show failure (best guess)
    let line_index = trace.states.length - 1;
    wavejson.signal.unshift({node: "".padEnd(line_index, ".")})
    wavejson.signal[0].node += "A";
    wavejson.signal.push({node: "".padEnd(line_index, ".")})
    wavejson.signal[wavejson.signal.length-1].node += "B";
    wavejson.edge = ["A-B"];


    console.log("displaying waveform:", wavejson)
    return wavejson;
}

function open_waveform(prop) {
    console.log("updating current wave for prop: ", prop);
    if (prop.trace != null) {
        let current_wave = ebmc_trace_to_wavejson(prop);
        renderWaveForm(0, current_wave, "WaveDrom_Display_", false);
    } else {
        console.log("no wave for proved")
    }
}

</script>

<PaneGroup direction="vertical" class="w-full h-full">
    <Pane defaultSize={70}>
        <PaneGroup direction="horizontal">
            <Pane defaultSize={70}>
                <div class="relative flex flex-row justify-between content-center p-4 h-20">
                    <h1 class="h1 overflow-hidden">FPV Explorer</h1>
                    <div class="flex flex-row gap-4 content-center">
                        <label class="label" for="bound_box">Bound:</label>
                        <input type="number" id="bound_box" class="input h-12 w-32" bind:value={bound}/>
                    </div>
                    <button class="btn preset-filled-primary-500" onclick={run_ebmc}> Run </button>
                </div>
                <Editor bind:editor={editor}/>
            </Pane>
            <PaneResizer class="bg-background relative flex items-center justify-center">
                <DotsSixVertical color="white" size={20} weight="bold" />
            </PaneResizer>
            <Pane defaultSize={30}>
                <div class="table-wrap">
                    <table class="table caption-bottom">
                        <thead>
                        <tr>
                            <th>Status</th>
                            <th>Name</th>
                            <th>Description</th>
                        </tr>
                        </thead>
                        <tbody class="[&>tr]:hover:preset-tonal-primary">
                        {#each property_list as p}
                            <tr onclick={() => open_waveform(p)}>
                                <td class="p-2">{status_emoji(p.status)} {p.status}</td>
                                <td class="p-2">{p.name.split(".").at(-1)}</td>
                                <td class="p-2">{p.description}</td>
                            </tr>
                        {/each}
                    </tbody>
                    </table>
                </div>
            </Pane>
        </PaneGroup>
    </Pane>
    <PaneResizer class="bg-background relative flex items-center justify-center">
        <DotsSix color="white" size={20} weight="bold" />
    </PaneResizer>
    <Pane defaultSize={30}>
        <div id="WaveDrom_Display_0"></div>
    </Pane>
</PaneGroup>

