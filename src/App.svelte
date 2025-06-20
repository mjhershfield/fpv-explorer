<script lang="ts">
import { PaneGroup, Pane, PaneResizer } from "paneforge";
import DotsSixVertical from "phosphor-svelte/lib/DotsSixVertical";
import DotsSix from "phosphor-svelte/lib/DotsSix";

import Editor from './Editor.svelte';
import Surfer from './Surfer.svelte';
import { defaultExample, defaultVcd } from "./rtl.js";

let editor = $state();
let surfer = $state();
let property_list = $state([]);
let bound = $state(10);

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
            property_list.find((element)=>element.identifier==prop.identifier).status=prop.status;
        }
    }
}

function run_ebmc() {
    console.log("running ebmc");
    worker.postMessage({ kind: "Properties", text: editor.getValue() });
}

function open_waveform() {
    const encoder = new TextEncoder();
    surfer.inject_message(JSON.stringify({
              LoadFromData: [
                 Array.from(encoder.encode(defaultVcd)),{keep_variables: false, keep_unavailable: false}
              ]
          }
      ))

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
                            <tr onclick={open_waveform}>
                                <td class="p-2">{status_emoji(p.status)} {p.status}</td>
                                <td class="p-2">{p.name}</td>
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
        <!-- <iframe src="./surfer/index.html" class="h-full w-full" bind:this={surfer}> </iframe>
        -->
        <Surfer bind:surfer={surfer}/>
    </Pane>
</PaneGroup>

