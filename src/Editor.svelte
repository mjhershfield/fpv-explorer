<script>
    import ace from "ace-builds/src-noconflict/ace.js";
    import "ace-builds/src-noconflict/mode-verilog.js";
    import "ace-builds/src-noconflict/theme-gruvbox.js"

	let { editor = $bindable()} = $props();

    const init_editor = (node) => {
        // the node has been mounted in the DOM

        $effect(() => {
            // setup goes here
            editor = ace.edit("editor");
            editor.setOptions({
                highlightActiveLine: false,
                theme: "ace/theme/gruvbox",
                mode: "ace/mode/verilog"
            });

            return () => {
                // teardown goes here
            };
        });
    };
</script>

<div id="editor" use:init_editor class="m-0 w-full h-full"></div>

<style type="text/css" media="screen">

</style>
