<script>
    let {status, name, description} = $props();
</script>

<div class="flex flex-row gap-2">
    <p>{status == null || status == 'REFUTED' ? '❌' : '✅'} {status}</p>
    <p>{name}</p>
    <p>{description}</p>
    <button>🔍</button>
</div>
