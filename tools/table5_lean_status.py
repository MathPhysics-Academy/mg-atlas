"""Read verified certificate coverage from receipts and source hashes."""
import hashlib, json

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def data_fingerprint(inputs, exports, group):
    ins = sorted([r for r in inputs if r['group'] == group], key=lambda r: r['component'])
    outs = sorted([{k: v for k, v in r.items() if k != 'gap_ms'} for r in exports if r['group'] == group], key=lambda r: r['component'])
    return hashlib.sha256(json.dumps(dict(inputs=ins, exports=outs), sort_keys=True, separators=(',', ':')).encode()).hexdigest()

def verified_pilots(root, out):
    inputs = json.loads((out / 'inputs.json').read_text())
    exports = json.loads((out / 'exports.json').read_text())
    verified = {}
    for path in out.glob('lean-*-audit.json'):
        r = json.loads(path.read_text())
        if not r.get('complete') or 'source_data_path' not in r:
            continue
        if sha(root / r['source_data_path']) != r['source_data_sha256']:
            continue
        if data_fingerprint(inputs, exports, r['group']) != r.get('selected_data_sha256'):
            continue
        receipts = [r['action'], r['bundle']] + r['farey']
        if not all((c['passed'] and c['exit_code'] == 0 and (sha(root / c['source']) == c['source_sha256']) for c in receipts)):
            continue
        verified[r['group']] = dict(r, audit_file=path.with_suffix('.md').name)
    return verified
