#!/usr/bin/env python3
"""Generate a Lean action certificate for each GAP group."""
import hashlib
import argparse
import json
import re
from pathlib import Path
from generate_baseline import AUDIT, PRELUDE, ROOT, component

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        '--extra-input',
        action='append',
        default=[],
        help='additional GAP JSONL batch, relative to repository root',
    )
    parser.add_argument('--input', action='append', help='override the default input JSONL batch')
    parser.add_argument('--output-dir', default='lean/more')
    parser.add_argument('--summary-output', default='results/lean-more-certificate-inputs.json')
    args = parser.parse_args()
    input_path = ROOT / 'results/gap-more-examples.jsonl'
    groups = []
    input_labels = {}
    for batch in ([ROOT / name for name in args.input] if args.input else [input_path]) + [ROOT / name for name in args.extra_input]:
        for line in batch.read_text().splitlines():
            group = json.loads(line)
            assert group['group'] not in input_labels, f"Duplicate group: {group['group']}"
            input_labels[group['group']] = str(batch.relative_to(ROOT))
            groups.append(group)
    output_dir = ROOT / args.output_dir
    output_dir.mkdir(exist_ok=True)
    manifest = []
    summaries = []
    for group in groups:
        match = re.fullmatch('SmallGroup\\((\\d+),(\\d+)\\)', group['group'])
        namespace = f'G{match[1]}_{match[2]}' if match else re.sub('[^A-Za-z0-9]+', '_', group['group']).strip('_')
        indexed_partition = any((len(c['S']) > 384 for c in group['components']))
        tree_lookup = any((len(c['S']) > 1024 for c in group['components']))
        data = dict(
            group,
            namespace=namespace,
            balanced=True,
            indexed_partition=indexed_partition,
            tree_lookup=tree_lookup,
        )
        source = [PRELUDE.replace('ChenBaseline', 'ChenMore').replace('results/gap-actions.jsonl', input_labels[group['group']]).replace('lean/generate_baseline.py', 'lean/generate_more.py').replace('namespace ChenMore', ('set_option maxRecDepth 16384\n'
                           'set_option maxHeartbeats 0\n\nnamespace ChenMore'))]
        if indexed_partition:
            source[0] = source[0].replace('import Mathlib.Data.Fin.Basic', 'import Mathlib.Data.Fin.Basic\nimport Mathlib.Data.List.FinRange\nimport Mathlib.Data.List.Count')
            shared = (ROOT / 'lean/CuspPartition.lean').read_text()
            source.append(shared.split('namespace ChenMore\n', 1)[1].rsplit('end ChenMore', 1)[0])
        if tree_lookup:
            shared = (ROOT / 'lean/LookupTree.lean').read_text()
            source.append(shared.split('namespace ChenMore\n', 1)[1].rsplit('end ChenMore', 1)[0])
        summary = []
        assert sum((len(c['S']) for c in group['components'])) == group['pairs']
        for number, c in enumerate(group['components']):
            text, row = component(data, number, c, group)
            source.append(text)
            summary.append(row)
        source.append(AUDIT.replace('ChenBaseline', 'ChenMore'))
        text = ''.join(source).replace('by decide', 'by decide +kernel')
        text = text.replace('\n    decide\n', '\n    decide +kernel\n')
        text = text.replace('by simpa [paths] using p.isLt', 'by simp [paths]')
        if tree_lookup:
            text = re.sub('(?m)^def ', 'noncomputable def ', text)
            text = text.replace('set_option maxRecDepth 16384', ('-- Skip native code generation; kernel reduction still checks every proof.\n'
                'set_option maxRecDepth 16384'))
        path = output_dir / f'{namespace}.lean'
        path.write_text(text)
        entry = {
            'group': group['group'],
            'file': path.name,
            'components': len(summary),
            'max_degree': max((r['degree'] for r in summary)),
            'obstructions': sum((len(r['obstructed_moduli']) for r in summary)),
            'sha256': hashlib.sha256(text.encode()).hexdigest(),
        }
        manifest.append(entry)
        summaries.extend(summary)
        print((f"Generated {entry['file']}: {entry['components']} components, "
              f"{entry['obstructions']} obstruction witnesses"), flush=True)
    (output_dir / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    (ROOT / args.summary_output).write_text(json.dumps(summaries, indent=2) + '\n')
    print((f'Generated {len(summaries)} components for {len(groups)} groups. '
          f'Sources: {args.output_dir}. Use lean/check-farey.sh with --source-dir {args.output_dir} and a separate --results-dir to verify.'))
if __name__ == '__main__':
    main()
