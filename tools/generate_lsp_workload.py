#!/usr/bin/env python3
"""OFFLINE reference-shaped fixtures/oracle; never a runtime protocol parser."""
import argparse
import hashlib
import json
from pathlib import Path

from observe_json_state_sharing import ObjectMembers, TOKEN, scalar_unicode

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / 'tools/fixtures/lsp-workload'
URI = 'file:///workspace/anonymous/Buffer.fib'
SOURCE = 'main : IO Unit\r\nmain = putStrLn "α🌍é"\r\n'


def encode(value):
    return json.dumps(value, ensure_ascii=False, separators=(',', ':')).encode('utf-8')


def frame(body):
    return b'Content-Length: ' + str(len(body)).encode() + b'\r\n\r\n' + body


def packet(method, params, **fields):
    return encode({'jsonrpc': '2.0', **fields, 'method': method, 'params': params})


def capabilities():
    # Representative LSP capabilities, not a claimed Neovim version's exact dump.
    dynamic = {'dynamicRegistration': True}
    return {
        'general': {'positionEncodings': ['utf-16'], 'staleRequestSupport': {
            'cancel': True, 'retryOnContentModified': ['textDocument/semanticTokens/full']}},
        'workspace': {'applyEdit': True, 'workspaceEdit': {'documentChanges': True,
            'resourceOperations': ['create', 'rename', 'delete'], 'failureHandling': 'textOnlyTransactional'},
            'workspaceFolders': True, 'configuration': True,
            **{key: dynamic for key in ['didChangeConfiguration', 'didChangeWatchedFiles', 'symbol', 'executeCommand']}},
        'textDocument': {
            'synchronization': {**dynamic, 'willSave': True, 'willSaveWaitUntil': True, 'didSave': True},
            'completion': {**dynamic, 'contextSupport': True, 'completionItem': {
                'snippetSupport': True, 'commitCharactersSupport': True,
                'documentationFormat': ['markdown', 'plaintext'], 'deprecatedSupport': True,
                'preselectSupport': True, 'tagSupport': {'valueSet': [1]},
                'insertReplaceSupport': True, 'resolveSupport': {'properties': ['documentation', 'detail', 'additionalTextEdits']}}},
            'hover': {**dynamic, 'contentFormat': ['markdown', 'plaintext']},
            'signatureHelp': {**dynamic, 'signatureInformation': {'documentationFormat': ['markdown', 'plaintext'],
                'parameterInformation': {'labelOffsetSupport': True}, 'activeParameterSupport': True}},
            **{key: {**dynamic, 'linkSupport': True} for key in ['declaration', 'definition', 'typeDefinition', 'implementation']},
            **{key: dynamic for key in ['references', 'documentHighlight', 'formatting', 'rangeFormatting', 'onTypeFormatting']},
            'documentSymbol': {**dynamic, 'hierarchicalDocumentSymbolSupport': True,
                'symbolKind': {'valueSet': list(range(1, 27))}},
            'codeAction': {**dynamic, 'isPreferredSupport': True, 'disabledSupport': True,
                'dataSupport': True, 'resolveSupport': {'properties': ['edit']},
                'codeActionLiteralSupport': {'codeActionKind': {'valueSet': ['', 'quickfix', 'refactor',
                    'refactor.extract', 'refactor.inline', 'refactor.rewrite', 'source', 'source.organizeImports']}}},
            'rename': {**dynamic, 'prepareSupport': True},
            'publishDiagnostics': {'relatedInformation': True, 'versionSupport': True,
                'tagSupport': {'valueSet': [1, 2]}, 'codeDescriptionSupport': True, 'dataSupport': True},
            'foldingRange': {**dynamic, 'lineFoldingOnly': True},
            'selectionRange': dynamic,
            'semanticTokens': {**dynamic, 'requests': {'range': True, 'full': {'delta': True}},
                'tokenTypes': ['namespace', 'type', 'class', 'enum', 'interface', 'struct', 'typeParameter',
                    'parameter', 'variable', 'property', 'enumMember', 'event', 'function', 'method',
                    'macro', 'keyword', 'modifier', 'comment', 'string', 'number', 'regexp', 'operator', 'decorator'],
                'tokenModifiers': ['declaration', 'definition', 'readonly', 'static', 'deprecated',
                    'abstract', 'async', 'modification', 'documentation', 'defaultLibrary'],
                'formats': ['relative'], 'overlappingTokenSupport': False, 'multilineTokenSupport': False},
        },
        'window': {'workDoneProgress': True, 'showMessage': {'messageActionItem': {'additionalPropertiesSupport': True}}},
    }


def bodies():
    root = 'file:///workspace/anonymous'
    yield 'initialize-reference', packet('initialize', {'rootUri': root, 'capabilities': {
        'workspace': {'workspaceEdit': {'documentChanges': True}},
        'textDocument': {'definition': {'linkSupport': True}}}, 'initializationOptions': {}}, id=1), 'reference-derived'
    yield 'initialized', packet('initialized', {}), 'reference-derived'
    yield 'didOpen-unicode', packet('textDocument/didOpen', {'textDocument': {
        'uri': URI, 'languageId': 'fibril', 'version': 1, 'text': SOURCE}}), 'reference-derived'
    # On line 1: 'main = putStrLn "' is 17 UTF-16 units; α adds one;
    # 🌍 occupies [18,20), unlike a single Python Unicode scalar.
    changes = [{'range': {'start': {'line': 1, 'character': 18}, 'end': {'line': 1, 'character': 20}},
                'rangeLength': 2, 'text': '🧵λ'},
               {'range': {'start': {'line': 1, 'character': 21}, 'end': {'line': 1, 'character': 23}},
                'rangeLength': 2, 'text': 'é'}]
    yield 'didChange-utf16', packet('textDocument/didChange', {'textDocument': {'uri': URI, 'version': 2},
        'contentChanges': changes}), 'reference-derived'
    yield 'shutdown', packet('shutdown', {}, id=2), 'reference-derived'
    yield 'exit', packet('exit', {}), 'reference-derived'
    yield 'shutdown-string-id', packet('shutdown', None, id='shutdown-2'), 'synthetic'
    yield 'initialize-capabilities', packet('initialize', {'processId': None,
        'clientInfo': {'name': 'anonymous-neovim-shaped', 'version': 'fixture-1'}, 'locale': 'en-US',
        'rootPath': '/workspace/anonymous', 'rootUri': root,
        'workspaceFolders': [{'uri': root, 'name': 'anonymous'}],
        'capabilities': capabilities(), 'initializationOptions': {}, 'trace': 'off'}, id=1), 'synthetic'
    module = ''.join(f'-- buffer line {i:03d}: α 🌍 é unsaved editor contents\n' for i in range(100)) + SOURCE
    for method, params in [
        ('didOpen', {'textDocument': {'uri': URI, 'languageId': 'fibril', 'version': 3, 'text': module}}),
        ('didChange', {'textDocument': {'uri': URI, 'version': 4}, 'contentChanges': [{'text': module}]}),
    ]:
        yield method + '-large', packet('textDocument/' + method, params), 'synthetic'
    for size in (4095, 4096, 4097):
        def opened(text):
            return packet('textDocument/didOpen', {'textDocument': {'uri': URI, 'languageId': 'fibril', 'version': 5, 'text': text}})
        prefix = '-- boundary fixture\n'
        body = opened(prefix + 'a' * (size - len(opened(prefix))))
        assert len(body) == size
        yield f'didOpen-boundary-{size}', body, 'synthetic'
    yield 'duplicate-fields', b'{"jsonrpc":"2.0","id":"s-1","id":7,"method":"shutdown","params":{"x":1,"x":2}}', 'synthetic-ambiguity-probe'


def preserve(value):
    if isinstance(value, ObjectMembers):
        return {'object_members': [[key, preserve(item)] for key, item in value]}
    if isinstance(value, list):
        return [preserve(item) for item in value]
    return value


def kind(value):
    if value is None:
        return 'null'
    if isinstance(value, str):
        return 'string'
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return 'number'
    return 'invalid'


def describe(name, body, provenance):
    value = json.loads(body.decode('utf-8'), object_pairs_hook=ObjectMembers)
    scalar_unicode(value)  # Includes overwritten/nested duplicate members.
    position = depth = maximum = count = 0
    for match in TOKEN.finditer(body):
        assert match.start() == position
        position = match.end()
        token = match.group()
        if token.isspace():
            continue
        count += 1  # Every punctuation/string/number/literal, including keys.
        if token in (b'{', b'['):
            depth += 1
            maximum = max(maximum, depth)
        elif token in (b'}', b']'):
            depth -= 1
    assert position == len(body) and depth == 0
    ids = [item for key, item in value if key == 'id']
    return {'name': name, 'provenance': provenance, 'captured_client_traffic': False,
        'body_bytes': len(body), 'wire_bytes': len(frame(body)), 'tokens': count,
        'max_container_nesting': maximum, 'body_sha256': hashlib.sha256(body).hexdigest(),
        'wire_sha256': hashlib.sha256(frame(body)).hexdigest(),
        'expected_jsonrpc_values': [item for key, item in value if key == 'jsonrpc'],
        'expected_method_values': [item for key, item in value if key == 'method'],
        'expected_id_kinds': [kind(item) for item in ids] or ['absent'],
        'expected_id_values': ids,
        'envelope_policy': 'ambiguous-duplicate-id-no-dispatch-expectation' if len(ids) > 1 else 'request' if ids else 'notification',
        'canonical_framer_policy': 'within-4096-body-cap' if len(body) <= 4096 else 'over-4096-body-cap',
        'json_diagnostic_policy': 'within-64-byte-cap' if len(body) <= 64 else 'over-64-byte-cap',
        'expected_fields': preserve(value)}


def artifacts():
    rows = []
    result = {}
    for name, body, provenance in bodies():
        rows.append(describe(name, body, provenance))
        result[name + '.json'] = body  # Exact bytes: no extra newline.
        result[name + '.frame'] = frame(body)
    result['manifest.json'] = (json.dumps({'scope': 'OFFLINE fixtures/oracle, not captured traffic or runtime decoding',
        'token_definition': 'one per punctuation, key/string, number or literal; whitespace excluded',
        'cases': rows}, ensure_ascii=False, indent=2) + '\n').encode()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=DESTINATION)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    expected = artifacts()
    if args.check:
        actual = {path.name: path.read_bytes() for path in args.output.iterdir() if path.is_file()}
        if actual != expected:
            raise SystemExit('workload corpus differs; regenerate explicitly')
    else:
        args.output.mkdir(parents=True, exist_ok=True)
        for name, data in expected.items():
            (args.output / name).write_bytes(data)
    print(f'{(len(expected) - 1) // 2} offline fixture bodies/frames verified' if args.check else 'offline corpus generated')


if __name__ == '__main__':
    main()
