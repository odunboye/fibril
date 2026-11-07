#!/usr/bin/env python3
"""Private two-alias candidate checks; never normalizes arbitrary parser code."""
import copy
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CANDIDATE = ROOT / 'tools/fixtures/lsp-source-sharing'
BASELINES = {'Frame': ROOT / 'examples/modules/binary-frame/Protocol/Frame.fib',
             'JSON': ROOT / 'tools/fixtures/json-iteration/Protocol/JSON.fib'}
ALIASES = {'Frame': ('sharedEqualString', 'equalString', '(1 left : String) -> (1 right : String) -> Bool'),
           'JSON': ('sharedOrBool', 'orBool', '(1 left : Bool) -> (1 right : Bool) -> Bool')}
# Strings/comments are indivisible: replacement is only on complete name tokens.
TOKEN = re.compile(r'--[^\n]*|"(?:\\.|[^"\\])*"|[A-Za-z_][A-Za-z_0-9]*|.', re.S)


def source_preservation(name, candidate=None):
    baseline = BASELINES[name].read_text()
    text = candidate if candidate is not None else (CANDIDATE / f'Protocol/{name}.fib').read_text()
    alias, helper, ty = ALIASES[name]
    line = f'  let ({alias} : {ty}) = {helper} in\n'
    assert text.count(line) == 1
    assert alias not in TOKEN.findall(baseline), 'alias must be fresh everywhere in baseline'
    # The unique introduced binder encloses all rewritten references. Exact inverse
    # equality rejects any other binder, annotation, policy, literal or body edit.
    prefix, body = text.split(line)
    assert alias not in TOKEN.findall(prefix)
    restored = prefix + ''.join(helper if t == alias else t for t in TOKEN.findall(body))
    assert restored == baseline, f'{name}: non-alias source change'
    return True


def bare(node):
    return [node['tag'], node.get('detail', []), [bare(c) for c in node['children']]]


def binder_child(tag, index):
    return tag in ('Lambda', 'Pi', 'Sigma') and index == 1


def closed(tree, depth=0):
    if tree['tag'] == 'Variable':
        return tree['detail'][0] < depth
    return all(closed(c, depth + binder_child(tree['tag'], i)) for i, c in enumerate(tree['children']))


def expand_closed(body, rhs, depth=0):
    """Remove exactly one binder. RHS closed: weakening it under binders is inert."""
    result = copy.deepcopy(body)
    if body['tag'] == 'Variable':
        index = body['detail'][0]
        if index == depth:
            return copy.deepcopy(rhs)
        if index > depth:
            result['detail'] = [index - 1]
    result['children'] = [expand_closed(c, rhs, depth + binder_child(body['tag'], i))
                          for i, c in enumerate(body['children'])]
    return result


def expand_introduced(tree, rhs):
    """Only an unrestricted let with the exact verified imported closed RHS."""
    assert closed(rhs)
    count = 0
    def visit(node):
        nonlocal count
        if node['tag'] == 'Apply':
            function, argument = node['children']
            if function['tag'] == 'Lambda' and bare(argument) == bare(rhs):
                assert function['detail'] == [2], 'helper value binder must be reusable'
                # Its domain must be the original helper type, with linear args.
                domain = function['children'][0]
                assert rhs['tag'] == 'Apply' and rhs['children'][0]['tag'] == 'Lambda'
                expected = bare(rhs['children'][0]['children'][0])
                assert expected[0:2] == ['Pi', [1]]
                assert expected[2][1][0:2] == ['Pi', [1]]
                assert bare(domain) == expected
                count += 1
                return visit(expand_closed(function['children'][1], rhs))
        result = dict(node)
        result['children'] = [visit(c) for c in node['children']]
        return result
    result = visit(tree)
    assert count == 1, 'expected exactly the one introduced shared helper binder'
    return result, count


def instrument_module_check(source):
    """Counter-only clone: report existing budget debit, without changing decisions."""
    seams = {
      'module Fibril.Driver.ModuleCheck': 'module CountedModuleCheck',
      '  checkedExports : List (List String, List (String, String))':
      '  checkedExports : List (List String, List (String, String))\n  constructionDebit : Nat\n  declarationDebit : Nat\n  mainReservation : Nat',
      'Project graph term checked.inferredType sites (exportIndex interfaces)':
      'Project graph term checked.inferredType sites (exportIndex interfaces) 0 0 0',
      'Project graph term checked.inferredType (sites ++ compiled.sites) (exportIndex interfaces)':
      'Project graph term checked.inferredType (sites ++ compiled.sites) (exportIndex interfaces) ((minus 200000 compiled.remaining) + main.size) (minus 200000 compiled.remaining) main.size',
      '"Expanded core construction budget exhausted (200000)")\n     else Right ()':
      '("Expanded core construction budget exhausted (200000); remaining=" ++ show remaining ++ "; declaration_estimate=" ++ show estimate))\n     else Right ()',
    }
    # Anonymous accounting is not used: all experiment entries are named modules.
    for old, new in seams.items():
        assert source.count(old) == 1, old
        source = source.replace(old, new)
    return source
