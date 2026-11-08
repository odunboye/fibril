"""OFFLINE counter insertions in private native copies, never production runtime.

Exclusive counters: successful enter calls by immediate evaluator/ledger site,
plus the existing UTF-8 length charge; successful arena allocations by direct C caller. Value tags are a second marginal,
not additive with allocation sites. No extra forcing, decisions or fuel charges.
"""
import re
from pathlib import Path


def replace_once(text, old, new):
    assert text.count(old) == 1, old
    return text.replace(old, new)


def instrument(directory):
    directory = Path(directory)
    program = directory / 'program.c'
    text = program.read_text()
    definitions = re.findall(r'static FValue \*(fibril_expr_\d+)\(FRuntime \*r, FEnv \*e\) \{ (.*?) \}', text)
    assert definitions
    operations = {}
    for name, body in definitions:
        operation = re.search(r'return (f_\w+)\(', body)
        assert operation, body
        operations[name] = operation[1]
    # Shared globals enter public wrappers that directly call an expression.
    # Attribute that evaluator entry to the wrapped expression's operation;
    # the direct C call does not itself spend another evaluator entry.
    wrappers = re.findall(r'FValue \*(fibril_global_\d+)\(FRuntime \*r, FEnv \*e\) \{ \(void\)e; return (fibril_expr_\d+)\(r, NULL\); \}', text)
    for wrapper, expression in wrappers:
        assert expression in operations, expression
        operations[wrapper] = operations[expression]
    labels = sorted(set(operations.values()))
    text += '\n/* OFFLINE counter-only evaluator attribution. */\n'
    text += 'int audit_operation(FEval code) {\n'
    for name, operation in operations.items():
        text += f'  if (code == {name}) return {labels.index(operation)};\n'
    text += f'  return {len(labels)};\n}}\n'
    program.write_text(text)

    path = directory / 'fibril_runtime.c'
    text = path.read_text()
    # Discover direct allocate callers from the unchanged, simple C definitions.
    sites = set()
    current = None
    for line in text.splitlines():
        match = re.match(r'(?:static )?[\w *]+\b(\w+)\([^;]*\) \{', line)
        if match:
            current = match[1]
        if 'allocate(r,' in line:
            assert current
            sites.add(current)
    sites.add('interact_binary')
    sites = sorted(sites)
    step_labels = labels + ['unmapped_evaluation', 'byte_work', 'evaluate_fold', 'plan', 'interact', 'interact_binary', 'utf8_validation_charge']
    declarations = ('extern int audit_operation(FEval);\n'
                    f'static size_t audit_steps[{len(step_labels)}];\n'
                    f'static size_t audit_allocations[{len(sites)}], audit_bytes[{len(sites)}];\n'
                    'static size_t audit_values[64];\n'
                    f'static size_t audit_arguments[{len(labels) + 1}];\n')
    text = replace_once(text, 'static void *allocate(FRuntime *r, size_t size) {',
                        declarations + 'static void *audit_allocate(FRuntime *r, size_t size, const char *site) {')
    record = ''
    for i, site in enumerate(sites):
        record += f'  if (!strcmp(site, "{site}")) {{ audit_allocations[{i}]++; audit_bytes[{i}] += size; }}\n'
    text = replace_once(text, '  return (void *)(p + 1);\n}',
                        record + '  return (void *)(p + 1);\n}\n#define allocate(r, size) audit_allocate(r, size, __func__)')
    text = replace_once(text, '  FValue *result = code(r, env);',
                        '  audit_steps[audit_operation(code)]++;\n  FValue *result = code(r, env);')
    text = replace_once(text, 'FValue *f_apply(FRuntime *r, FEnv *env, FEval function, FEval argument) {',
                        'FValue *f_apply(FRuntime *r, FEnv *env, FEval function, FEval argument) {\n  audit_arguments[audit_operation(argument)]++;')
    for function in ('byte_work', 'evaluate_fold', 'plan', 'interact'):
        # Signature may span lines: only change the unique successful enter in its body.
        pattern = re.compile(r'(\b' + function + r'\([^;{}]*\) \{\n  if \(!enter\(r\)\) return (?:0|NULL);)')
        text, count = pattern.subn(r'\1\n  audit_steps[' + str(step_labels.index(function)) + ' ]++;', text)
        assert count == 1, function
    text = replace_once(text, '  r->steps += length;',
                        f'  r->steps += length; audit_steps[{step_labels.index("utf8_validation_charge")}] += length;')
    text = replace_once(text, '  if (v) { memset(v, 0, sizeof(*v)); v->tag = tag; }',
                        '  if (v) { audit_values[tag]++; memset(v, 0, sizeof(*v)); v->tag = tag; }')
    path.write_text(text)
    path = directory / 'fibril_binary_runtime.c'
    text = replace_once(path.read_text(), '    if (!enter(r)) return NULL;',
                        f'    if (!enter(r)) return NULL;\n    audit_steps[{step_labels.index("interact_binary")}]++;')
    path.write_text(text)
    tags = re.search(r'typedef enum \{ (V_UNIT,.*?) \} FTag;', (directory / 'fibril_runtime.c').read_text(), re.S)[1]
    tags = re.findall(r'V_\w+', tags)
    assert len(tags) <= 64
    # The existing observer prints before binary_finish destroys the arena.
    path = directory / 'observer.c'
    text = path.read_text()
    printing = '  fprintf(stderr, "ATTR {\\\"steps\\\":{");\n'
    for i, label in enumerate(step_labels):
        printing += f'  fprintf(stderr, "{"," if i else ""}\\\"{label}\\\":%zu", audit_steps[{i}]);\n'
    printing += '  fprintf(stderr, "},\\\"allocations\\\":{");\n'
    for i, label in enumerate(sites):
        printing += f'  fprintf(stderr, "{"," if i else ""}\\\"{label}\\\":[%zu,%zu]", audit_allocations[{i}], audit_bytes[{i}]);\n'
    printing += '  fprintf(stderr, "},\\\"values\\\":{");\n'
    for i, label in enumerate(tags):
        printing += f'  fprintf(stderr, "{"," if i else ""}\\\"{label}\\\":%zu", audit_values[{i}]);\n'
    printing += '  fprintf(stderr, "},\\\"application_arguments\\\":{");\n'
    for i, label in enumerate(labels + ['unmapped_argument']):
        printing += f'  fprintf(stderr, "{"," if i else ""}\\\"{label}\\\":%zu", audit_arguments[{i}]);\n'
    printing += '  fprintf(stderr, "}}\\n");\n'
    text = replace_once(text, '  return binary_finish(&runtime, &context, status);',
                        printing + '  return binary_finish(&runtime, &context, status);')
    path.write_text(text)
    return {'step_buckets': step_labels, 'allocation_sites': sites, 'value_tags': tags,
            'emitted_operations': {label: list(operations.values()).count(label) for label in labels}}
