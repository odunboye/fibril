// Trusted-IR runtime tests; source admission is tested separately by test_javascript.py.
import assert from 'node:assert/strict';
import {runProgram} from '../runtime/javascript/fibril_runtime.mjs';
const str=s=>['string',s], write=t=>['write',t], variable=n=>['var',n];
const program=entry=>({entry,globals:{}});
function output(p,limits={}) {
  const chunks=[]; let flushed=0;
  const result=runProgram(p,{write:b=>chunks.push(Buffer.from(b)),flush:()=>{flushed++;}},limits);
  assert.equal(flushed,1);
  assert.equal(result.actions,chunks.length);
  return Buffer.concat(chunks).toString('utf8');
}
function fails(p,pattern,limits={}) {
  const calls=[];
  assert.throws(()=>runProgram(p,{write:()=>calls.push('write'),flush:()=>calls.push('flush')},limits),pattern);
  assert.deepEqual(calls,[]);
}
assert.equal(output(program(write(['apply',['lambda',false,str('lazy')],['unsupported']]))),'lazy\n');
assert.equal(output(program(write(['apply',['lambda',true,str('erased')],['unsupported']]))),'erased\n');
assert.equal(output(program(write(['if',['bool',true],str('yes'),['unsupported']]))),'yes\n');
let reads=0;
const memo=program(write(['apply',['lambda',false,['append',variable(0),variable(0)]],['global',0]]));
Object.defineProperty(memo.globals,'0',{get(){reads++;return str('memo');}});
assert.equal(output(memo),'memomemo\n'); assert.equal(reads,1);
fails(program(write(['fix',variable(0)])),/cyclic/);
const word=n=>['word',n], show=t=>['wordToString',t];
assert.equal(output(program(write(show(word('18446744073709551615'))))),'18446744073709551615\n');
assert.equal(output(program(write(show(['wordAdd',word('18446744073709551615'),word('1')])))),'0\n');
assert.equal(output(program(write(show(['wordMul',word('9223372036854775808'),word('2')])))),'0\n');
assert.equal(output(program(write(show(['wordSub',word('0'),word('1')])))),'18446744073709551615\n');
const unwrap=t=>['variantCase',t,[str('zero'),['lambda',false,show(variable(0))]]];
assert.equal(output(program(write(unwrap(['wordDiv',word('18446744073709551615'),word('3')])))),'6148914691236517205\n');
assert.equal(output(program(write(unwrap(['wordDiv',word('1'),word('0')])))),'zero\n');
assert.equal(output(program(write(unwrap(['wordRem',word('1'),word('0')])))),'zero\n');
const decode=bytes=>['variantCase',['utf8Decode',['bytes',bytes]],[str('invalid'),['lambda',false,variable(0)]]];
for(const bytes of [[0xc0,0x80],[0xed,0xa0,0x80],[0xf4,0x90,0x80,0x80],[0xe2,0x82],[0x80]])
  assert.equal(output(program(write(decode(bytes)))),'invalid\n');
assert.equal(output(program(write(decode([0xef,0xbb,0xbf,0x61])))),'\ufeffa\n');
assert.equal(output(program(write(decode([0xf0,0x9f,0x8c,0x8d])))),'🌍\n');
const invalidUTF16=['variantCase',['utf8Encode',str('\ud800')],[str('invalid'),['lambda',false,str('unexpected')]]];
assert.equal(output(program(write(invalidUTF16))),'invalid\n');
const laterFailure=program(['bind',write(str('must not escape')),['lambda',false,write(str('bad\0output'))]]);
fails(laterFailure,/console output/);
for(const limits of [{steps:0},{depth:0},{bytes:0},{actions:0}])fails(program(write(str('x'))),/budget/,limits);
fails(program(write(str('x'))),/invalid.*limit/,{steps:100001});
let calls=[];
assert.throws(()=>runProgram(program(write(str('x'))),{write(){calls.push('write');return false;},flush(){calls.push('flush');}}),/host callback/);
assert.deepEqual(calls,['write']);
assert.throws(()=>runProgram(program(['pure',['unit']]),{write(){},flush(){return false;}}),/host callback/);
assert.throws(()=>runProgram(program(write(str('x'))),{write(){return Promise.resolve();},flush(){}}),/asynchronous/);
assert.throws(()=>runProgram(program(write(str('x'))),{write(){return Promise.reject(new Error('host rejection'));},flush(){}}),/asynchronous/);
assert.throws(()=>runProgram(program(['pure',['unit']]),{}),/callbacks/);
const reentrant=[];
runProgram(program(write(str('outer'))),{write(){reentrant.push(output(program(write(str('inner')))));},flush(){}});
assert.deepEqual(reentrant,['inner\n']);
assert.equal(output(program(write(str('repeat')))),output(program(write(str('repeat')))));
let many=['zero'];for(let i=0;i<1000;i++)many=['succ',many];
assert.equal(output(program(write(show(['wordFromNat',many])))),'1000\n');
// Strictly demand the recursive fold result: the runtime must stop before host stack overflow.
const deepFold=['natFold',str(''),['lambda',true,['lambda',false,['append',str('x'),variable(0)]]],many];
fails(program(write(deepFold)),/depth budget/);
console.log('JavaScript trusted-IR runtime checks passed');
