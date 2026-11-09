// Runtime for checked Fibril output-only programs. Host callbacks are synchronous.
// Limits account for interpreter work and logical allocations, not physical JS heap.
const defaults = Object.freeze({steps:100000, depth:256, bytes:16777216, actions:64});
export function runProgram(program, host, options = {}) {
  if (!host || typeof host.write !== 'function' || typeof host.flush !== 'function')
    throw new Error('JavaScript host requires write and flush callbacks');
  const write = host.write.bind(host), flush = host.flush.bind(host);
  const limits = {...defaults};
  for (const [key, value] of Object.entries(options)) {
    if (!(key in defaults) || !Number.isSafeInteger(value) || value < 0 || value > defaults[key])
      throw new Error('invalid JavaScript runtime limit');
    limits[key] = value;
  }
  let steps = 0, depth = 0, bytes = 0;
  const encoder = new TextEncoder();
  const decoder = new TextDecoder('utf-8', {fatal:true, ignoreBOM:true});
  function tick(n=1) {
    if (n > limits.steps - steps) throw new Error('JavaScript evaluation budget exhausted');
    steps += n;
  }
  function alloc(n=64) {
    if (n > limits.bytes - bytes) throw new Error('JavaScript allocation budget exhausted');
    bytes += n;
  }
  function enter(f) {
    tick();
    if (depth >= limits.depth) throw new Error('JavaScript depth budget exhausted');
    depth++;
    try { return f(); } finally { depth--; }
  }
  function value(tag, fields={}) { alloc(); return {tag,...fields}; }
  function thunk(compute) { alloc(); return {state:0, compute}; }
  function ready(v) { const t = thunk(null); t.state=2; t.value=v; return t; }
  function force(t) {
    if (!t) throw new Error('erased JavaScript value was forced');
    if (t.state===2) return t.value;
    if (t.state===1) throw new Error('cyclic JavaScript thunk');
    t.state=1;
    const v=enter(t.compute);
    t.value=v; t.state=2; t.compute=null;
    return v;
  }
  function cell(term, env) {
    if (term[0]==='var') {
      if (term[1] >= env.length) throw new Error('invalid JavaScript variable');
      return env[term[1]];
    }
    return thunk(()=>evaluate(term,env));
  }
  function apply(fun, arg) {
    if (fun.tag!=='lambda') throw new Error('JavaScript application expects a function');
    alloc(16 + fun.env.length*8);
    return evaluate(fun.body,[fun.erased ? null : arg,...fun.env]);
  }
  function expect(v, tag) {
    if (v.tag!==tag) throw new Error('JavaScript operand expects '+tag);
    return v;
  }
  function variant(tag, payload=null) { return value('variant',{index:tag,payload}); }
  function nat(n) {
    let result=value('zero');
    for (let i=0;i<n;i++) { tick(); result=value('succ',{tail:ready(result)}); }
    return result;
  }
  function count(v) {
    let n=0;
    while (v.tag==='succ') { tick(); n++; v=force(v.tail); }
    expect(v,'zero'); return n;
  }
  function word(n) { return value('word',{word:BigInt.asUintN(64,n)}); }
  function string(s) { alloc(s.length*2); return value('string',{text:s}); }
  function octets(data, charge=true) { if (charge) alloc(data.length); return value('bytes',{data}); }
  function scalar(s) {
    for (const c of s) { const n=c.codePointAt(0); if(n>=0xd800 && n<=0xdfff) return false; }
    return true;
  }
  function fold(kind, base, step, input, env) {
    return enter(()=>{
      const v=force(input), terminal=kind==='seq'?'nil':kind==='rec'?'end':'zero';
      if (v.tag===terminal) return evaluate(base,env);
      expect(v,kind==='seq'?'cons':kind==='rec'?'more':'succ');
      let branch=evaluate(step,env);
      const next=thunk(()=>fold(kind,base,step,v.tail,env));
      if(kind==='seq') branch=apply(branch,v.head);
      branch=apply(branch,kind==='natRuntime'?v.tail:null);
      return apply(branch,next);
    });
  }
  function evaluate(term, env=[]) {
    return enter(()=>{
      const [op,...args]=term;
      const ev=i=>evaluate(args[i],env), lazy=i=>cell(args[i],env);
      switch(op) {
        case 'erased': return value('erased');
        case 'unit': return value('unit');
        case 'bool': return value('bool',{boolean:args[0]});
        case 'string': return string(args[0]);
        case 'bytes': alloc(args[0].length); return octets(Uint8Array.from(args[0]),false);
        case 'word': return word(BigInt(args[0]));
        case 'var': if(args[0]>=env.length) throw new Error('invalid JavaScript variable'); return force(env[args[0]]);
        case 'global': {
          const body=program.globals[args[0]];
          if(!body) throw new Error('unknown JavaScript global');
          return evaluate(body,[]);
        }
        case 'lambda': return value('lambda',{erased:args[0],body:args[1],env});
        case 'fix': {
          const self=thunk(null); self.state=1; alloc(16+env.length*8);
          const result=evaluate(args[0],[self,...env]); self.value=result; self.state=2; return result;
        }
        case 'apply': {
          const fun=ev(0); expect(fun,'lambda');
          return apply(fun,fun.erased?null:lazy(1));
        }
        case 'zero': return value('zero');
        case 'end': return value('end');
        case 'nil': return value('nil');
        case 'succ': case 'more': return value(op,{tail:lazy(0)});
        case 'cons': return value('cons',{head:lazy(0),tail:lazy(1)});
        case 'natFold': case 'natRuntimeFold': case 'recFold': case 'seqFold':
          return fold(op==='seqFold'?'seq':op==='recFold'?'rec':op==='natRuntimeFold'?'natRuntime':'nat',args[0],args[1],lazy(2),env);
        case 'natCase': case 'recCase': case 'seqCase': {
          const v=ev(0), seq=op==='seqCase', rec=op==='recCase';
          if(v.tag===(seq?'nil':rec?'end':'zero')) return ev(1);
          expect(v,seq?'cons':rec?'more':'succ');
          let branch=ev(2); if(seq) branch=apply(branch,v.head);
          return apply(branch,v.tail);
        }
        case 'if': return expect(ev(0),'bool').boolean ? ev(1) : ev(2);
        case 'unitCase': expect(ev(0),'unit'); return ev(1);
        case 'nominal': return value('nominal',{payload:lazy(0)});
        case 'nominalCase': { const v=expect(ev(0),'nominal'); return apply(ev(1),v.payload); }
        case 'variant': return variant(args[0],args[1]===null?null:cell(args[1],env));
        case 'variantCase': {
          const v=expect(ev(0),'variant'), branches=args[1];
          if(v.index>=branches.length) throw new Error('out of range JavaScript variant');
          const branch=evaluate(branches[v.index],env);
          return v.payload ? apply(branch,v.payload) : branch;
        }
        case 'pair': return value('pair',{first:args[0]?null:cell(args[2],env),second:args[1]?null:cell(args[3],env)});
        case 'pairCase': {const p=expect(ev(0),'pair'); return apply(apply(ev(1),p.first),p.second);}
        case 'append': {const a=expect(ev(0),'string'), b=expect(ev(1),'string'); alloc((a.text.length+b.text.length)*2); return value('string',{text:a.text+b.text});}
        case 'stringEq': {const a=expect(ev(0),'string'), b=expect(ev(1),'string'); tick(a.text.length+b.text.length); return value('bool',{boolean:a.text===b.text});}
        case 'bytesAppend': {const a=expect(ev(0),'bytes').data,b=expect(ev(1),'bytes').data; tick(a.length+b.length); alloc(a.length+b.length); const data=new Uint8Array(a.length+b.length);data.set(a);data.set(b,a.length);return octets(data,false);}
        case 'bytesEqual': {const a=expect(ev(0),'bytes').data,b=expect(ev(1),'bytes').data; tick(a.length+b.length); return value('bool',{boolean:a.length===b.length&&a.every((x,i)=>x===b[i])});}
        case 'bytesShare': return value('nominal',{payload:lazy(0)});
        case 'bytesLength': return nat(expect(ev(0),'bytes').data.length);
        case 'bytesOctet': return octets(Uint8Array.of(count(ev(0))%256));
        case 'bytesLengthIs': {const n=count(ev(0)), b=expect(ev(1),'bytes').data; return value('bool',{boolean:n===b.length});}
        case 'bytesIndex': {const n=count(ev(0)),b=expect(ev(1),'bytes').data;return n<b.length?variant(1,ready(nat(b[n]))):variant(0);}
        case 'bytesSlice': {const n=count(ev(0)),len=count(ev(1)),b=expect(ev(2),'bytes').data;return octets(b.subarray(Math.min(n,b.length),Math.min(n+len,b.length)),false);}
        case 'utf8Encode': {const s=expect(ev(0),'string').text;tick(s.length);if(!scalar(s))return variant(0);alloc(s.length*3);return variant(1,ready(octets(encoder.encode(s),false)));}
        case 'utf8Decode': {const b=expect(ev(0),'bytes').data;tick(b.length);let s;try{s=decoder.decode(b);}catch(e){if(e instanceof TypeError)return variant(0);throw e;}return variant(1,ready(string(s)));}
        case 'wordFromNat': {let v=ev(0),n=0n;while(v.tag==='succ'){tick();n=BigInt.asUintN(64,n+1n);v=force(v.tail);}expect(v,'zero');return word(n);}
        case 'wordToString': return string(expect(ev(0),'word').word.toString());
        case 'wordAdd': case 'wordSub': case 'wordMul': case 'wordEq': case 'wordLt': case 'wordDiv': case 'wordRem': {
          const a=expect(ev(0),'word').word,b=expect(ev(1),'word').word;
          if(op==='wordEq'||op==='wordLt')return value('bool',{boolean:op==='wordEq'?a===b:a<b});
          if(op==='wordDiv'||op==='wordRem')return b===0n?variant(0):variant(1,ready(word(op==='wordDiv'?a/b:a%b)));
          return word(op==='wordAdd'?a+b:op==='wordSub'?a-b:a*b);
        }
        case 'pure': return value('pure',{result:lazy(0)});
        case 'write': return value('write',{text:lazy(0)});
        case 'bind': return value('bind',{first:lazy(0),next:lazy(1)});
        default: throw new Error('unsupported JavaScript instruction: '+op);
      }
    });
  }
  const actions=[], continuations=[];
  let io=evaluate(program.entry);
  for (;;) {
    tick(); let result;
    if(io.tag==='bind') {alloc();continuations.push(io.next);io=force(io.first);continue;}
    if(io.tag==='pure') result=io.result;
    else if(io.tag==='write') {
      const text=expect(force(io.text),'string').text;
      if(actions.length>=limits.actions)throw new Error('JavaScript output action budget exhausted');
      if(text.includes('\0')||!scalar(text))throw new Error('invalid JavaScript console output');
      tick(text.length);alloc(text.length*3+1);
      actions.push(encoder.encode(text+'\n'));result=ready(value('unit'));
    } else throw new Error('JavaScript program returned a non-IO value');
    if(!continuations.length) {expect(force(result),'unit');break;}
    io=apply(force(continuations.pop()),result);
  }
  function callback(fn,...args) {
    const result=fn(...args);
    if(result && typeof result.then==='function') { Promise.resolve(result).catch(()=>{}); throw new Error('JavaScript host callback is asynchronous'); }
    if(result===false)throw new Error('JavaScript host callback failed');
  }
  for(const action of actions) callback(write,action);
  callback(flush);
  return Object.freeze({actions:actions.length,steps,allocatedBytes:bytes});
}
